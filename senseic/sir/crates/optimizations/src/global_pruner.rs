use sensei_core::span::IncIterable;
use sir_data::{
    BasicBlock, BasicBlockId, Branch, Cases, CasesId, Control, ControlView, DataId, DenseIndexSet,
    EthIRProgram, Function, FunctionId, Idx, LargeConstId, LocalId, LocalIdx, Operation,
    OperationIdx, Span, StaticAllocId, Switch,
    operation::{OpVisitor, OpVisitorMut},
};
use std::collections::HashMap;

pub struct GlobalPruner {
    func_worklist: Vec<FunctionId>,
    block_worklist: Vec<BasicBlockId>,
    local_map: HashMap<LocalId, LocalId>,
    static_alloc_map: HashMap<StaticAllocId, StaticAllocId>,
    large_const_map: HashMap<LargeConstId, Option<LargeConstId>>,
    data_map: HashMap<DataId, Option<DataId>>,
    function_map: HashMap<FunctionId, Option<FunctionId>>,
    block_map: HashMap<BasicBlockId, Option<BasicBlockId>>,
    cases_map: HashMap<CasesId, Option<CasesId>>,
}

impl Default for GlobalPruner {
    fn default() -> Self {
        Self::new()
    }
}

impl GlobalPruner {
    pub fn new() -> Self {
        Self {
            func_worklist: Vec::new(),
            block_worklist: Vec::new(),
            local_map: HashMap::new(),
            static_alloc_map: HashMap::new(),
            large_const_map: HashMap::new(),
            data_map: HashMap::new(),
            function_map: HashMap::new(),
            block_map: HashMap::new(),
            cases_map: HashMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.func_worklist.clear();
        self.block_worklist.clear();
        self.local_map.clear();
        self.static_alloc_map.clear();
        self.large_const_map.clear();
        self.data_map.clear();
        self.function_map.clear();
        self.block_map.clear();
        self.cases_map.clear();
    }

    pub fn run(
        &mut self,
        src: &EthIRProgram,
        dst: &mut EthIRProgram,
        live_blocks: Option<&DenseIndexSet<BasicBlockId>>,
    ) {
        self.clear();
        dst.clear();
        let mut pruner = PrunerContext { state: self, src, dst, live_blocks };
        pruner.analyze();
        pruner.apply();
    }
}

struct PrunerContext<'a> {
    state: &'a mut GlobalPruner,
    src: &'a EthIRProgram,
    dst: &'a mut EthIRProgram,
    live_blocks: Option<&'a DenseIndexSet<BasicBlockId>>,
}

impl<'a> PrunerContext<'a> {
    fn analyze(&mut self) {
        self.state.func_worklist.push(self.src.init_entry);
        if let Some(main) = self.src.main_entry {
            self.state.func_worklist.push(main);
        }

        while let Some(function) = self.state.func_worklist.pop() {
            self.track_function(function);
        }
    }

    fn apply(&mut self) {
        self.copy_data_segments();
        self.copy_large_consts();
        self.reserve_block_ids();
        self.copy_cases();
        self.copy_functions();
        self.fill_blocks();

        self.dst.init_entry =
            self.state.function_map[&self.src.init_entry].expect("init_entry should be copied");
        self.dst.main_entry = self
            .src
            .main_entry
            .map(|m| self.state.function_map[&m].expect("main_entry should be copied"));
    }

    fn copy_data_segments(&mut self) {
        for (old_id, bytes) in self.src.data_segments.enumerate_idx() {
            if let Some(None) = self.state.data_map.get(&old_id) {
                let new_id = self.dst.data_segments.push_copy_slice(bytes);
                self.state.data_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn copy_large_consts(&mut self) {
        for (old_id, &value) in self.src.large_consts.enumerate_idx() {
            if let Some(None) = self.state.large_const_map.get(&old_id) {
                let new_id = self.dst.large_consts.push(value);
                self.state.large_const_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn reserve_block_ids(&mut self) {
        for (old_id, _) in self.src.basic_blocks.enumerate_idx() {
            if let Some(None) = self.state.block_map.get(&old_id) {
                let placeholder = BasicBlock {
                    inputs: Span::new(LocalIdx::ZERO, LocalIdx::ZERO),
                    outputs: Span::new(LocalIdx::ZERO, LocalIdx::ZERO),
                    operations: Span::new(OperationIdx::ZERO, OperationIdx::ZERO),
                    control: Control::LastOpTerminates,
                };
                let new_id = self.dst.basic_blocks.push(placeholder);
                self.state.block_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn copy_cases(&mut self) {
        for (old_id, old_cases) in self.src.cases.enumerate_idx() {
            if let Some(None) = self.state.cases_map.get(&old_id) {
                let new_values_start = self.state.large_const_map[&old_cases.values_start_id]
                    .expect("large const should be copied");
                debug_assert!((0..old_cases.cases_count).all(|i| {
                    self.state.large_const_map[&(old_cases.values_start_id + i)]
                        == Some(new_values_start + i)
                }));

                let new_targets_start = self.dst.cases_bb_ids.next_idx();
                for old_bb_id in old_cases.get_bb_ids(self.src).as_raw_slice() {
                    let new_bb_id =
                        self.state.block_map[old_bb_id].expect("block should be copied");
                    self.dst.cases_bb_ids.push(new_bb_id);
                }

                let new_cases = Cases {
                    values_start_id: new_values_start,
                    targets_start_id: new_targets_start,
                    cases_count: old_cases.cases_count,
                };
                let new_id = self.dst.cases.push(new_cases);
                self.state.cases_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn copy_functions(&mut self) {
        for (old_id, old_func) in self.src.functions.enumerate_idx() {
            if let Some(None) = self.state.function_map.get(&old_id) {
                let new_entry =
                    self.state.block_map[&old_func.entry()].expect("entry block should be copied");
                let new_func = Function::new(new_entry, old_func.get_outputs());
                let new_id = self.dst.functions.push(new_func);
                self.state.function_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn fill_blocks(&mut self) {
        for (old_id, old_block) in self.src.basic_blocks.enumerate_idx() {
            if let Some(Some(new_id)) = self.state.block_map.get(&old_id).copied() {
                let inputs_start = self.dst.locals.next_idx();
                for old_local in self.src.block(old_id).inputs() {
                    let new_local = self.state.local_map[old_local];
                    self.dst.locals.push(new_local);
                }
                let inputs_end = self.dst.locals.next_idx();

                let outputs_start = self.dst.locals.next_idx();
                for old_local in self.src.block(old_id).outputs() {
                    let new_local = self.state.local_map[old_local];
                    self.dst.locals.push(new_local);
                }
                let outputs_end = self.dst.locals.next_idx();

                let ops_start = self.dst.operations.next_idx();
                for op in self.src.block(old_id).operations() {
                    if matches!(op.op(), Operation::Noop(())) {
                        continue;
                    }
                    let remapped_op = self.remap_operation(op.op());
                    self.dst.operations.push(remapped_op);
                }
                let ops_end = self.dst.operations.next_idx();

                let new_control = self.remap_control(&old_block.control);

                self.dst.basic_blocks[new_id] = BasicBlock {
                    inputs: Span::new(inputs_start, inputs_end),
                    outputs: Span::new(outputs_start, outputs_end),
                    operations: Span::new(ops_start, ops_end),
                    control: new_control,
                };
            }
        }
    }

    fn remap_control(&self, control: &Control) -> Control {
        match control {
            Control::LastOpTerminates => Control::LastOpTerminates,
            Control::InternalReturn => Control::InternalReturn,
            Control::ContinuesTo(bb) => {
                Control::ContinuesTo(self.state.block_map[bb].expect("block should be copied"))
            }
            Control::Branches(branch) => Control::Branches(Branch {
                condition: self.state.local_map[&branch.condition],
                non_zero_target: self.state.block_map[&branch.non_zero_target]
                    .expect("block should be copied"),
                zero_target: self.state.block_map[&branch.zero_target]
                    .expect("block should be copied"),
            }),
            Control::Switch(switch) => Control::Switch(Switch {
                condition: self.state.local_map[&switch.condition],
                fallback: switch
                    .fallback
                    .map(|fb| self.state.block_map[&fb].expect("block should be copied")),
                cases: self.state.cases_map[&switch.cases].expect("cases should be copied"),
            }),
        }
    }

    fn remap_operation(&mut self, mut op: Operation) -> Operation {
        op.visit_data_mut(self);
        op
    }

    fn track_function(&mut self, function: FunctionId) {
        if self.state.function_map.contains_key(&function) {
            return;
        }
        self.state.function_map.insert(function, None);
        self.state.block_worklist.push(self.src.function(function).entry().id());
        while let Some(bb) = self.state.block_worklist.pop() {
            self.track_block(bb);
        }
    }

    fn track_block(&mut self, bb: BasicBlockId) {
        if self.state.block_map.contains_key(&bb) {
            return;
        }
        if self.live_blocks.is_some_and(|reachable| !reachable.contains(bb)) {
            return;
        }

        self.state.block_map.insert(bb, None);
        let block = self.src.block(bb);

        for op in block.operations() {
            if matches!(op.op(), Operation::Noop(())) {
                continue;
            }
            op.op().visit_data(self);
        }

        for input in block.inputs() {
            self.track_local(*input);
        }
        for output in block.outputs() {
            self.track_local(*output);
        }

        match block.control() {
            ControlView::LastOpTerminates | ControlView::InternalReturn => {}
            ControlView::ContinuesTo(to) => self.state.block_worklist.push(to),
            ControlView::Branches { condition, non_zero_target, zero_target } => {
                self.track_local(condition);
                self.state.block_worklist.push(non_zero_target);
                self.state.block_worklist.push(zero_target);
            }
            ControlView::Switch(switch_view) => {
                self.track_local(switch_view.condition());
                self.track_cases(switch_view.cases_id());

                if let Some(fb) = switch_view.fallback() {
                    self.state.block_worklist.push(fb);
                }

                for (_, target) in switch_view.cases() {
                    self.state.block_worklist.push(target);
                }

                for const_id in switch_view.value_ids() {
                    self.track_large_const(const_id);
                }
            }
        }
    }

    fn track_local(&mut self, local: LocalId) {
        if !self.state.local_map.contains_key(&local) {
            let new_id = self.dst.next_free_local_id.get_and_inc();
            self.state.local_map.insert(local, new_id);
        }
    }

    fn track_static_alloc(&mut self, alloc_id: StaticAllocId) {
        if !self.state.static_alloc_map.contains_key(&alloc_id) {
            let new_id = self.dst.next_static_alloc_id.get_and_inc();
            self.state.static_alloc_map.insert(alloc_id, new_id);
        }
    }

    fn track_large_const(&mut self, const_id: LargeConstId) {
        self.state.large_const_map.entry(const_id).or_insert(None);
    }

    fn track_data(&mut self, data_id: DataId) {
        self.state.data_map.entry(data_id).or_insert(None);
    }

    fn track_cases(&mut self, cases_id: CasesId) {
        self.state.cases_map.entry(cases_id).or_insert(None);
    }
}

impl<'a> OpVisitor<'_, ()> for PrunerContext<'a> {
    fn visit_inline_operands<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'_ sir_data::operation::InlineOperands<INS, OUTS>,
    ) {
        for local in data.ins.iter().chain(data.outs.iter()) {
            self.track_local(*local);
        }
    }

    fn visit_allocated_ins<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'_ sir_data::operation::AllocatedIns<INS, OUTS>,
    ) {
        for local in data.get_inputs(self.src).iter().chain(data.outs.iter()) {
            self.track_local(*local);
        }
    }

    fn visit_static_alloc(&mut self, data: &'_ sir_data::operation::StaticAllocData) {
        self.track_local(data.ptr_out);
        self.track_static_alloc(data.alloc_id);
    }

    fn visit_memory_load(&mut self, data: &'_ sir_data::operation::MemoryLoadData) {
        self.track_local(data.out);
        self.track_local(data.ptr);
    }

    fn visit_memory_store(&mut self, data: &'_ sir_data::operation::MemoryStoreData) {
        for local in data.ins {
            self.track_local(local);
        }
    }

    fn visit_set_small_const(&mut self, data: &'_ sir_data::operation::SetSmallConstData) {
        self.track_local(data.sets);
    }

    fn visit_set_large_const(&mut self, data: &'_ sir_data::operation::SetLargeConstData) {
        self.track_local(data.sets);
        self.track_large_const(data.value);
    }

    fn visit_set_data_offset(&mut self, data: &'_ sir_data::operation::SetDataOffsetData) {
        self.track_local(data.sets);
        self.track_data(data.segment_id);
    }

    fn visit_icall(&mut self, data: &'_ sir_data::operation::InternalCallData) {
        self.state.func_worklist.push(data.function);

        for &local in data.get_inputs(self.src).iter().chain(data.get_outputs(self.src).iter()) {
            self.track_local(local);
        }
    }

    fn visit_void(&mut self) {}
}

impl<'a> OpVisitorMut<'_, ()> for PrunerContext<'a> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut sir_data::operation::InlineOperands<INS, OUTS>,
    ) {
        for local in data.ins.iter_mut().chain(data.outs.iter_mut()) {
            *local = self.state.local_map[local];
        }
    }

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut sir_data::operation::AllocatedIns<INS, OUTS>,
    ) {
        let new_ins_start = self.dst.locals.next_idx();
        for old_local in data.get_inputs(self.src) {
            self.dst.locals.push(self.state.local_map[old_local]);
        }
        data.ins_start = new_ins_start;

        for local in &mut data.outs {
            *local = self.state.local_map[local];
        }
    }

    fn visit_static_alloc_mut(&mut self, data: &mut sir_data::operation::StaticAllocData) {
        data.ptr_out = self.state.local_map[&data.ptr_out];
        data.alloc_id = self.state.static_alloc_map[&data.alloc_id];
    }

    fn visit_memory_load_mut(&mut self, data: &mut sir_data::operation::MemoryLoadData) {
        data.out = self.state.local_map[&data.out];
        data.ptr = self.state.local_map[&data.ptr];
    }

    fn visit_memory_store_mut(&mut self, data: &mut sir_data::operation::MemoryStoreData) {
        for local in &mut data.ins {
            *local = self.state.local_map[local];
        }
    }

    fn visit_set_small_const_mut(&mut self, data: &mut sir_data::operation::SetSmallConstData) {
        data.sets = self.state.local_map[&data.sets];
    }

    fn visit_set_large_const_mut(&mut self, data: &mut sir_data::operation::SetLargeConstData) {
        data.sets = self.state.local_map[&data.sets];
        data.value = self.state.large_const_map[&data.value].expect("large const should be copied");
    }

    fn visit_set_data_offset_mut(&mut self, data: &mut sir_data::operation::SetDataOffsetData) {
        data.sets = self.state.local_map[&data.sets];
        data.segment_id =
            self.state.data_map[&data.segment_id].expect("data segment should be copied");
    }

    fn visit_icall_mut(&mut self, data: &mut sir_data::operation::InternalCallData) {
        let new_ins_start = self.dst.locals.next_idx();
        for &old_local in data.get_inputs(self.src) {
            self.dst.locals.push(self.state.local_map[&old_local]);
        }

        let new_outs_start = self.dst.locals.next_idx();
        for &old_local in data.get_outputs(self.src) {
            self.dst.locals.push(self.state.local_map[&old_local]);
        }

        data.function = self.state.function_map[&data.function].expect("function should be copied");
        data.ins_start = new_ins_start;
        data.outs_start = new_outs_start;
    }

    fn visit_void_mut(&mut self) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{constant_propagation::SCCPAnalysis, unused_operation_elimination};
    use sir_parser::{EmitConfig, parse_or_panic};
    use sir_test_utils::assert_trim_strings_eq_with_diff;

    #[derive(Debug, PartialEq, Eq)]
    struct IrShape {
        functions: usize,
        basic_blocks: usize,
        operations: usize,
        locals: usize,
        large_consts: usize,
        data_segments: usize,
        data_bytes: usize,
        cases: usize,
        cases_bb_ids: usize,
        next_local: usize,
        next_static_alloc: usize,
    }

    impl IrShape {
        fn of(ir: &EthIRProgram) -> Self {
            Self {
                functions: ir.functions.len(),
                basic_blocks: ir.basic_blocks.len(),
                operations: ir.operations.len(),
                locals: ir.locals.len(),
                large_consts: ir.large_consts.len(),
                data_segments: ir.data_segments.len(),
                data_bytes: ir.data_segments.iter().map(|s| s.len()).sum(),
                cases: ir.cases.len(),
                cases_bb_ids: ir.cases_bb_ids.len(),
                next_local: ir.next_free_local_id.idx(),
                next_static_alloc: ir.next_static_alloc_id.idx(),
            }
        }
    }

    #[test]
    fn test_sccp_unused_elim_and_prune() {
        let input = r#"
            fn init:
                entry {
                    cond = const 1
                    => cond ? @live : @dead
                }
                live {
                    a = const 1
                    b = const 2
                    result = icall @helper a b
                    unused_local = add a b
                    key = const 0
                    sstore key result
                    stop
                }
                dead {
                    offset = data_offset .dead_data
                    x = const 99
                    y = const 100
                    p q = icall @dead_helper x y
                    stop
                }

            fn helper:
                entry x y -> sum {
                    sum = add x y
                    iret
                }

            fn dead_helper:
                entry a b -> product quotient {
                    product = mul a b
                    quotient = div a b
                    iret
                }

            data dead_data 0xcafebabe
        "#;

        let mut ir = parse_or_panic(input, EmitConfig::init_only());

        let mut sccp = SCCPAnalysis::new(&ir);
        sccp.analysis(&ir);
        sccp.apply(&mut ir);

        unused_operation_elimination::run(&mut ir);

        let src_str = sir_data::display_program(&ir);
        let expected_src = r#"
Functions:
    fn @0 -> entry @0  (outputs: 1)
    fn @1 -> entry @1  (outputs: 2)
    fn @2 -> entry @2  (outputs: 0)

Basic Blocks:
    @0 $0 $1 -> $2 {
        $2 = add $0 $1
        iret
    }

    @1 $3 $4 -> $5 $6 {
        $5 = mul $3 $4
        $6 = div $3 $4
        iret
    }

    @2 {
        noop
        => @3
    }

    @3 {
        $8 = const 0x1
        $9 = const 0x2
        $10 = icall @0 $8 $9
        noop
        $12 = const 0x0
        sstore $12 $10
        stop
    }

    @4 {
        noop
        $14 = const 0x63
        $15 = const 0x64
        $16 $17 = icall @1 $14 $15
        stop
    }


data .0 0xcafebabe
        "#;
        assert_trim_strings_eq_with_diff(&src_str, expected_src, "src after sccp + unused elim");

        assert_eq!(
            IrShape::of(&ir),
            IrShape {
                functions: 3,
                basic_blocks: 5,
                operations: 16,
                locals: 14,
                large_consts: 0,
                data_segments: 1,
                data_bytes: 4,
                cases: 0,
                cases_bb_ids: 0,
                next_local: 18,
                next_static_alloc: 0,
            }
        );

        let mut dst = EthIRProgram::default();
        let mut pruner = GlobalPruner::new();
        pruner.run(&ir, &mut dst, Some(&sccp.reachable));

        let dst_str = sir_data::display_program(&dst);
        let expected_dst = r#"
Functions:
    fn @0 -> entry @0  (outputs: 1)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 $4 $5 -> $6 {
        $6 = add $4 $5
        iret
    }

    @1 {
        => @2
    }

    @2 {
        $0 = const 0x1
        $1 = const 0x2
        $2 = icall @0 $0 $1
        $3 = const 0x0
        sstore $3 $2
        stop
    }
        "#;
        assert_trim_strings_eq_with_diff(&dst_str, expected_dst, "dst after prune");

        assert_eq!(
            IrShape::of(&dst),
            IrShape {
                functions: 2,
                basic_blocks: 3,
                operations: 7,
                locals: 6,
                large_consts: 0,
                data_segments: 0,
                data_bytes: 0,
                cases: 0,
                cases_bb_ids: 0,
                next_local: 7,
                next_static_alloc: 0,
            }
        );
    }

    #[test]
    fn test_prune_dead_function_data() {
        let input = r#"
            fn init:
                entry {
                    val = large_const 0xaabbccddaabbccddaabbccddaabbccddaabbccddaabbccddaabbccddaabbccdd
                    offset = data_offset .live_data
                    live_ptr = salloc 64
                    sstore live_ptr val
                    selector = const 0
                    switch selector {
                        1 => @case_one
                        2 => @case_two
                        default => @fallback
                    }
                }
                case_one { stop }
                case_two { stop }
                fallback { stop }

            fn dead_fn:
                entry {
                    dead_val = large_const 0x1122334411223344112233441122334411223344112233441122334411223344
                    dead_offset = data_offset .dead_data
                    dead_ptr = salloc 128
                    s = const 0
                    switch s {
                        100 => @dead_a
                        200 => @dead_b
                        default => @dead_c
                    }
                }
                dead_a { stop }
                dead_b { stop }
                dead_c { stop }

            data live_data 0x1234
            data dead_data 0x5678
        "#;

        let ir = parse_or_panic(input, EmitConfig::init_only());

        let src_str = sir_data::display_program(&ir);
        let expected_src = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @4  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = large_const 0xaabbccddaabbccddaabbccddaabbccddaabbccddaabbccddaabbccddaabbccdd
        $1 = data_offset .0
        $2 = salloc 64 #0
        sstore $2 $0
        $3 = const 0x0
        switch $3 {
            1 => @1,
            2 => @2,
            else => @3
        }

    }

    @1 {
        stop
    }

    @2 {
        stop
    }

    @3 {
        stop
    }

    @4 {
        $4 = large_const 0x1122334411223344112233441122334411223344112233441122334411223344
        $5 = data_offset .1
        $6 = salloc 128 #1
        $7 = const 0x0
        switch $7 {
            64 => @5,
            c8 => @6,
            else => @7
        }

    }

    @5 {
        stop
    }

    @6 {
        stop
    }

    @7 {
        stop
    }


data .0 0x1234
data .1 0x5678
        "#;
        assert_trim_strings_eq_with_diff(&src_str, expected_src, "src before prune");

        assert_eq!(
            IrShape::of(&ir),
            IrShape {
                functions: 2,
                basic_blocks: 8,
                operations: 15,
                locals: 0,
                large_consts: 6,
                data_segments: 2,
                data_bytes: 4,
                cases: 2,
                cases_bb_ids: 4,
                next_local: 8,
                next_static_alloc: 2,
            }
        );

        let mut dst = EthIRProgram::default();
        let mut pruner = GlobalPruner::new();
        pruner.run(&ir, &mut dst, None);

        let dst_str = sir_data::display_program(&dst);
        let expected_dst = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = large_const 0xaabbccddaabbccddaabbccddaabbccddaabbccddaabbccddaabbccddaabbccdd
        $1 = data_offset .0
        $2 = salloc 64 #0
        sstore $2 $0
        $3 = const 0x0
        switch $3 {
            1 => @1,
            2 => @2,
            else => @3
        }

    }

    @1 {
        stop
    }

    @2 {
        stop
    }

    @3 {
        stop
    }


data .0 0x1234
        "#;
        assert_trim_strings_eq_with_diff(&dst_str, expected_dst, "dst after prune");

        assert_eq!(
            IrShape::of(&dst),
            IrShape {
                functions: 1,
                basic_blocks: 4,
                operations: 8,
                locals: 0,
                large_consts: 3,
                data_segments: 1,
                data_bytes: 2,
                cases: 1,
                cases_bb_ids: 2,
                next_local: 4,
                next_static_alloc: 1,
            }
        );
    }
}
