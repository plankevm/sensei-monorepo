use sensei_core::span::IncIterable;
use sir_data::{
    BasicBlock, BasicBlockId, BlockView, Branch, Cases, CasesId, Control, ControlView, DataId,
    DenseIndexSet, EthIRProgram, Function, FunctionId, Idx, LargeConstId, LocalId, LocalIdx,
    Operation, OperationIdx, Span, StaticAllocId, Switch,
    operation::{OpVisitor, OpVisitorMut},
};
use std::collections::HashMap;

pub struct Defragmenter {
    func_worklist: Vec<FunctionId>,
    block_worklist: Vec<BasicBlockId>,
    local_map: HashMap<LocalId, LocalId>,
    static_alloc_map: HashMap<StaticAllocId, StaticAllocId>,
    large_const_map: HashMap<LargeConstId, LargeConstId>,
    data_map: HashMap<DataId, DataId>,
    function_map: HashMap<FunctionId, FunctionId>,
    block_map: HashMap<BasicBlockId, BasicBlockId>,
    cases_map: HashMap<CasesId, CasesId>,
}

impl Default for Defragmenter {
    fn default() -> Self {
        Self::new()
    }
}

impl Defragmenter {
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
        Rewriter { state: self, src, dst, live_blocks }.rewrite();
    }
}

struct Rewriter<'a> {
    state: &'a mut Defragmenter,
    src: &'a EthIRProgram,
    dst: &'a mut EthIRProgram,
    live_blocks: Option<&'a DenseIndexSet<BasicBlockId>>,
}

impl<'a> Rewriter<'a> {
    fn rewrite(mut self) {
        self.state.func_worklist.push(self.src.init_entry);
        if let Some(main) = self.src.main_entry {
            self.state.func_worklist.push(main);
        }

        while let Some(function) = self.state.func_worklist.pop() {
            self.emit_function(function);
        }

        self.patch_block_control();

        self.dst.init_entry = self.state.function_map[&self.src.init_entry];
        self.dst.main_entry = self.src.main_entry.map(|m| self.state.function_map[&m]);
    }

    fn emit_function(&mut self, old_id: FunctionId) {
        let old_func = self.src.function(old_id);
        let old_entry_id = old_func.entry().id();

        // We check block_map instead of function_map because visit_icall eagerly
        // reserves function IDs before the function is emitted. Entry block being
        // emitted implies the function has been fully processed.
        if self.state.block_map.contains_key(&old_entry_id) {
            return;
        }

        self.reserve_function_id(old_id);

        self.push_block(old_entry_id);
        while let Some(bb) = self.state.block_worklist.pop() {
            self.emit_block(bb);
        }

        let new_id = self.state.function_map[&old_id];
        let new_entry = self.state.block_map[&old_entry_id];
        self.dst.functions[new_id] = Function::new(new_entry, old_func.num_outputs());
    }

    fn reserve_function_id(&mut self, old_id: FunctionId) -> bool {
        if self.state.function_map.contains_key(&old_id) {
            false
        } else {
            let placeholder =
                Function::new(BasicBlockId::ZERO, self.src.function(old_id).num_outputs());
            self.state.function_map.insert(old_id, self.dst.functions.push(placeholder));
            true
        }
    }

    fn emit_block(&mut self, old_id: BasicBlockId) {
        if self.state.block_map.contains_key(&old_id) {
            return;
        }
        if self.live_blocks.is_some_and(|blocks| !blocks.contains(old_id)) {
            return;
        }

        let placeholder = BasicBlock {
            inputs: Span::new(LocalIdx::ZERO, LocalIdx::ZERO),
            outputs: Span::new(LocalIdx::ZERO, LocalIdx::ZERO),
            operations: Span::new(OperationIdx::ZERO, OperationIdx::ZERO),
            control: Control::LastOpTerminates,
        };
        let new_id = self.dst.basic_blocks.push(placeholder);
        self.state.block_map.insert(old_id, new_id);
        let block = self.src.block(old_id);

        let inputs = self.emit_block_locals(block.inputs());
        let outputs = self.emit_block_locals(block.outputs());
        let operations = self.emit_block_operations(block);

        self.dst.basic_blocks[new_id] =
            BasicBlock { inputs, outputs, operations, control: Control::LastOpTerminates };

        self.discover_successors(block);
    }

    fn emit_block_locals(&mut self, locals: &[LocalId]) -> Span<LocalIdx> {
        let start = self.dst.locals.next_idx();
        for local in locals {
            self.emit_local(*local);
            self.dst.locals.push(self.state.local_map[local]);
        }
        Span::new(start, self.dst.locals.next_idx())
    }

    fn emit_local(&mut self, local: LocalId) {
        self.state
            .local_map
            .entry(local)
            .or_insert_with(|| self.dst.next_free_local_id.get_and_inc());
    }

    fn emit_block_operations(&mut self, block: BlockView<'_>) -> Span<OperationIdx> {
        let start = self.dst.operations.next_idx();
        for op in block.operations() {
            let operation = op.op();
            if matches!(operation, Operation::Noop(())) {
                continue;
            }
            operation.visit_data(self);
            let remapped = self.remap_operation(operation);
            self.dst.operations.push(remapped);
        }
        Span::new(start, self.dst.operations.next_idx())
    }

    fn remap_operation(&mut self, mut op: Operation) -> Operation {
        op.visit_data_mut(self);
        op
    }

    fn discover_successors(&mut self, block: BlockView<'_>) {
        match block.control() {
            ControlView::LastOpTerminates | ControlView::InternalReturn => {}
            ControlView::ContinuesTo(to) => self.push_block(to),
            ControlView::Branches { condition, non_zero_target, zero_target } => {
                debug_assert!(self.state.local_map.contains_key(&condition));
                self.push_block(non_zero_target);
                self.push_block(zero_target);
            }
            ControlView::Switch(switch) => {
                debug_assert!(self.state.local_map.contains_key(&switch.condition()));
                if let Some(fb) = switch.fallback() {
                    self.push_block(fb);
                }
                let old_cases = &self.src.cases[switch.cases_id()];
                for i in 0..old_cases.cases_count {
                    self.emit_large_const(old_cases.values_start_id + i);
                }
                for old_bb_id in old_cases.get_bb_ids(self.src).as_raw_slice() {
                    self.push_block(*old_bb_id);
                }
            }
        }
    }

    fn push_block(&mut self, bb: BasicBlockId) {
        debug_assert!(
            self.live_blocks.is_none_or(|live| live.contains(bb)),
            "successor {bb:?} should be in live_blocks"
        );
        self.state.block_worklist.push(bb);
    }

    fn patch_block_control(&mut self) {
        let block_map = &self.state.block_map;
        let local_map = &self.state.local_map;
        let large_const_map = &self.state.large_const_map;
        let cases_map = &mut self.state.cases_map;

        for (old_id, new_id) in block_map {
            let new_control = match self.src.block(*old_id).control() {
                ControlView::LastOpTerminates => Control::LastOpTerminates,
                ControlView::InternalReturn => Control::InternalReturn,
                ControlView::ContinuesTo(bb) => Control::ContinuesTo(block_map[&bb]),
                ControlView::Branches { condition, non_zero_target, zero_target } => {
                    Control::Branches(Branch {
                        condition: local_map[&condition],
                        non_zero_target: block_map[&non_zero_target],
                        zero_target: block_map[&zero_target],
                    })
                }
                ControlView::Switch(switch) => {
                    let cases_id = *cases_map.entry(switch.cases_id()).or_insert_with(|| {
                        let old_cases = &self.src.cases[switch.cases_id()];
                        let new_values_start = large_const_map[&old_cases.values_start_id];

                        debug_assert!(
                            (0..old_cases.cases_count).all(|i| {
                                large_const_map[&(old_cases.values_start_id + i)]
                                    == new_values_start + i
                            }),
                            "case value large consts should be contiguous after emission"
                        );

                        let new_targets_start = self.dst.cases_bb_ids.next_idx();
                        for old_bb_id in old_cases.get_bb_ids(self.src).as_raw_slice() {
                            self.dst.cases_bb_ids.push(block_map[old_bb_id]);
                        }

                        self.dst.cases.push(Cases {
                            values_start_id: new_values_start,
                            targets_start_id: new_targets_start,
                            cases_count: old_cases.cases_count,
                        })
                    });
                    Control::Switch(Switch {
                        condition: local_map[&switch.condition()],
                        fallback: switch.fallback().map(|fb| block_map[&fb]),
                        cases: cases_id,
                    })
                }
            };
            self.dst.basic_blocks[*new_id].control = new_control;
        }
    }

    fn emit_static_alloc(&mut self, alloc_id: StaticAllocId) {
        self.state
            .static_alloc_map
            .entry(alloc_id)
            .or_insert_with(|| self.dst.next_static_alloc_id.get_and_inc());
    }

    fn emit_large_const(&mut self, const_id: LargeConstId) {
        self.state
            .large_const_map
            .entry(const_id)
            .or_insert_with(|| self.dst.large_consts.push(self.src.large_consts[const_id]));
    }

    fn emit_data(&mut self, data_id: DataId) {
        self.state.data_map.entry(data_id).or_insert_with(|| {
            self.dst.data_segments.push_copy_slice(&self.src.data_segments[data_id])
        });
    }
}

impl<'a> OpVisitor<'_, ()> for Rewriter<'a> {
    fn visit_inline_operands<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'_ sir_data::operation::InlineOperands<INS, OUTS>,
    ) {
        for local in data.ins.iter().chain(data.outs.iter()) {
            self.emit_local(*local);
        }
    }

    fn visit_allocated_ins<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'_ sir_data::operation::AllocatedIns<INS, OUTS>,
    ) {
        for local in data.get_inputs(self.src).iter().chain(data.outs.iter()) {
            self.emit_local(*local);
        }
    }

    fn visit_static_alloc(&mut self, data: &'_ sir_data::operation::StaticAllocData) {
        self.emit_local(data.ptr_out);
        self.emit_static_alloc(data.alloc_id);
    }

    fn visit_memory_load(&mut self, data: &'_ sir_data::operation::MemoryLoadData) {
        self.emit_local(data.out);
        self.emit_local(data.ptr);
    }

    fn visit_memory_store(&mut self, data: &'_ sir_data::operation::MemoryStoreData) {
        for local in data.ins {
            self.emit_local(local);
        }
    }

    fn visit_set_small_const(&mut self, data: &'_ sir_data::operation::SetSmallConstData) {
        self.emit_local(data.sets);
    }

    fn visit_set_large_const(&mut self, data: &'_ sir_data::operation::SetLargeConstData) {
        self.emit_local(data.sets);
        self.emit_large_const(data.value);
    }

    fn visit_set_data_offset(&mut self, data: &'_ sir_data::operation::SetDataOffsetData) {
        self.emit_local(data.sets);
        self.emit_data(data.segment_id);
    }

    fn visit_icall(&mut self, data: &'_ sir_data::operation::InternalCallData) {
        if self.reserve_function_id(data.function) {
            self.state.func_worklist.push(data.function);
        }

        for local in data.get_inputs(self.src).iter().chain(data.get_outputs(self.src).iter()) {
            self.emit_local(*local);
        }
    }

    fn visit_void(&mut self) {}
}

impl<'a> OpVisitorMut<'_, ()> for Rewriter<'a> {
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
        data.value = self.state.large_const_map[&data.value];
    }

    fn visit_set_data_offset_mut(&mut self, data: &mut sir_data::operation::SetDataOffsetData) {
        data.sets = self.state.local_map[&data.sets];
        data.segment_id = self.state.data_map[&data.segment_id];
    }

    fn visit_icall_mut(&mut self, data: &mut sir_data::operation::InternalCallData) {
        let new_ins_start = self.dst.locals.next_idx();
        for old_local in data.get_inputs(self.src) {
            self.dst.locals.push(self.state.local_map[old_local]);
        }

        let new_outs_start = self.dst.locals.next_idx();
        for old_local in data.get_outputs(self.src) {
            self.dst.locals.push(self.state.local_map[old_local]);
        }

        data.function = self.state.function_map[&data.function];
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
    fn test_sccp_unused_elim_and_defragment() {
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
        let mut defragmenter = Defragmenter::new();
        defragmenter.run(&ir, &mut dst, Some(&sccp.reachable));

        let dst_str = sir_data::display_program(&dst);
        let expected_dst = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @2  (outputs: 1)

Basic Blocks:
    @0 {
        => @1
    }

    @1 {
        $0 = const 0x1
        $1 = const 0x2
        $2 = icall @1 $0 $1
        $3 = const 0x0
        sstore $3 $2
        stop
    }

    @2 $4 $5 -> $6 {
        $6 = add $4 $5
        iret
    }
        "#;
        assert_trim_strings_eq_with_diff(&dst_str, expected_dst, "dst after defragment");

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
    fn test_defragment_dead_function_data() {
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
        assert_trim_strings_eq_with_diff(&src_str, expected_src, "src before defragment");

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
        let mut defragmenter = Defragmenter::new();
        defragmenter.run(&ir, &mut dst, None);

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
            1 => @2,
            2 => @1,
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
        assert_trim_strings_eq_with_diff(&dst_str, expected_dst, "dst after defragment");

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
