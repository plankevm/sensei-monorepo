use sensei_core::span::IncIterable;
use sir_data::{
    BasicBlock, BasicBlockId, Branch, Cases, CasesId, Control, ControlView, DataId, DenseIndexSet,
    EthIRProgram, Function, FunctionId, Idx, LargeConstId, LocalId, LocalIdx, Operation,
    OperationIdx, Span, StaticAllocId, Switch,
    operation::{OpVisitor, OpVisitorMut},
};
use std::collections::HashMap;

pub struct PrunerState {
    func_worklist: Vec<FunctionId>,
    block_worklist: Vec<BasicBlockId>,
    next_free_local_id: LocalId,
    local_map: HashMap<LocalId, LocalId>,
    next_static_alloc_id: StaticAllocId,
    static_alloc_map: HashMap<StaticAllocId, StaticAllocId>,
    large_const_map: HashMap<LargeConstId, Option<LargeConstId>>,
    data_map: HashMap<DataId, Option<DataId>>,
    function_map: HashMap<FunctionId, Option<FunctionId>>,
    block_map: HashMap<BasicBlockId, Option<BasicBlockId>>,
    cases_map: HashMap<CasesId, Option<CasesId>>,
}

impl Default for PrunerState {
    fn default() -> Self {
        Self::new()
    }
}

impl PrunerState {
    pub fn new() -> Self {
        Self {
            func_worklist: Vec::new(),
            block_worklist: Vec::new(),
            next_free_local_id: LocalId::ZERO,
            local_map: HashMap::new(),
            next_static_alloc_id: StaticAllocId::ZERO,
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
        self.next_free_local_id = LocalId::ZERO;
        self.local_map.clear();
        self.next_static_alloc_id = StaticAllocId::ZERO;
        self.static_alloc_map.clear();
        self.large_const_map.clear();
        self.data_map.clear();
        self.function_map.clear();
        self.block_map.clear();
        self.cases_map.clear();
    }

    pub fn run(
        &mut self,
        old: &EthIRProgram,
        new: &mut EthIRProgram,
        sccp_reachable: Option<&DenseIndexSet<BasicBlockId>>,
    ) {
        self.clear();
        new.clear();
        let mut pruner = GlobalPruner { state: self, old, new, sccp_reachable };
        pruner.analyze();
        pruner.apply();
    }
}

struct GlobalPruner<'a> {
    state: &'a mut PrunerState,
    old: &'a EthIRProgram,
    new: &'a mut EthIRProgram,
    sccp_reachable: Option<&'a DenseIndexSet<BasicBlockId>>,
}

impl<'a> GlobalPruner<'a> {
    fn analyze(&mut self) {
        self.state.func_worklist.push(self.old.init_entry);
        if let Some(main) = self.old.main_entry {
            self.state.func_worklist.push(main);
        }

        while let Some(function) = self.state.func_worklist.pop() {
            self.track_function(function);
        }
    }

    fn apply(&mut self) {
        self.copy_data_segments();
        self.copy_large_consts();
        self.copy_basic_block_ids();
        self.copy_cases();
        self.copy_functions();
        self.copy_block_contents();

        self.new.init_entry =
            self.state.function_map[&self.old.init_entry].expect("init_entry should be copied");
        self.new.main_entry = self
            .old
            .main_entry
            .map(|m| self.state.function_map[&m].expect("main_entry should be copied"));
    }

    fn copy_data_segments(&mut self) {
        for (old_id, _) in self.old.data_segments_start.enumerate_idx() {
            if let Some(None) = self.state.data_map.get_mut(&old_id) {
                let span = self.old.get_segment_span(old_id);
                let bytes = &self.old.data_bytes.as_raw_slice()
                    [span.start.get() as usize..span.end.get() as usize];
                let start_offset = self.new.data_bytes.next_idx();
                self.new.data_bytes.as_mut_vec().extend_from_slice(bytes);
                let new_id = self.new.data_segments_start.push(start_offset);
                self.state.data_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn copy_large_consts(&mut self) {
        for (old_id, &value) in self.old.large_consts.enumerate_idx() {
            if let Some(None) = self.state.large_const_map.get(&old_id) {
                let new_id = self.new.large_consts.push(value);
                self.state.large_const_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn copy_basic_block_ids(&mut self) {
        for (old_id, _) in self.old.basic_blocks.enumerate_idx() {
            if let Some(None) = self.state.block_map.get(&old_id) {
                let placeholder = BasicBlock {
                    inputs: Span::new(LocalIdx::ZERO, LocalIdx::ZERO),
                    outputs: Span::new(LocalIdx::ZERO, LocalIdx::ZERO),
                    operations: Span::new(OperationIdx::ZERO, OperationIdx::ZERO),
                    control: Control::LastOpTerminates,
                };
                let new_id = self.new.basic_blocks.push(placeholder);
                self.state.block_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn copy_cases(&mut self) {
        for (old_id, old_cases) in self.old.cases.enumerate_idx() {
            if let Some(None) = self.state.cases_map.get(&old_id) {
                let new_values_start = self.state.large_const_map[&old_cases.values_start_id]
                    .expect("large const should be copied");

                let new_targets_start = self.new.cases_bb_ids.next_idx();
                for old_bb_id in old_cases.get_bb_ids(self.old).as_raw_slice() {
                    let new_bb_id =
                        self.state.block_map[old_bb_id].expect("block should be copied");
                    self.new.cases_bb_ids.push(new_bb_id);
                }

                let new_cases = Cases {
                    values_start_id: new_values_start,
                    targets_start_id: new_targets_start,
                    cases_count: old_cases.cases_count,
                };
                let new_id = self.new.cases.push(new_cases);
                self.state.cases_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn copy_functions(&mut self) {
        for (old_id, old_func) in self.old.functions.enumerate_idx() {
            if let Some(None) = self.state.function_map.get(&old_id) {
                let new_entry =
                    self.state.block_map[&old_func.entry()].expect("entry block should be copied");
                let new_func = Function::new(new_entry, old_func.get_outputs());
                let new_id = self.new.functions.push(new_func);
                self.state.function_map.insert(old_id, Some(new_id));
            }
        }
    }

    fn copy_block_contents(&mut self) {
        for (old_id, old_block) in self.old.basic_blocks.enumerate_idx() {
            if let Some(Some(new_id)) = self.state.block_map.get(&old_id).copied() {
                let inputs_start = self.new.locals.next_idx();
                for old_local in self.old.block(old_id).inputs() {
                    let new_local = self.state.local_map[old_local];
                    self.new.locals.push(new_local);
                }
                let inputs_end = self.new.locals.next_idx();

                let outputs_start = self.new.locals.next_idx();
                for old_local in self.old.block(old_id).outputs() {
                    let new_local = self.state.local_map[old_local];
                    self.new.locals.push(new_local);
                }
                let outputs_end = self.new.locals.next_idx();

                let ops_start = self.new.operations.next_idx();
                for op in self.old.block(old_id).operations() {
                    if matches!(op.op(), Operation::Noop(())) {
                        continue;
                    }
                    let remapped_op = self.remap_operation(op.op());
                    self.new.operations.push(remapped_op);
                }
                let ops_end = self.new.operations.next_idx();

                let new_control = self.remap_control(&old_block.control);

                self.new.basic_blocks[new_id] = BasicBlock {
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
                    .expect("block block_should be copied"),
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
        self.state.block_worklist.clear();
        self.state.block_worklist.push(self.old.function(function).entry().id());
        while let Some(bb) = self.state.block_worklist.pop() {
            self.track_block(bb);
        }
    }

    fn track_block(&mut self, bb: BasicBlockId) {
        if self.state.block_map.contains_key(&bb) {
            return;
        }
        if self.sccp_reachable.is_some_and(|reachable| !reachable.contains(bb)) {
            return;
        }

        self.state.block_map.insert(bb, None);
        let block = self.old.block(bb);

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
            let new_id = self.state.next_free_local_id.get_and_inc();
            self.state.local_map.insert(local, new_id);
        }
    }

    fn track_static_alloc(&mut self, alloc_id: StaticAllocId) {
        if !self.state.static_alloc_map.contains_key(&alloc_id) {
            let new_id = self.state.next_static_alloc_id.get_and_inc();
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

impl<'a> OpVisitor<'_, ()> for GlobalPruner<'a> {
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
        for local in data.get_inputs(self.old).iter().chain(data.outs.iter()) {
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

        for &local in data.get_inputs(self.old).iter().chain(data.get_outputs(self.old).iter()) {
            self.track_local(local);
        }
    }

    fn visit_void(&mut self) {}
}

impl<'a> OpVisitorMut<'_, ()> for GlobalPruner<'a> {
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
        let new_ins_start = self.new.locals.next_idx();
        for old_local in data.get_inputs(self.old) {
            self.new.locals.push(self.state.local_map[old_local]);
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
        data.function = self.state.function_map[&data.function].expect("function should be copied");

        let new_ins_start = self.new.locals.next_idx();
        for &old_local in data.get_inputs(self.old) {
            self.new.locals.push(self.state.local_map[&old_local]);
        }

        let new_outs_start = self.new.locals.next_idx();
        for &old_local in data.get_outputs(self.old) {
            self.new.locals.push(self.state.local_map[&old_local]);
        }

        data.ins_start = new_ins_start;
        data.outs_start = new_outs_start;
    }

    fn visit_void_mut(&mut self) {}
}
