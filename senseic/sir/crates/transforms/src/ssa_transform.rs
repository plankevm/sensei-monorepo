use sensei_core::IncIterable;
use sir_analyses::{compute_dominance_frontiers, compute_dominators, compute_predecessors};
use sir_data::{
    BasicBlock, BasicBlockId, Branch, Control, DenseIndexSet, EthIRProgram, Idx, IndexVec, LocalId,
    LocalIdx, Span, Switch, index_vec, operation::OpVisitorMut,
};

pub fn ssa_transform(program: &mut EthIRProgram) {
    let mut predecessors = IndexVec::new();
    compute_predecessors(program, &mut predecessors);
    split_critical_edges(program, &predecessors);
    compute_predecessors(program, &mut predecessors);
    SsaTransform::new(program, predecessors).run(program);
}

struct SsaTransform {
    def_sites: IndexVec<LocalId, DenseIndexSet<BasicBlockId>>,
    dominators: IndexVec<BasicBlockId, Option<BasicBlockId>>,
    dominator_tree: IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    phi_locations: IndexVec<BasicBlockId, Vec<LocalId>>,
    predecessors: IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    dominance_frontiers: IndexVec<BasicBlockId, DenseIndexSet<BasicBlockId>>,
}

impl SsaTransform {
    fn new(
        program: &EthIRProgram,
        predecessors: IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    ) -> Self {
        let dominators = compute_dominators(program);
        let dominance_frontiers = compute_dominance_frontiers(&dominators, &predecessors);

        let mut dominator_tree = index_vec![Vec::new(); dominators.len()];
        for (bb, &idom) in dominators.enumerate_idx() {
            if let Some(parent) = idom
                && parent != bb
            {
                dominator_tree[parent].push(bb);
            }
        }

        let def_sites = Self::collect_definition_sites(program);

        Self {
            def_sites,
            dominators,
            dominator_tree,
            predecessors,
            dominance_frontiers,
            phi_locations: index_vec![Vec::new(); program.basic_blocks.len()],
        }
    }

    fn collect_definition_sites(
        program: &EthIRProgram,
    ) -> IndexVec<LocalId, DenseIndexSet<BasicBlockId>> {
        let mut def_sites = index_vec![DenseIndexSet::new(); program.next_free_local_id.idx()];
        for block in program.blocks() {
            for &local in block.inputs() {
                def_sites[local].add(block.id());
            }
            for op in block.operations() {
                for &local in op.outputs() {
                    def_sites[local].add(block.id());
                }
            }
        }
        def_sites
    }

    fn run(&mut self, program: &mut EthIRProgram) {
        self.compute_phi_locations();
        self.rename(program);
        self.cleanup_trivial_phis(program);
    }

    fn compute_phi_locations(&mut self) {
        let mut worklist = Vec::new();
        let mut visited = DenseIndexSet::new();
        for (local, def_blocks) in self.def_sites.enumerate_idx() {
            if def_blocks.len() <= 1 {
                continue;
            }
            visited.clear();
            for bb in def_blocks.iter() {
                worklist.push(bb);
            }
            while let Some(bb) = worklist.pop() {
                for frontier_block in self.dominance_frontiers[bb].iter() {
                    if visited.add(frontier_block) {
                        self.phi_locations[frontier_block].push(local);
                        worklist.push(frontier_block);
                    }
                }
            }
        }
    }

    fn rename(&mut self, program: &mut EthIRProgram) {
        let num_locals = program.next_free_local_id.idx();
        let mut counters = index_vec![0; num_locals];
        let mut stacks = index_vec![Vec::new(); num_locals];
        for func_id in program.functions.iter_idx() {
            self.rename_block(
                program,
                program.functions[func_id].entry(),
                &mut counters,
                &mut stacks,
            );
        }
        todo!()
    }

    fn rename_block(
        &mut self,
        program: &mut EthIRProgram,
        bb: BasicBlockId,
        counters: &mut IndexVec<LocalId, u32>,
        stacks: &mut IndexVec<LocalId, Vec<LocalId>>,
    ) {
        // 1. Rename existing block inputs and add phi inputs
        let old_inputs_span = program.basic_blocks[bb].inputs;
        let new_inputs_start = program.locals.next_idx();
        for idx in old_inputs_span.iter() {
            let local = program.locals[idx];
            let renamed = rename_use(stacks, local);
            program.locals.push(renamed);
        }
        for &local in &self.phi_locations[bb] {
            let new_version = rename_def(stacks, &mut program.next_free_local_id, local);
            program.locals.push(new_version);
        }
        program.basic_blocks[bb].inputs = Span::new(new_inputs_start, program.locals.next_idx());

        // 2. Rename uses and defs in operations
        let mut renamer = Renamer { program, stacks };
        for op_idx in renamer.program.basic_blocks[bb].operations.iter() {
            let mut op = renamer.program.operations[op_idx];
            op.visit_data_mut(&mut renamer);
            renamer.program.operations[op_idx] = op;
        }
        let program = renamer.program;
        let stacks = renamer.stacks;

        // 3. For each successor, add phi operands to this block's outputs
        let successors: Vec<_> = program.basic_blocks[bb].control.iter_outgoing(program).collect();
        for succ in successors {
            if self.phi_locations[succ].is_empty() {
                continue;
            }
            let old_outputs_span = program.basic_blocks[bb].outputs;
            let new_outputs_start = program.locals.next_idx();
            for idx in old_outputs_span.iter() {
                program.locals.push(program.locals[idx]);
            }
            for &phi_local in &self.phi_locations[succ] {
                let version = rename_use(stacks, phi_local);
                program.locals.push(version);
            }
            program.basic_blocks[bb].outputs =
                Span::new(new_outputs_start, program.locals.next_idx());
        }

        // 4. Recurse into dominator tree children
        // TODO

        // 5. Pop versions defined in this block
        // TODO
    }

    fn cleanup_trivial_phis(&mut self, _program: &mut EthIRProgram) {
        todo!()
    }
}

struct Renamer<'a> {
    program: &'a mut EthIRProgram,
    stacks: &'a mut IndexVec<LocalId, Vec<LocalId>>,
}

fn rename_use(stacks: &IndexVec<LocalId, Vec<LocalId>>, local: LocalId) -> LocalId {
    *stacks[local].last().expect("local not in scope")
}

fn rename_def(
    stacks: &mut IndexVec<LocalId, Vec<LocalId>>,
    next_local: &mut LocalId,
    local: LocalId,
) -> LocalId {
    let new_version = next_local.get_and_inc();
    stacks[local].push(new_version);
    new_version
}

impl OpVisitorMut<'_, ()> for Renamer<'_> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut sir_data::operation::InlineOperands<INS, OUTS>,
    ) {
        for local in &mut data.ins {
            *local = rename_use(self.stacks, *local);
        }
        for local in &mut data.outs {
            *local = rename_def(self.stacks, &mut self.program.next_free_local_id, *local);
        }
    }

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut sir_data::operation::AllocatedIns<INS, OUTS>,
    ) {
        for local in data.get_inputs_mut(self.program) {
            *local = rename_use(self.stacks, *local);
        }
        for local in &mut data.outs {
            *local = rename_def(self.stacks, &mut self.program.next_free_local_id, *local);
        }
    }

    fn visit_static_alloc_mut(&mut self, data: &mut sir_data::operation::StaticAllocData) {
        data.ptr_out = rename_def(self.stacks, &mut self.program.next_free_local_id, data.ptr_out);
    }

    fn visit_memory_load_mut(&mut self, data: &mut sir_data::operation::MemoryLoadData) {
        data.ptr = rename_use(self.stacks, data.ptr);
        data.out = rename_def(self.stacks, &mut self.program.next_free_local_id, data.out);
    }

    fn visit_memory_store_mut(&mut self, data: &mut sir_data::operation::MemoryStoreData) {
        for local in &mut data.ins {
            *local = rename_use(self.stacks, *local);
        }
    }

    fn visit_set_small_const_mut(&mut self, data: &mut sir_data::operation::SetSmallConstData) {
        data.sets = rename_def(self.stacks, &mut self.program.next_free_local_id, data.sets);
    }

    fn visit_set_large_const_mut(&mut self, data: &mut sir_data::operation::SetLargeConstData) {
        data.sets = rename_def(self.stacks, &mut self.program.next_free_local_id, data.sets);
    }

    fn visit_set_data_offset_mut(&mut self, data: &mut sir_data::operation::SetDataOffsetData) {
        data.sets = rename_def(self.stacks, &mut self.program.next_free_local_id, data.sets);
    }

    fn visit_icall_mut(&mut self, data: &mut sir_data::operation::InternalCallData) {
        for local in &mut self.program.locals[data.ins_start..data.outs_start] {
            *local = rename_use(self.stacks, *local);
        }
        let output_count = self.program.functions[data.function].get_outputs();
        for local in &mut self.program.locals[data.outs_start..data.outs_start + output_count] {
            *local = rename_def(self.stacks, &mut self.program.next_free_local_id, *local);
        }
    }

    fn visit_void_mut(&mut self) {}
}

fn split_critical_edges(
    program: &mut EthIRProgram,
    predecessors: &IndexVec<BasicBlockId, Vec<BasicBlockId>>,
) {
    let original_block_count = program.basic_blocks.len();
    for bb_idx in 0..original_block_count {
        let bb = BasicBlockId::new(bb_idx as u32);

        match program.basic_blocks[bb].control {
            Control::Branches(Branch { condition, non_zero_target, zero_target }) => {
                program.basic_blocks[bb].control = Control::Branches(Branch {
                    condition,
                    non_zero_target: split_edge(program, predecessors, bb, non_zero_target),
                    zero_target: split_edge(program, predecessors, bb, zero_target),
                });
            }
            Control::Switch(Switch { cases, fallback, .. }) => {
                let cases_data = program.cases[cases];
                for target_idx in cases_data.target_indices().iter() {
                    let target = program.cases_bb_ids[target_idx];
                    program.cases_bb_ids[target_idx] =
                        split_edge(program, predecessors, bb, target);
                }
                if let Some(fallback) = fallback {
                    let new_fallback = split_edge(program, predecessors, bb, fallback);
                    let Control::Switch(ref mut switch) = program.basic_blocks[bb].control else {
                        unreachable!()
                    };
                    switch.fallback = Some(new_fallback);
                }
            }
            _ => {}
        }
    }
}

fn split_edge(
    program: &mut EthIRProgram,
    predecessors: &IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    source: BasicBlockId,
    target: BasicBlockId,
) -> BasicBlockId {
    if predecessors[target].len() > 1 {
        insert_forwarding_block(program, source, target)
    } else {
        target
    }
}

fn insert_forwarding_block(
    program: &mut EthIRProgram,
    source: BasicBlockId,
    target: BasicBlockId,
) -> BasicBlockId {
    let source_outputs = program.basic_blocks[source].outputs;
    let empty_ops = Span::new(program.operations.next_idx(), program.operations.next_idx());

    let inputs = copy_span(program, source_outputs);
    let outputs = copy_span(program, source_outputs);

    program.basic_blocks.push(BasicBlock {
        inputs,
        outputs,
        operations: empty_ops,
        control: Control::ContinuesTo(target),
    })
}

fn copy_span(program: &mut EthIRProgram, span: Span<LocalIdx>) -> Span<LocalIdx> {
    let start = program.locals.next_idx();
    for idx in span.iter() {
        program.locals.push(program.locals[idx]);
    }
    Span::new(start, program.locals.next_idx())
}
