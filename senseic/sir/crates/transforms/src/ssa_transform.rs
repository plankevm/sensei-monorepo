use hashbrown::HashSet;
use sensei_core::IncIterable;
use sir_analyses::{
    compute_dominance_frontiers, compute_dominators_from_predecessors, compute_predecessors,
};
use sir_data::{
    BasicBlock, BasicBlockId, Branch, Control, EthIRProgram, Idx, IndexVec, LocalId, LocalIdx,
    Span, Switch, index_vec, operation::OpVisitorMut,
};

pub fn ssa_transform(program: &mut EthIRProgram) {
    let mut predecessors = IndexVec::new();
    compute_predecessors(program, &mut predecessors);
    split_critical_edges(program, &predecessors);
    compute_predecessors(program, &mut predecessors);
    SsaTransform::new(program, predecessors).run(program);
}

struct SsaTransform {
    def_sites: IndexVec<LocalId, HashSet<BasicBlockId>>,
    dominators: IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    phi_locations: IndexVec<BasicBlockId, Vec<LocalId>>,
    dominance_frontiers: IndexVec<BasicBlockId, HashSet<BasicBlockId>>,
}

impl SsaTransform {
    fn new(
        program: &EthIRProgram,
        predecessors: IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    ) -> Self {
        let dominators_child_to_parent =
            compute_dominators_from_predecessors(program, &predecessors);
        let mut dominators_parent_to_child =
            index_vec![Vec::new(); dominators_child_to_parent.len()];
        for (bb, &idom) in dominators_child_to_parent.enumerate_idx() {
            if let Some(parent) = idom
                && parent != bb
            {
                dominators_parent_to_child[parent].push(bb);
            }
        }

        let dominance_frontiers =
            compute_dominance_frontiers(&dominators_child_to_parent, &predecessors);

        let def_sites = Self::collect_definition_sites(program);

        Self {
            def_sites,
            dominators: dominators_parent_to_child,
            dominance_frontiers,
            phi_locations: index_vec![Vec::new(); program.basic_blocks.len()],
        }
    }

    fn run(&mut self, program: &mut EthIRProgram) {
        self.compute_phi_locations();
        self.rename(program);
    }

    fn collect_definition_sites(
        program: &EthIRProgram,
    ) -> IndexVec<LocalId, HashSet<BasicBlockId>> {
        let mut def_sites = index_vec![HashSet::new(); program.next_free_local_id.idx()];
        for block in program.blocks() {
            for &local in block.inputs() {
                def_sites[local].insert(block.id());
            }
            for op in block.operations() {
                for &local in op.outputs() {
                    def_sites[local].insert(block.id());
                }
            }
        }
        def_sites
    }

    fn compute_phi_locations(&mut self) {
        let mut worklist = Vec::new();
        for (local, def_blocks) in self.def_sites.enumerate_idx() {
            if def_blocks.len() <= 1 {
                continue;
            }
            for bb in def_blocks {
                worklist.push(*bb);
            }
            while let Some(bb) = worklist.pop() {
                for &frontier_block in &self.dominance_frontiers[bb] {
                    if !self.phi_locations[frontier_block].contains(&local) {
                        self.phi_locations[frontier_block].push(local);
                        worklist.push(frontier_block);
                    }
                }
            }
        }
    }

    fn rename(&mut self, program: &mut EthIRProgram) {
        let num_locals = program.next_free_local_id.idx();
        let mut local_versions = index_vec![Vec::new(); num_locals];
        let mut rename_trail = Vec::new();
        for func_id in program.functions.iter_idx() {
            self.rename_block(
                program,
                program.functions[func_id].entry(),
                &mut local_versions,
                &mut rename_trail,
            );
        }
    }

    fn rename_block(
        &mut self,
        program: &mut EthIRProgram,
        bb: BasicBlockId,
        local_versions: &mut IndexVec<LocalId, Vec<LocalId>>,
        rename_trail: &mut Vec<LocalId>,
    ) {
        let checkpoint = rename_trail.len();

        self.rename_block_inputs(program, bb, local_versions, rename_trail);

        rename_operations(program, bb, local_versions, rename_trail);

        match &mut program.basic_blocks[bb].control {
            Control::Branches(branch) => {
                branch.condition = rename_use(local_versions, branch.condition);
            }
            Control::Switch(switch) => {
                switch.condition = rename_use(local_versions, switch.condition);
            }
            _ => {}
        }

        self.rename_block_outputs(program, bb, local_versions);

        for i in 0..self.dominators[bb].len() {
            let child = self.dominators[bb][i];
            self.rename_block(program, child, local_versions, rename_trail);
        }

        for local in &rename_trail[checkpoint..] {
            local_versions[*local].pop();
        }
        rename_trail.truncate(checkpoint);
    }

    fn rename_block_inputs(
        &self,
        program: &mut EthIRProgram,
        bb: BasicBlockId,
        local_versions: &mut IndexVec<LocalId, Vec<LocalId>>,
        rename_trail: &mut Vec<LocalId>,
    ) {
        let old_inputs_span = program.basic_blocks[bb].inputs;
        let new_inputs_start = program.locals.next_idx();
        for idx in old_inputs_span.iter() {
            let local = program.locals[idx];
            let renamed =
                rename_def(local_versions, rename_trail, &mut program.next_free_local_id, local);
            program.locals.push(renamed);
        }
        for local in &self.phi_locations[bb] {
            let renamed =
                rename_def(local_versions, rename_trail, &mut program.next_free_local_id, *local);
            program.locals.push(renamed);
        }
        program.basic_blocks[bb].inputs = Span::new(new_inputs_start, program.locals.next_idx());
    }

    fn rename_block_outputs(
        &self,
        program: &mut EthIRProgram,
        bb: BasicBlockId,
        local_versions: &IndexVec<LocalId, Vec<LocalId>>,
    ) {
        let old_outputs_span = program.basic_blocks[bb].outputs;
        let new_outputs_start = program.locals.next_idx();
        for idx in old_outputs_span.iter() {
            program.locals.push(rename_use(local_versions, program.locals[idx]));
        }
        // After critical edge splitting, only single-successor blocks (ContinuesTo) can
        // target a join block with phis. This lets us avoid collecting successors into a Vec.
        if let Control::ContinuesTo(succ) = program.basic_blocks[bb].control {
            for local in &self.phi_locations[succ] {
                program.locals.push(rename_use(local_versions, *local));
            }
        }
        program.basic_blocks[bb].outputs = Span::new(new_outputs_start, program.locals.next_idx());
    }
}

struct Renamer<'a> {
    program: &'a mut EthIRProgram,
    local_versions: &'a mut IndexVec<LocalId, Vec<LocalId>>,
    rename_trail: &'a mut Vec<LocalId>,
}

impl OpVisitorMut<'_, ()> for Renamer<'_> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut sir_data::operation::InlineOperands<INS, OUTS>,
    ) {
        for local in &mut data.ins {
            *local = rename_use(self.local_versions, *local);
        }
        for local in &mut data.outs {
            *local = rename_def(
                self.local_versions,
                self.rename_trail,
                &mut self.program.next_free_local_id,
                *local,
            );
        }
    }

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut sir_data::operation::AllocatedIns<INS, OUTS>,
    ) {
        for local in data.get_inputs_mut(self.program) {
            *local = rename_use(self.local_versions, *local);
        }
        for local in &mut data.outs {
            *local = rename_def(
                self.local_versions,
                self.rename_trail,
                &mut self.program.next_free_local_id,
                *local,
            );
        }
    }

    fn visit_static_alloc_mut(&mut self, data: &mut sir_data::operation::StaticAllocData) {
        data.ptr_out = rename_def(
            self.local_versions,
            self.rename_trail,
            &mut self.program.next_free_local_id,
            data.ptr_out,
        );
    }

    fn visit_memory_load_mut(&mut self, data: &mut sir_data::operation::MemoryLoadData) {
        data.ptr = rename_use(self.local_versions, data.ptr);
        data.out = rename_def(
            self.local_versions,
            self.rename_trail,
            &mut self.program.next_free_local_id,
            data.out,
        );
    }

    fn visit_memory_store_mut(&mut self, data: &mut sir_data::operation::MemoryStoreData) {
        for local in &mut data.ins {
            *local = rename_use(self.local_versions, *local);
        }
    }

    fn visit_set_small_const_mut(&mut self, data: &mut sir_data::operation::SetSmallConstData) {
        data.sets = rename_def(
            self.local_versions,
            self.rename_trail,
            &mut self.program.next_free_local_id,
            data.sets,
        );
    }

    fn visit_set_large_const_mut(&mut self, data: &mut sir_data::operation::SetLargeConstData) {
        data.sets = rename_def(
            self.local_versions,
            self.rename_trail,
            &mut self.program.next_free_local_id,
            data.sets,
        );
    }

    fn visit_set_data_offset_mut(&mut self, data: &mut sir_data::operation::SetDataOffsetData) {
        data.sets = rename_def(
            self.local_versions,
            self.rename_trail,
            &mut self.program.next_free_local_id,
            data.sets,
        );
    }

    fn visit_icall_mut(&mut self, data: &mut sir_data::operation::InternalCallData) {
        for local in &mut self.program.locals[data.ins_start..data.outs_start] {
            *local = rename_use(self.local_versions, *local);
        }
        let output_count = self.program.functions[data.function].get_outputs();
        for local in &mut self.program.locals[data.outs_start..data.outs_start + output_count] {
            *local = rename_def(
                self.local_versions,
                self.rename_trail,
                &mut self.program.next_free_local_id,
                *local,
            );
        }
    }

    fn visit_void_mut(&mut self) {}
}

fn rename_operations(
    program: &mut EthIRProgram,
    bb: BasicBlockId,
    local_versions: &mut IndexVec<LocalId, Vec<LocalId>>,
    rename_trail: &mut Vec<LocalId>,
) {
    let mut renamer = Renamer { program, local_versions, rename_trail };
    for op_idx in renamer.program.basic_blocks[bb].operations.iter() {
        let mut op = renamer.program.operations[op_idx];
        op.visit_data_mut(&mut renamer);
        renamer.program.operations[op_idx] = op;
    }
}

fn rename_use(local_versions: &IndexVec<LocalId, Vec<LocalId>>, local: LocalId) -> LocalId {
    *local_versions[local].last().expect("local not in scope")
}

fn rename_def(
    local_versions: &mut IndexVec<LocalId, Vec<LocalId>>,
    rename_trail: &mut Vec<LocalId>,
    next_local: &mut LocalId,
    local: LocalId,
) -> LocalId {
    let new_version = next_local.get_and_inc();
    local_versions[local].push(new_version);
    rename_trail.push(local);
    new_version
}

fn split_critical_edges(
    program: &mut EthIRProgram,
    predecessors: &IndexVec<BasicBlockId, Vec<BasicBlockId>>,
) {
    for bb in program.basic_blocks.iter_idx() {
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

    let inputs_start = program.locals.next_idx();
    for _ in source_outputs.iter() {
        program.locals.push(program.next_free_local_id.get_and_inc());
    }
    let inputs = Span::new(inputs_start, program.locals.next_idx());
    let outputs = copy_span(program, inputs);

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

#[cfg(test)]
mod tests {
    use super::*;
    use sir_data::display_program;
    use sir_parser::EmitConfig;

    fn parse_without_ssa(source: &str) -> EthIRProgram {
        let mut config = EmitConfig::init_only();
        config.allow_duplicate_locals = true;
        sir_parser::parse_without_legalization(source, config)
    }

    fn transform_and_legalize(program: &mut EthIRProgram) {
        ssa_transform(program);
        let ir = display_program(program);
        sir_analyses::legalize(program).unwrap_or_else(|e| panic!("{e}\n{ir}"));
    }

    #[test]
    fn test_diamond_phi_placement() {
        //       A
        //      / \
        //     B   C
        //      \ /
        //       D
        //
        // v defined in B and C.
        let mut program = parse_without_ssa(
            r#"
            fn init:
                a {
                    cond = const 1
                    => cond ? @b : @c
                }
                b -> v {
                    v = const 2
                    => @d
                }
                c -> v {
                    v = const 3
                    => @d
                }
                d v {
                    stop
                }
            "#,
        );

        let d = BasicBlockId::new(3);
        let original_v = program.block(d).inputs()[0];

        transform_and_legalize(&mut program);
        let post_ir = display_program(&program);

        let d_inputs = program.block(d).inputs();
        assert_eq!(d_inputs.len(), 2, "D should have original input + phi\n{post_ir}");
        for &input in d_inputs {
            assert_ne!(input, original_v, "phi input should be renamed\n{post_ir}");
        }
        assert_ne!(d_inputs[0], d_inputs[1], "phi inputs should be distinct\n{post_ir}");
    }

    #[test]
    fn test_partial_redef_phi() {
        //     A
        //    / \
        //   B   C
        //    \ /
        //     D
        //
        // v defined in A and B, but not C.
        let mut program = parse_without_ssa(
            r#"
            fn init:
                a -> v {
                    v = const 1
                    cond = const 0
                    => cond ? @b : @c
                }
                b v -> v {
                    v = const 2
                    => @d
                }
                c v -> v {
                    => @d
                }
                d v {
                    stop
                }
            "#,
        );

        let d = BasicBlockId::new(3);
        let original_v = program.block(d).inputs()[0];

        transform_and_legalize(&mut program);
        let post_ir = display_program(&program);

        let d_inputs = program.block(d).inputs();
        assert_eq!(d_inputs.len(), 2, "D should have original input + phi\n{post_ir}");
        for &input in d_inputs {
            assert_ne!(input, original_v, "phi input should be renamed\n{post_ir}");
        }
        assert_ne!(d_inputs[0], d_inputs[1], "phi inputs should be distinct\n{post_ir}");
    }

    #[test]
    fn test_loop_phi() {
        //   A
        //   |
        //   B <--+
        //  / \   |
        // D   C--+
        //
        // v defined in A and C.
        let mut program = parse_without_ssa(
            r#"
            fn init:
                a -> v {
                    v = const 0
                    => @b
                }
                b v -> v {
                    cond = const 1
                    => cond ? @c : @d
                }
                c v -> v {
                    one = const 1
                    v = add v one
                    => @b
                }
                d v {
                    stop
                }
            "#,
        );

        let b = BasicBlockId::new(1);
        let original_v = program.block(b).inputs()[0];

        transform_and_legalize(&mut program);
        let post_ir = display_program(&program);

        let b_inputs = program.block(b).inputs();
        assert_eq!(b_inputs.len(), 2, "B should have original input + phi\n{post_ir}");
        for &input in b_inputs {
            assert_ne!(input, original_v, "phi input should be renamed\n{post_ir}");
        }
        assert_ne!(b_inputs[0], b_inputs[1], "phi inputs should be distinct\n{post_ir}");
    }

    #[test]
    fn test_multiple_phis_at_join() {
        //     A
        //    / \
        //   B   C
        //    \ /
        //     D
        //
        // x defined in A and B, y defined in A and C.
        let mut program = parse_without_ssa(
            r#"
            fn init:
                a -> x y {
                    x = const 1
                    y = const 2
                    cond = const 0
                    => cond ? @b : @c
                }
                b x y -> x y {
                    x = const 3
                    => @d
                }
                c x y -> x y {
                    y = const 4
                    => @d
                }
                d x y {
                    stop
                }
            "#,
        );

        let d = BasicBlockId::new(3);
        let original_x = program.block(d).inputs()[0];
        let original_y = program.block(d).inputs()[1];

        transform_and_legalize(&mut program);
        let post_ir = display_program(&program);

        let d_inputs = program.block(d).inputs();
        assert_eq!(d_inputs.len(), 4, "D should have 2 original inputs + 2 phis\n{post_ir}");
        for &input in d_inputs {
            assert_ne!(input, original_x, "x should be renamed\n{post_ir}");
            assert_ne!(input, original_y, "y should be renamed\n{post_ir}");
        }
    }

    #[test]
    fn test_critical_edge_and_switch_phi() {
        //     A
        //    / \
        //   B   C
        //  / \  |
        // E   D-+
        //
        // v defined in A and B. B uses a switch, so B→D is a critical edge.
        let mut program = parse_without_ssa(
            r#"
            fn init:
                a -> v {
                    v = const 1
                    cond = const 0
                    => cond ? @b : @c
                }
                b v -> v {
                    v = const 2
                    sel = const 0
                    switch sel {
                        0 => @d
                        default => @e
                    }
                }
                c v -> v {
                    => @d
                }
                d v {
                    stop
                }
                e v {
                    stop
                }
            "#,
        );

        let d = BasicBlockId::new(3);
        let original_block_count = program.basic_blocks.len();
        let original_v = program.block(d).inputs()[0];

        transform_and_legalize(&mut program);
        let post_ir = display_program(&program);

        assert!(
            program.basic_blocks.len() > original_block_count,
            "critical edge splitting should insert forwarding blocks\n{post_ir}"
        );

        let d_inputs = program.block(d).inputs();
        assert_eq!(d_inputs.len(), 2, "D should have original input + phi\n{post_ir}");
        for &input in d_inputs {
            assert_ne!(input, original_v, "phi input should be renamed\n{post_ir}");
        }
        assert_ne!(d_inputs[0], d_inputs[1], "phi inputs should be distinct\n{post_ir}");
    }

    #[test]
    fn test_icall_and_multi_function() {
        //  init:        helper:
        //     A           E
        //    / \          |
        //   B   C         F
        //    \ /
        //     D (calls helper with v)
        //
        // v defined in A and B. D calls helper passing v.
        let mut program = parse_without_ssa(
            r#"
            fn init:
                a -> v {
                    v = const 1
                    cond = const 0
                    => cond ? @b : @c
                }
                b v -> v {
                    v = const 2
                    => @d
                }
                c v -> v {
                    => @d
                }
                d v {
                    result = icall @helper v
                    stop
                }
            fn helper:
                e x -> x {
                    => @f
                }
                f x -> x {
                    iret
                }
            "#,
        );

        let init_entry = program.functions[program.init_entry].entry();
        let helper_id = program.functions.iter_idx().find(|&id| id != program.init_entry).unwrap();
        let helper_entry = program.functions[helper_id].entry();

        transform_and_legalize(&mut program);
        let post_ir = display_program(&program);

        let init_inputs = program.block(init_entry).inputs();
        let helper_inputs = program.block(helper_entry).inputs();
        assert_eq!(helper_inputs.len(), 1, "helper entry should still have 1 input\n{post_ir}");
        for &init_local in init_inputs {
            for &helper_local in helper_inputs {
                assert_ne!(
                    init_local, helper_local,
                    "locals across functions should be renamed independently\n{post_ir}"
                );
            }
        }
    }
}
