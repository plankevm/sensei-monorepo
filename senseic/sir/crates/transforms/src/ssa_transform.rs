use sir_analyses::{compute_dominance_frontiers, compute_dominators, compute_predecessors};
use sir_data::{BasicBlockId, DenseIndexSet, EthIRProgram, Idx, IndexVec, LocalId, index_vec};

struct SsaTransform {
    def_sites: IndexVec<LocalId, DenseIndexSet<BasicBlockId>>,
    dominators: IndexVec<BasicBlockId, Option<BasicBlockId>>,
    dominator_tree: IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    phi_blocks: IndexVec<LocalId, DenseIndexSet<BasicBlockId>>,
    predecessors: IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    dominance_frontiers: IndexVec<BasicBlockId, DenseIndexSet<BasicBlockId>>,
}

impl SsaTransform {
    fn new(program: &EthIRProgram) -> Self {
        let dominators = compute_dominators(program);
        let mut predecessors = IndexVec::new();
        compute_predecessors(program, &mut predecessors);
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
            phi_blocks: index_vec![DenseIndexSet::new(); program.next_free_local_id.idx()],
        }
    }

    fn run(&mut self, program: &mut EthIRProgram) {
        self.compute_phi_locations();
        self.rename(program);
        self.cleanup_trivial_phis(program);
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

    fn compute_phi_locations(&mut self) {
        let mut worklist = Vec::new();
        for (local, def_blocks) in self.def_sites.enumerate_idx() {
            if def_blocks.len() <= 1 {
                continue;
            }
            for bb in def_blocks.iter() {
                worklist.push(bb);
            }
            while let Some(bb) = worklist.pop() {
                for frontier_block in self.dominance_frontiers[bb].iter() {
                    if !self.phi_blocks[local].contains(frontier_block) {
                        self.phi_blocks[local].add(frontier_block);
                        worklist.push(frontier_block);
                    }
                }
            }
        }
    }

    fn rename(&mut self, _program: &mut EthIRProgram) {
        todo!()
    }

    fn cleanup_trivial_phis(&mut self, _program: &mut EthIRProgram) {
        todo!()
    }
}

pub fn ssa_transform(program: &mut EthIRProgram) {
    SsaTransform::new(program).run(program);
}
