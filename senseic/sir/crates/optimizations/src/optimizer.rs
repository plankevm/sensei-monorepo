use sir_analyses::DefUse;
use sir_data::{BasicBlockId, DenseIndexSet, EthIRProgram};

use crate::{
    constant_propagation::SCCPAnalysis, copy_propagation::CopyPropagation,
    defragmenter::Defragmenter, unused_operation_elimination::UnusedOperationElimination,
};

pub struct Optimizer {
    src: EthIRProgram,
    dst: Option<EthIRProgram>,

    uses: Option<DefUse>,
    live_blocks: Option<DenseIndexSet<BasicBlockId>>,

    sccp: Option<SCCPAnalysis>,
    copy_prop: Option<CopyPropagation>,
    unused_elim: Option<UnusedOperationElimination>,
    defragmenter: Option<Defragmenter>,
}

impl Optimizer {
    pub fn new(program: EthIRProgram) -> Self {
        Self {
            src: program,
            dst: None,
            uses: None,
            live_blocks: None,
            sccp: None,
            copy_prop: None,
            unused_elim: None,
            defragmenter: None,
        }
    }

    pub fn run_passes(&mut self, passes: &str) {
        for c in passes.chars() {
            match c {
                's' => self.run_sccp(),
                'c' => self.run_copy_prop(),
                'u' => self.run_unused_elim(),
                'd' => self.run_defragment(),
                _ => eprintln!("warning: unknown optimization pass '{}'", c),
            }
        }
    }

    pub fn finish(self) -> EthIRProgram {
        self.src
    }

    fn run_sccp(&mut self) {
        let sccp = self.sccp.get_or_insert_with(|| SCCPAnalysis::new(&self.src));
        let uses = self.uses.get_or_insert_with(DefUse::new);
        sccp.analysis(&self.src, uses);
        sccp.apply(&mut self.src);
        self.live_blocks = Some(sccp.reachable.clone());
    }

    fn run_copy_prop(&mut self) {
        let copy_prop = self.copy_prop.get_or_insert_with(CopyPropagation::new);
        copy_prop.run(&mut self.src);
    }

    fn run_unused_elim(&mut self) {
        let unused_elim = self.unused_elim.get_or_insert_with(UnusedOperationElimination::new);
        let uses = self.uses.get_or_insert_with(DefUse::new);
        unused_elim.run(&mut self.src, uses);
    }

    fn run_defragment(&mut self) {
        let dst = self.dst.get_or_insert_with(EthIRProgram::default);
        let defragmenter = self.defragmenter.get_or_insert_with(Defragmenter::new);
        defragmenter.run(&self.src, dst, self.live_blocks.as_ref());
        std::mem::swap(&mut self.src, dst);
    }
}
