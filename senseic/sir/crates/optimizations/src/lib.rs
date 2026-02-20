mod constant_propagation;
mod copy_propagation;
mod global_prune_pass;
mod unused_operation_elimination;

use sir_data::{BasicBlockId, DenseIndexSet, EthIRProgram};

pub use global_prune_pass::PrunerState;

pub enum Optimization {
    CopyPropagation,
    ConstantPropagation,
    UnusedOperationElimination,
    GlobalPruning,
}

pub struct OptimizationOptions<'a> {
    pub sccp_reachable: Option<&'a DenseIndexSet<BasicBlockId>>,
    pub new_ir: Option<&'a mut EthIRProgram>,
    pub pruner_state: Option<&'a mut PrunerState>,
}

impl Optimization {
    pub fn apply(&self, ir: &mut EthIRProgram, options: Option<OptimizationOptions<'_>>) {
        match self {
            Optimization::CopyPropagation => copy_propagation::run(ir),
            Optimization::ConstantPropagation => constant_propagation::run(ir),
            Optimization::UnusedOperationElimination => unused_operation_elimination::run(ir),
            Optimization::GlobalPruning => {
                let (sccp, new_ir, pruner_state) = match options {
                    Some(opts) => (opts.sccp_reachable, opts.new_ir, opts.pruner_state),
                    None => (None, None, None),
                };

                let mut default_state;
                let state = match pruner_state {
                    Some(s) => s,
                    None => {
                        default_state = PrunerState::new();
                        &mut default_state
                    }
                };

                if let Some(new) = new_ir {
                    state.run(ir, new, sccp);
                    std::mem::swap(ir, new);
                } else {
                    panic!("GlobalPruning requires new_ir in options");
                }
            }
        }
    }
}
