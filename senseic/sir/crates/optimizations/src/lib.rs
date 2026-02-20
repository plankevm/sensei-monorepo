mod constant_propagation;
mod copy_propagation;
mod global_prune_pass;
mod unused_operation_elimination;

use sir_data::EthIRProgram;

pub use global_prune_pass::PrunerState;

pub enum Optimization {
    CopyPropagation,
    ConstantPropagation,
    UnusedOperationElimination,
}

impl Optimization {
    pub fn apply(&self, ir: &mut EthIRProgram) {
        match self {
            Optimization::CopyPropagation => copy_propagation::run(ir),
            Optimization::ConstantPropagation => constant_propagation::run(ir),
            Optimization::UnusedOperationElimination => unused_operation_elimination::run(ir),
        }
    }
}
