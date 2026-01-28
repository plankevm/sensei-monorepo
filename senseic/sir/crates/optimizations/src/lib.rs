mod copy_propagation;

use sir_data::EthIRProgram;

pub enum Optimization {
    CopyPropagation,
}

impl Optimization {
    pub fn apply(&self, ir: &mut EthIRProgram) {
        match self {
            Optimization::CopyPropagation => copy_propagation::run(ir),
        }
    }
}
