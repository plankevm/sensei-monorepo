mod constant_propagation;
mod copy_propagation;
mod defragmenter;
mod optimizer;
mod unused_operation_elimination;

pub use defragmenter::Defragmenter;
pub use optimizer::Optimizer;
