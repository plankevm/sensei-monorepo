mod basic_block_ownership;
mod cfg_in_out_bundling;
mod def_use;
mod dominators;
mod legalizer;
mod predecessors;

pub use basic_block_ownership::BasicBlockOwnershipAndReachability;
pub use cfg_in_out_bundling::{ControlFlowGraphInOutBundling, InOutGroupId};
pub use def_use::{DefUse, UseKind, UseLocation, compute_def_use};
pub use dominators::{compute_dominance_frontiers, compute_dominators};
pub use legalizer::legalize;
pub use predecessors::compute_predecessors;
