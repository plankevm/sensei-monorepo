use serde::{Deserialize, Serialize};

pub const BLOCKS_FILE_NAME: &str = "blocks.csv";
pub const CANONICAL_BLOCKS_FILE_NAME: &str = "canonical-blocks.sqlite3";
pub const BLOCKS_HEADER: [&str; 3] = ["file", "block_id", "canonical_hash"];

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockRow {
    pub file: String,
    pub block_id: u32,
    pub canonical_hash: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CanonicalBlockRow {
    pub canonical_hash: String,
    pub canonical_graph: String,
    pub best_schedule: String,
    pub best_gas_cost: u64,
    pub manually_optimized: bool,
}
