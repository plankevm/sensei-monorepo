use sir_data::{BasicBlockId, EthIRProgram, IndexVec, index_vec};

pub fn compute_predecessors(program: &EthIRProgram) -> IndexVec<BasicBlockId, Vec<BasicBlockId>> {
    let mut predecessors = index_vec![Vec::new(); program.basic_blocks.len()];

    for block in program.blocks() {
        for successor in block.successors() {
            predecessors[successor].push(block.id);
        }
    }

    predecessors
}
