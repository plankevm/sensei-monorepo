use sir_data::{BasicBlockId, EthIRProgram, IndexVec};

pub fn compute_predecessors(
    program: &EthIRProgram,
    predecessors: &mut IndexVec<BasicBlockId, Vec<BasicBlockId>>,
) {
    for pred in predecessors.iter_mut() {
        pred.clear();
    }
    predecessors.resize(program.basic_blocks.len(), Vec::new());

    for block in program.blocks() {
        for successor in block.successors() {
            predecessors[successor].push(block.id());
        }
    }
}
