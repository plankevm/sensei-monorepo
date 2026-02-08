use sir_data::{BasicBlockId, BasicBlockIdMarker, EthIRProgram, IndexVec, index_vec};

pub fn compute_predecessors(
    program: &EthIRProgram,
) -> IndexVec<BasicBlockIdMarker, Vec<BasicBlockId>> {
    let mut predecessors = index_vec![Vec::new(); program.basic_blocks.len()];

    for (id, bb) in program.basic_blocks.enumerate_idx() {
        for successor in bb.control.iter_outgoing(program) {
            predecessors[successor].push(id);
        }
    }

    predecessors
}
