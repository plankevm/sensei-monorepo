use sir_data::{BasicBlockId, EthIRProgram, Idx, IndexVec, LocalId, OperationIdx, index_vec};

#[derive(Clone)]
pub struct UseLocation {
    pub block_id: BasicBlockId,
    pub op_id: OperationIdx,
}

pub type DefUse = IndexVec<LocalId, Vec<UseLocation>>;

pub fn compute_def_use(program: &EthIRProgram) -> DefUse {
    let num_locals = program.next_free_local_id.idx();
    let mut uses: DefUse = index_vec![Vec::new(); num_locals];

    for (bb_id, bb) in program.basic_blocks.enumerate_idx() {
        for (op_id, op) in program.operations[bb.operations].iter().enumerate() {
            let global_index = OperationIdx::new(bb.operations.start.get() + op_id as u32);
            for &input in op.inputs(program) {
                uses[input].push(UseLocation { block_id: bb_id, op_id: global_index });
            }
        }
    }
    uses
}
