use sir_data::{
    BasicBlockId, Control, EthIRProgram, Idx, IndexVec, LocalId, OperationIdx, index_vec,
};

#[derive(Clone)]
pub struct UseLocation {
    pub block_id: BasicBlockId,
    pub kind: UseKind,
}

#[derive(Clone, Copy)]
pub enum UseKind {
    Operation(OperationIdx),
    Control,
    BlockOutput,
}

pub type DefUse = IndexVec<LocalId, Vec<UseLocation>>;

pub fn compute_def_use(program: &EthIRProgram) -> DefUse {
    let num_locals = program.next_free_local_id.idx();
    let mut uses: DefUse = index_vec![Vec::new(); num_locals];

    for (bb_id, bb) in program.basic_blocks.enumerate_idx() {
        for op_idx in bb.operations.iter() {
            let op = &program.operations[op_idx];
            for &input in op.inputs(program) {
                uses[input].push(UseLocation { block_id: bb_id, kind: UseKind::Operation(op_idx) });
            }
        }

        match &bb.control {
            Control::Branches(branch) => {
                uses[branch.condition]
                    .push(UseLocation { block_id: bb_id, kind: UseKind::Control });
            }
            Control::Switch(switch) => {
                uses[switch.condition]
                    .push(UseLocation { block_id: bb_id, kind: UseKind::Control });
            }
            _ => {}
        }

        for &local in &program.locals[bb.outputs] {
            uses[local].push(UseLocation { block_id: bb_id, kind: UseKind::BlockOutput });
        }
    }
    uses
}
