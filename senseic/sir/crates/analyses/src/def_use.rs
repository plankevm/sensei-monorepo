use sir_data::{BasicBlockId, ControlView, EthIRProgram, Idx, IndexVec, LocalId, OperationIdx};

#[derive(Clone)]
pub struct UseLocation {
    pub block_id: BasicBlockId,
    pub kind: UseKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseKind {
    Operation(OperationIdx),
    Control,
    BlockOutput,
}

impl std::fmt::Display for UseKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UseKind::Operation(op) => write!(f, "operation {op}"),
            UseKind::Control => write!(f, "control"),
            UseKind::BlockOutput => write!(f, "block output"),
        }
    }
}

pub type DefUse = IndexVec<LocalId, Vec<UseLocation>>;

pub fn compute_def_use(program: &EthIRProgram, uses: &mut DefUse) {
    let num_locals = program.next_free_local_id.idx();
    for vec in uses.iter_mut() {
        vec.clear();
    }
    uses.resize_with(num_locals, Vec::new);

    for block in program.blocks() {
        for op in block.operations() {
            for &input in op.inputs() {
                uses[input]
                    .push(UseLocation { block_id: block.id(), kind: UseKind::Operation(op.id()) });
            }
        }

        match block.control() {
            ControlView::Branches { condition, .. } => {
                uses[condition].push(UseLocation { block_id: block.id(), kind: UseKind::Control });
            }
            ControlView::Switch(switch) => {
                uses[switch.condition()]
                    .push(UseLocation { block_id: block.id(), kind: UseKind::Control });
            }
            _ => {}
        }

        for &local in block.outputs() {
            uses[local].push(UseLocation { block_id: block.id(), kind: UseKind::BlockOutput });
        }
    }
}
