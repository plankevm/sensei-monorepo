use sensei_core::{newtype_index, span::IncIterable};
use sir_data::{BasicBlockId, EthIRProgram, IndexVec, index_vec};

newtype_index! {
    pub struct InOutGroupId;
}

#[derive(Debug)]
pub struct ControlFlowGraphInOutBundling {
    out_group: IndexVec<BasicBlockId, Option<InOutGroupId>>,
    in_group: IndexVec<BasicBlockId, Option<InOutGroupId>>,
    next_group_id: InOutGroupId,
}

impl ControlFlowGraphInOutBundling {
    pub fn analyze(ir: &EthIRProgram) -> Self {
        let mut out_group = index_vec![None; ir.basic_blocks.len()];
        let mut in_group = index_vec![None; ir.basic_blocks.len()];
        let mut next_group_id = InOutGroupId::ZERO;

        for block in ir.blocks() {
            let existing_group_id = block.successors().find_map(|to| in_group[to]);
            let group_id = existing_group_id.unwrap_or_else(|| next_group_id.get_and_inc());
            out_group[block.id] = Some(group_id);
            for to in block.successors() {
                in_group[to] = Some(group_id);
            }
        }

        Self { out_group, in_group, next_group_id }
    }

    pub fn get_out_group(&self, bb_id: BasicBlockId) -> Option<InOutGroupId> {
        self.out_group[bb_id]
    }

    pub fn get_in_group(&self, bb_id: BasicBlockId) -> Option<InOutGroupId> {
        self.in_group[bb_id]
    }

    pub fn next_group_id(&self) -> InOutGroupId {
        self.next_group_id
    }
}
