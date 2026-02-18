use crate::{
    BasicBlockId, CasesIter, Control, EthIRProgram, FunctionId, LocalId, Operation, OperationIdx,
    OutgoingConnectionsIter,
};

#[derive(Clone, Copy)]
pub struct BlockView<'ir> {
    id: BasicBlockId,
    ir: &'ir EthIRProgram,
}

impl<'ir> BlockView<'ir> {
    pub fn id(&self) -> BasicBlockId {
        self.id
    }

    pub fn inputs(&self) -> &'ir [LocalId] {
        &self.ir.locals[self.ir.basic_blocks[self.id].inputs]
    }

    pub fn outputs(&self) -> &'ir [LocalId] {
        &self.ir.locals[self.ir.basic_blocks[self.id].outputs]
    }

    pub fn operations(&self) -> impl Iterator<Item = OperationView<'ir>> {
        let ir = self.ir;
        self.ir.basic_blocks[self.id].operations.iter().map(move |id| OperationView { id, ir })
    }

    pub fn control(&self) -> ControlView<'ir> {
        ControlView::from_control(&self.ir.basic_blocks[self.id].control, self.ir)
    }

    pub fn successors(&self) -> OutgoingConnectionsIter<'ir> {
        self.ir.basic_blocks[self.id].control.iter_outgoing(self.ir)
    }
}

#[derive(Clone, Copy)]
pub struct OperationView<'ir> {
    id: OperationIdx,
    ir: &'ir EthIRProgram,
}

impl<'ir> OperationView<'ir> {
    pub fn id(&self) -> OperationIdx {
        self.id
    }

    pub fn inputs(&self) -> &'ir [LocalId] {
        self.ir.operations[self.id].inputs(self.ir)
    }

    pub fn outputs(&self) -> &'ir [LocalId] {
        self.ir.operations[self.id].outputs(self.ir)
    }

    pub fn op(&self) -> Operation {
        self.ir.operations[self.id]
    }
}

pub enum ControlView<'ir> {
    LastOpTerminates,
    InternalReturn,
    ContinuesTo(BasicBlockId),
    Branches { condition: LocalId, non_zero_target: BasicBlockId, zero_target: BasicBlockId },
    Switch(SwitchView<'ir>),
}

impl<'ir> ControlView<'ir> {
    fn from_control(control: &Control, ir: &'ir EthIRProgram) -> Self {
        match control {
            Control::LastOpTerminates => Self::LastOpTerminates,
            Control::InternalReturn => Self::InternalReturn,
            Control::ContinuesTo(bb) => Self::ContinuesTo(*bb),
            Control::Branches(branch) => Self::Branches {
                condition: branch.condition,
                non_zero_target: branch.non_zero_target,
                zero_target: branch.zero_target,
            },
            Control::Switch(switch) => Self::Switch(SwitchView {
                condition: switch.condition,
                fallback: switch.fallback,
                cases: &ir.cases[switch.cases],
                ir,
            }),
        }
    }
}

pub struct SwitchView<'ir> {
    condition: LocalId,
    fallback: Option<BasicBlockId>,
    cases: &'ir crate::Cases,
    ir: &'ir EthIRProgram,
}

impl<'ir> SwitchView<'ir> {
    pub fn condition(&self) -> LocalId {
        self.condition
    }

    pub fn fallback(&self) -> Option<BlockView<'ir>> {
        self.fallback.map(|id| BlockView { id, ir: self.ir })
    }

    pub fn cases(&self) -> CasesIter<'ir> {
        self.cases.iter(self.ir)
    }
}

#[derive(Clone, Copy)]
pub struct FunctionView<'ir> {
    id: FunctionId,
    ir: &'ir EthIRProgram,
}

impl<'ir> FunctionView<'ir> {
    pub fn id(&self) -> FunctionId {
        self.id
    }

    pub fn entry(&self) -> BlockView<'ir> {
        BlockView { id: self.ir.functions[self.id].entry(), ir: self.ir }
    }

    pub fn num_inputs(&self) -> u32 {
        self.ir.functions[self.id].get_inputs(&self.ir.basic_blocks)
    }

    pub fn num_outputs(&self) -> u32 {
        self.ir.functions[self.id].get_outputs()
    }
}

impl EthIRProgram {
    pub fn block(&self, id: BasicBlockId) -> BlockView<'_> {
        BlockView { id, ir: self }
    }

    pub fn function(&self, id: FunctionId) -> FunctionView<'_> {
        FunctionView { id, ir: self }
    }

    pub fn blocks(&self) -> impl Iterator<Item = BlockView<'_>> {
        self.basic_blocks.iter_idx().map(move |id| BlockView { id, ir: self })
    }

    pub fn functions_iter(&self) -> impl Iterator<Item = FunctionView<'_>> {
        self.functions.iter_idx().map(move |id| FunctionView { id, ir: self })
    }
}
