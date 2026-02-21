use crate::{
    BasicBlockId, CasesId, CasesIter, Control, EthIRProgram, FunctionId, LargeConstId, LocalId,
    Operation, OperationIdx, OutgoingConnectionsIter,
};
use std::fmt;

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

impl fmt::Display for BlockView<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "    @{}", self.id)?;

        let inputs = self.inputs();
        if !inputs.is_empty() {
            for local in inputs {
                write!(f, " ${local}")?;
            }
        }

        let outputs = self.outputs();
        if !outputs.is_empty() {
            write!(f, " ->")?;
            for local in outputs {
                write!(f, " ${local}")?;
            }
        }

        writeln!(f, " {{")?;

        for op_view in self.operations() {
            writeln!(f, "        {op_view}")?;
        }

        match self.control() {
            ControlView::LastOpTerminates => {}
            control => {
                write!(f, "        {control}")?;
                writeln!(f)?;
            }
        }

        writeln!(f, "    }}")
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

impl fmt::Display for OperationView<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ir.operations[self.id].op_fmt(f, self.ir)
    }
}

#[derive(Clone, Copy)]
pub enum ControlView<'ir> {
    LastOpTerminates,
    InternalReturn,
    ContinuesTo(BasicBlockId),
    Branches { condition: LocalId, non_zero_target: BasicBlockId, zero_target: BasicBlockId },
    Switch(SwitchView<'ir>),
}

impl fmt::Display for ControlView<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LastOpTerminates => Ok(()),
            Self::InternalReturn => write!(f, "iret"),
            Self::ContinuesTo(bb) => write!(f, "=> @{bb}"),
            Self::Branches { condition, non_zero_target, zero_target } => {
                write!(f, "=> ${condition} ? @{non_zero_target} : @{zero_target}",)
            }
            Self::Switch(switch) => {
                writeln!(f, "switch ${} {{", switch.condition())?;
                for (value, target) in switch.cases() {
                    writeln!(f, "            {value:x} => @{target},")?;
                }
                if let Some(fallback) = switch.fallback() {
                    writeln!(f, "            else => @{fallback}\n        }}")
                } else {
                    writeln!(f, "        }}")
                }
            }
        }
    }
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
                cases_id: switch.cases,
                cases: &ir.cases[switch.cases],
                ir,
            }),
        }
    }
}

#[derive(Clone, Copy)]
pub struct SwitchView<'ir> {
    condition: LocalId,
    fallback: Option<BasicBlockId>,
    cases_id: CasesId,
    cases: &'ir crate::Cases,
    ir: &'ir EthIRProgram,
}

impl<'ir> SwitchView<'ir> {
    pub fn condition(&self) -> LocalId {
        self.condition
    }

    pub fn fallback(&self) -> Option<BasicBlockId> {
        self.fallback
    }

    pub fn cases(&self) -> CasesIter<'ir> {
        self.cases.iter(self.ir)
    }

    pub fn cases_id(&self) -> CasesId {
        self.cases_id
    }

    pub fn value_ids(&self) -> impl Iterator<Item = LargeConstId> {
        (0..self.cases.cases_count).map(move |i| self.cases.values_start_id + i)
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

    pub fn operations(&self) -> impl Iterator<Item = OperationView<'_>> {
        self.operations.iter_idx().map(move |id| OperationView { id, ir: self })
    }
}
