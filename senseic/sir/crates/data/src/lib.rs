pub mod builder;
pub mod index;
pub mod operation;
pub mod view;

pub use crate::{index::*, operation::Operation, view::*};
use alloy_primitives::U256;
use sensei_core::list_of_lists::ListOfLists;
use std::fmt;

/// Implemented in a data oriented way. Instead of each basic block and function holding its own
/// vector of items they're all stored contiguously in the top level program
#[derive(Debug, Clone)]
pub struct EthIRProgram {
    // Entry Points
    pub init_entry: FunctionId,
    pub main_entry: Option<FunctionId>,
    // IR Statements
    pub functions: IndexVec<FunctionId, Function>,
    pub basic_blocks: IndexVec<BasicBlockId, BasicBlock>,
    pub operations: IndexVec<OperationIdx, Operation>,
    pub data_segments: ListOfLists<DataId, u8>,
    // IR Data
    pub locals: IndexVec<LocalIdx, LocalId>,
    pub large_consts: IndexVec<LargeConstId, U256>,
    pub cases: IndexVec<CasesId, Cases>,
    pub cases_bb_ids: IndexVec<CasesBasicBlocksIdx, BasicBlockId>,
    // Codegeneration helpers
    pub next_free_local_id: LocalId,
    pub next_static_alloc_id: StaticAllocId,
}

impl Default for EthIRProgram {
    fn default() -> Self {
        Self {
            init_entry: FunctionId::ZERO,
            main_entry: Default::default(),
            functions: Default::default(),
            basic_blocks: Default::default(),
            operations: Default::default(),
            data_segments: Default::default(),
            locals: Default::default(),
            large_consts: Default::default(),
            cases: Default::default(),
            cases_bb_ids: Default::default(),
            next_free_local_id: LocalId::ZERO,
            next_static_alloc_id: StaticAllocId::ZERO,
        }
    }
}

impl EthIRProgram {
    /// Clears all data and resets values to their defaults
    pub fn clear(&mut self) {
        self.init_entry = FunctionId::ZERO;
        self.main_entry = None;
        self.functions.clear();
        self.basic_blocks.clear();
        self.operations.clear();
        self.data_segments.clear();
        self.locals.clear();
        self.large_consts.clear();
        self.cases.clear();
        self.cases_bb_ids.clear();
        self.next_free_local_id = LocalId::ZERO;
        self.next_static_alloc_id = StaticAllocId::ZERO;
    }
}
/// Simple display of IR program - shows all elements independently without grouping
pub fn display_program(ir: &EthIRProgram) -> String {
    use fmt::Write;
    let mut output = String::new();

    if !ir.functions.is_empty() {
        writeln!(&mut output, "Functions:").unwrap();
    }

    // Display functions
    for func in ir.functions_iter() {
        writeln!(
            &mut output,
            "    fn @{} -> entry @{}  (outputs: {})",
            func.id(),
            func.entry().id(),
            func.num_outputs()
        )
        .unwrap();
    }

    if !ir.functions.is_empty() {
        writeln!(&mut output).unwrap();
    }

    writeln!(&mut output, "Basic Blocks:").unwrap();

    // Display all basic blocks
    for block in ir.blocks() {
        writeln!(&mut output, "{block}").unwrap();
    }

    // Display data segments
    if !ir.data_segments.is_empty() {
        writeln!(&mut output).unwrap();

        for (segment_id, data) in ir.data_segments.enumerate_idx() {
            write!(&mut output, "data .{segment_id} ").unwrap();

            write!(&mut output, "0x").unwrap();
            for &byte in data {
                write!(&mut output, "{:02x}", byte).unwrap();
            }
            writeln!(&mut output).unwrap();
        }
    }

    output
}

impl fmt::Display for EthIRProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", display_program(self))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Function {
    entry_bb_id: BasicBlockId,
    outputs: u32,
}

impl Function {
    pub fn new(entry_bb_id: BasicBlockId, outputs: u32) -> Self {
        Self { entry_bb_id, outputs }
    }

    pub fn entry(&self) -> BasicBlockId {
        self.entry_bb_id
    }

    pub fn get_inputs(&self, basic_blocks: &IndexVec<BasicBlockId, BasicBlock>) -> u32 {
        let inputs = basic_blocks[self.entry()].inputs;
        inputs.end - inputs.start
    }

    pub fn get_outputs(&self) -> u32 {
        self.outputs
    }
}

#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Input locals.
    pub inputs: Span<LocalIdx>,
    pub outputs: Span<LocalIdx>,
    pub operations: Span<OperationIdx>,
    pub control: Control,
}

impl BasicBlock {
    pub fn implied_fn_out(&self) -> Option<u32> {
        match self.control {
            Control::InternalReturn => Some(self.outputs.end - self.outputs.start),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Branch {
    pub condition: LocalId,
    pub non_zero_target: BasicBlockId,
    pub zero_target: BasicBlockId,
}

// Kept small to ensure that `Control` is no larger because of it. This is because I expect `Switch`
// to not be that common so I don't want to optimize for it.
#[derive(Debug, Clone)]
pub struct Switch {
    pub condition: LocalId,
    pub fallback: Option<BasicBlockId>,
    pub cases: CasesId,
}

/// Values stored at `values_start_id..values_start_id + cases_count`, target basic block IDs stored
/// at `targets_start_id..targets_start_id + cases_count`.
#[derive(Debug, Clone, Copy)]
pub struct Cases {
    pub values_start_id: LargeConstId,
    pub targets_start_id: CasesBasicBlocksIdx,
    pub cases_count: u32,
}

impl Cases {
    pub fn get_values<'ir>(&self, ir: &'ir EthIRProgram) -> RelSlice<'ir, LargeConstId, U256> {
        ir.large_consts.rel_slice(self.values_start_id..self.values_start_id + self.cases_count)
    }

    pub fn get_bb_ids<'ir>(
        &self,
        ir: &'ir EthIRProgram,
    ) -> RelSlice<'ir, CasesBasicBlocksIdx, BasicBlockId> {
        ir.cases_bb_ids.rel_slice(self.targets_start_id..self.targets_start_id + self.cases_count)
    }

    pub fn iter<'ir>(&self, ir: &'ir EthIRProgram) -> CasesIter<'ir> {
        CasesIter::new(self.get_values(ir).as_raw_slice(), self.get_bb_ids(ir).as_raw_slice())
    }
}

#[derive(Debug, Clone)]
pub struct CasesIter<'ir> {
    values: &'ir [U256],
    targets: &'ir [BasicBlockId],
}

impl<'ir> CasesIter<'ir> {
    fn new(values: &'ir [U256], targets: &'ir [BasicBlockId]) -> Self {
        Self { values, targets }
    }
}

impl<'ir> Iterator for CasesIter<'ir> {
    type Item = (U256, BasicBlockId);

    fn next(&mut self) -> Option<Self::Item> {
        let (value, rest_values) = self.values.split_first()?;
        let (target, rest_targets) = self.targets.split_first()?;
        self.values = rest_values;
        self.targets = rest_targets;
        Some((*value, *target))
    }
}

#[derive(Debug, Clone)]
pub enum Control {
    LastOpTerminates,
    InternalReturn,
    ContinuesTo(BasicBlockId),
    Branches(Branch),
    Switch(Switch),
}

impl Control {
    pub fn iter_outgoing<'ir>(&'ir self, ir: &'ir EthIRProgram) -> OutgoingConnectionsIter<'ir> {
        use core::slice::from_ref;
        match self {
            Control::InternalReturn | Control::LastOpTerminates => OutgoingConnectionsIter::empty(),
            Control::ContinuesTo(bb_id) => OutgoingConnectionsIter::from_list(from_ref(bb_id)),
            Control::Branches(branch) => OutgoingConnectionsIter::new(
                from_ref(&branch.zero_target),
                Some(branch.non_zero_target),
            ),
            Control::Switch(switch) => OutgoingConnectionsIter::new(
                ir.cases[switch.cases].get_bb_ids(ir).as_raw_slice(),
                switch.fallback,
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub struct OutgoingConnectionsIter<'ir> {
    extra_connection: Option<BasicBlockId>,
    connections_list: &'ir [BasicBlockId],
}

impl<'ir> OutgoingConnectionsIter<'ir> {
    fn empty() -> Self {
        Self { extra_connection: None, connections_list: &[] }
    }

    fn from_list(connections_list: &'ir [BasicBlockId]) -> Self {
        Self::new(connections_list, None)
    }

    fn new(connections_list: &'ir [BasicBlockId], extra_connection: Option<BasicBlockId>) -> Self {
        Self { extra_connection, connections_list }
    }
}

impl<'ir> Iterator for OutgoingConnectionsIter<'ir> {
    type Item = BasicBlockId;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(bb_id) = self.connections_list.split_off_first() {
            return Some(*bb_id);
        }

        self.extra_connection.take()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_ir_display(program: &EthIRProgram, expected: &str) {
        let actual = display_program(program);
        sir_test_utils::assert_trim_strings_eq_with_diff(&actual, expected, "IR display");
    }

    #[test]
    fn control_memory_layout() {
        assert_eq!(std::mem::size_of::<Control>(), 16, "changed desired control size");
        assert_eq!(std::mem::align_of::<Control>(), 4, "changed desired control alignment");
    }

    #[test]
    fn test_display() {
        use crate::{builder::EthIRBuilder, operation::*};

        // Create a simple program using the builder
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let local0 = func.new_local();
        let local1 = func.new_local();
        let local2 = func.new_local();

        let mut bb = func.begin_basic_block();
        bb.set_inputs(&[local0, local1]);
        bb.add_operation(Operation::Add(InlineOperands { ins: [local0, local1], outs: [local2] }));
        bb.add_operation(Operation::Stop(()));
        bb.set_outputs(&[local2]);
        let bb_id = bb.finish(Control::InternalReturn).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 1)

Basic Blocks:
    @0 $0 $1 -> $2 {
        $2 = add $0 $1
        stop
        iret
    }

"#;

        assert_ir_display(&program, expected);
    }

    #[test]
    fn test_display_with_unreachable_blocks() {
        use crate::{builder::EthIRBuilder, operation::*};

        // Create a program with unreachable blocks
        let mut builder = EthIRBuilder::new();

        // Function 0: one block with stop
        let mut func0 = builder.begin_function();
        let mut bb0 = func0.begin_basic_block();
        bb0.add_operation(Operation::Stop(()));
        let bb0_id = bb0.finish(Control::LastOpTerminates).unwrap();
        let func0_id = func0.finish(bb0_id);

        // Unreachable block 1
        let mut orphan1 = builder.begin_function();
        let mut bb1 = orphan1.begin_basic_block();
        bb1.add_operation(Operation::Invalid(()));
        bb1.finish(Control::LastOpTerminates).unwrap();

        // Function 1: one block with setcopy
        let mut func1 = builder.begin_function();
        let local0 = func1.new_local();
        let local1 = func1.new_local();
        let mut bb2 = func1.begin_basic_block();
        bb2.set_inputs(&[local0]);
        bb2.add_operation(Operation::SetCopy(InlineOperands { ins: [local0], outs: [local1] }));
        bb2.set_outputs(&[local1]);
        let bb2_id = bb2.finish(Control::InternalReturn).unwrap();
        let _func1_id = func1.finish(bb2_id);

        // Unreachable block 2
        let mut orphan2 = builder.begin_function();
        let mut bb3 = orphan2.begin_basic_block();
        bb3.add_operation(Operation::Stop(()));
        bb3.finish(Control::LastOpTerminates).unwrap();

        let program = builder.build(func0_id, None);

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @2  (outputs: 1)

Basic Blocks:
    @0 {
        stop
    }

    @1 {
        invalid
    }

    @2 $0 -> $1 {
        $1 = copy $0
        iret
    }

    @3 {
        stop
    }

"#;

        assert_ir_display(&program, expected);
    }

    #[test]
    fn test_display_with_data() {
        use crate::{builder::EthIRBuilder, operation::*};

        // Create a program with data segments and large constants
        let mut builder = EthIRBuilder::new();

        // Add data segments before creating the function
        builder.push_data_bytes(&[0x12, 0x34]);
        let data_segment_1 = builder.push_data_bytes(&[0x56, 0x78, 0x9a, 0xbc]);
        builder.push_data_bytes(&[0xde, 0xf0]);

        // Add large constant
        let large_const_id = builder.alloc_u256(U256::from(0xdeadbeef_u64));

        let mut func = builder.begin_function();
        let local0 = func.new_local();
        let local1 = func.new_local();

        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::SetLargeConst(SetLargeConstData {
            sets: local0,
            value: large_const_id,
        }));
        bb.add_operation(Operation::SetDataOffset(SetDataOffsetData {
            sets: local1,
            segment_id: data_segment_1,
        }));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = large_const 0xdeadbeef
        $1 = data_offset .1
        stop
    }


data .0 0x1234
data .1 0x56789abc
data .2 0xdef0
"#;

        assert_ir_display(&program, expected);
    }
}
