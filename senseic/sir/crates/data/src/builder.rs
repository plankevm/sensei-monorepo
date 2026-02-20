use crate::*;
use alloy_primitives::U256;
use sensei_core::span::IncIterable;

#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error(
        "Basic block implies conflicting output for function, set != new implied: {set_outputs} != {implied_out}"
    )]
    ConflictingFunctionOutputs { set_outputs: u32, implied_out: u32 },
}

#[derive(Debug)]
pub struct EthIRBuilder {
    next_local_id: LocalId,
    next_alloc_id: StaticAllocId,
    // IR Statements
    pub(crate) functions: IndexVec<FunctionId, Function>,
    pub(crate) basic_blocks: IndexVec<BasicBlockId, BasicBlock>,
    pub(crate) operations: IndexVec<OperationIdx, Operation>,
    pub(crate) data_segments: ListOfLists<DataId, u8>,

    // IR Data
    pub(crate) locals: IndexVec<LocalIdx, LocalId>,
    pub(crate) large_consts: IndexVec<LargeConstId, U256>,
    pub(crate) cases: IndexVec<CasesId, Cases>,
    pub(crate) cases_bb_ids: IndexVec<CasesBasicBlocksIdx, BasicBlockId>,
}

impl EthIRBuilder {
    pub fn new() -> Self {
        Self {
            next_local_id: LocalId::default(),
            next_alloc_id: StaticAllocId::default(),
            functions: IndexVec::new(),
            basic_blocks: IndexVec::new(),
            operations: IndexVec::new(),
            data_segments: ListOfLists::new(),
            locals: IndexVec::new(),
            large_consts: IndexVec::new(),
            cases: IndexVec::new(),
            cases_bb_ids: IndexVec::new(),
        }
    }

    pub fn build(self, init_entry: FunctionId, main_entry: Option<FunctionId>) -> EthIRProgram {
        EthIRProgram {
            init_entry,
            main_entry,
            functions: self.functions,
            basic_blocks: self.basic_blocks,
            operations: self.operations,
            data_segments: self.data_segments,
            locals: self.locals,
            large_consts: self.large_consts,
            cases: self.cases,
            cases_bb_ids: self.cases_bb_ids,
            next_free_local_id: self.next_local_id,
            next_static_alloc_id: self.next_alloc_id,
        }
    }

    pub fn view_bb_backing(&self) -> &IndexVec<BasicBlockId, BasicBlock> {
        &self.basic_blocks
    }

    pub fn new_local(&mut self) -> LocalId {
        self.next_local_id.get_and_inc()
    }

    pub fn new_static_alloc(&mut self) -> StaticAllocId {
        self.next_alloc_id.get_and_inc()
    }

    pub fn alloc_locals(&mut self, locals: &[LocalId]) -> Span<LocalIdx> {
        let start = self.locals.len_idx();
        self.locals.as_mut_vec().extend_from_slice(locals);
        let end = self.locals.len_idx();
        Span::new(start, end)
    }

    pub fn get_func(&self, func: FunctionId) -> Option<&Function> {
        self.functions.get(func)
    }

    pub fn next_basic_block_id(&self) -> BasicBlockId {
        self.basic_blocks.next_idx()
    }

    pub fn alloc_u256(&mut self, value: U256) -> LargeConstId {
        self.large_consts.push(value)
    }

    pub fn push_data_bytes(&mut self, bytes: &[u8]) -> DataId {
        self.data_segments.push_copy_slice(bytes)
    }

    // Function builder
    pub fn begin_function(&mut self) -> FunctionBuilder<'_> {
        let next_bb = self.basic_blocks.next_idx();
        FunctionBuilder { ir_builder: self, first_bb: next_bb, last_bb: next_bb, outputs: None }
    }
}

impl Default for EthIRBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[must_use]
pub struct FunctionBuilder<'ir> {
    pub ir_builder: &'ir mut EthIRBuilder,
    first_bb: BasicBlockId,
    last_bb: BasicBlockId,
    outputs: Option<u32>,
}

impl<'ir> FunctionBuilder<'ir> {
    pub fn new_local(&mut self) -> LocalId {
        self.ir_builder.new_local()
    }

    pub fn begin_basic_block(&mut self) -> BasicBlockBuilder<'_, 'ir> {
        let next_op = self.ir_builder.operations.next_idx();
        let next_local = self.ir_builder.locals.next_idx();
        BasicBlockBuilder {
            fn_builder: self,
            operations: Span::new(next_op, next_op),
            inputs: Span::new(next_local, next_local),
            outputs: Span::new(next_local, next_local),
        }
    }

    pub fn set_control(&mut self, bb_id: BasicBlockId, control: Control) -> Result<(), BuildError> {
        let bb = &mut self.ir_builder.basic_blocks[bb_id];
        bb.control = control;

        let implied_out = bb.implied_fn_out();
        if let Some((set_outputs, implied_out)) = self.outputs.zip(implied_out)
            && set_outputs != implied_out
        {
            return Err(BuildError::ConflictingFunctionOutputs { set_outputs, implied_out });
        }
        self.outputs = self.outputs.or(implied_out);

        Ok(())
    }

    pub fn begin_switch(&mut self) -> SwitchBuilder<'_, Self> {
        let values_start = self.ir_builder.large_consts.next_idx();
        let targets_start = self.ir_builder.cases_bb_ids.next_idx();
        SwitchBuilder { context: self, values_start, targets_start, cases_count: 0 }
    }

    fn push_completed_basic_block(&mut self, bb: BasicBlock) -> Result<BasicBlockId, BuildError> {
        let implied_out = bb.implied_fn_out();

        if let Some((set_outputs, implied_out)) = self.outputs.zip(implied_out)
            && set_outputs != implied_out
        {
            return Err(BuildError::ConflictingFunctionOutputs { set_outputs, implied_out });
        }
        self.outputs = self.outputs.or(implied_out);

        let bb_id = self.ir_builder.basic_blocks.push(bb);
        assert_eq!(bb_id, self.last_bb, "basic blocks not contiguous");
        self.last_bb = self.ir_builder.basic_blocks.next_idx();

        Ok(bb_id)
    }

    pub fn finish(self, entry_bb_id: BasicBlockId) -> FunctionId {
        let end_bb = self.ir_builder.basic_blocks.next_idx();
        let basic_blocks = self.first_bb..end_bb;
        assert!(
            basic_blocks.contains(&entry_bb_id),
            "Specifying entry basic block that's not part of function"
        );

        self.ir_builder.functions.push(Function { entry_bb_id, outputs: self.outputs.unwrap_or(0) })
    }
}

impl<'ir> AsMut<EthIRBuilder> for FunctionBuilder<'ir> {
    fn as_mut(&mut self) -> &mut EthIRBuilder {
        self.ir_builder
    }
}

#[must_use]
pub struct BasicBlockBuilder<'func, 'ir: 'func> {
    pub fn_builder: &'func mut FunctionBuilder<'ir>,
    operations: Span<OperationIdx>,
    inputs: Span<LocalIdx>,
    outputs: Span<LocalIdx>,
}

impl<'func, 'ir: 'func> BasicBlockBuilder<'func, 'ir> {
    pub fn new_local(&mut self) -> LocalId {
        self.fn_builder.new_local()
    }

    pub fn add_operation(&mut self, op: Operation) -> OperationIdx {
        let idx = self.fn_builder.ir_builder.operations.push(op);
        assert_eq!(idx, self.operations.end, "operations not contiguous");
        self.operations.end = self.fn_builder.ir_builder.operations.next_idx();
        idx
    }

    pub fn set_inputs(&mut self, new_inputs: &[LocalId]) {
        overwrite_span_via_copy(
            &mut self.inputs,
            &mut self.fn_builder.ir_builder.locals,
            new_inputs,
        );
    }

    pub fn set_outputs(&mut self, new_outputs: &[LocalId]) {
        overwrite_span_via_copy(
            &mut self.outputs,
            &mut self.fn_builder.ir_builder.locals,
            new_outputs,
        );
    }

    pub fn begin_switch(&mut self) -> SwitchBuilder<'_, Self> {
        let ir_builder: &mut EthIRBuilder = self.as_mut();
        let values_start = ir_builder.large_consts.next_idx();
        let targets_start = ir_builder.cases_bb_ids.next_idx();
        SwitchBuilder { context: self, values_start, targets_start, cases_count: 0 }
    }

    pub fn finish(self, control: Control) -> Result<BasicBlockId, BuildError> {
        self.fn_builder.push_completed_basic_block(BasicBlock {
            inputs: self.inputs,
            outputs: self.outputs,
            operations: self.operations,
            control,
        })
    }
}

impl<'func, 'ir: 'func> AsMut<EthIRBuilder> for BasicBlockBuilder<'func, 'ir> {
    fn as_mut(&mut self) -> &mut EthIRBuilder {
        self.fn_builder.ir_builder
    }
}

#[must_use]
pub struct SwitchBuilder<'ctx, C: AsMut<EthIRBuilder>> {
    context: &'ctx mut C,
    values_start: LargeConstId,
    targets_start: CasesBasicBlocksIdx,
    cases_count: u32,
}

impl<'ctx, C: AsMut<EthIRBuilder>> SwitchBuilder<'ctx, C> {
    pub fn push_case(&mut self, value: U256, target: BasicBlockId) {
        let ir = self.context.as_mut();

        let value_idx = ir.alloc_u256(value);
        assert_eq!(value_idx, self.values_start + self.cases_count, "switch values not contiguous");

        let target_idx = ir.cases_bb_ids.push(target);
        assert_eq!(
            target_idx,
            self.targets_start + self.cases_count,
            "switch targets not contiguous"
        );

        self.cases_count += 1;
    }

    pub fn finish(self, condition: LocalId, fallback: Option<BasicBlockId>) -> Switch {
        let ir = self.context.as_mut();
        let cases_id = ir.cases.push(Cases {
            values_start_id: self.values_start,
            targets_start_id: self.targets_start,
            cases_count: self.cases_count,
        });

        Switch { condition, fallback, cases: cases_id }
    }
}

fn overwrite_span_via_copy<I: Idx, T: Copy>(
    span: &mut Span<I>,
    backing: &mut IndexVec<I, T>,
    new_values: &[T],
) {
    let len = (span.end.get() - span.start.get()) as usize;
    if len >= new_values.len() {
        backing[*span][..new_values.len()].copy_from_slice(new_values);
        span.end = span.start + new_values.len() as u32;
        return;
    }

    if span.end == backing.len_idx() {
        backing[*span].clone_from_slice(&new_values[..len]);
        backing.as_mut_vec().extend_from_slice(&new_values[len..]);
        span.end = backing.len_idx();
        return;
    }

    span.start = backing.len_idx();
    backing.as_mut_vec().extend_from_slice(new_values);
    span.end = backing.len_idx();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::operation::*;
    use alloy_primitives::uint;

    #[test]
    fn test_simple_function() {
        let mut builder = EthIRBuilder::new();

        // Create a function
        let mut func = builder.begin_function();

        // Add a basic block
        let mut bb = func.begin_basic_block();
        let op = Operation::try_build(
            OperationKind::SetSmallConst,
            &[],
            &[LocalId::new(0)],
            OpExtraData::Num(uint!(42U256)),
            bb.as_mut(),
        )
        .unwrap();
        bb.add_operation(op);
        bb.set_outputs(&[LocalId::new(0)]);
        let bb_id = bb.finish(Control::InternalReturn).unwrap();

        // Finish the function
        let func_id = func.finish(bb_id);

        // Build the program
        let program = builder.build(func_id, None);

        assert_eq!(program.init_entry, func_id);
        assert_eq!(program.functions[func_id].get_outputs(), 1);
        assert_eq!(program.operations.len(), 1);
    }

    #[test]
    fn test_switch_builder() {
        let mut builder = EthIRBuilder::new();

        let mut func = builder.begin_function();

        // Create basic blocks for switch targets
        let bb0 = func.begin_basic_block().finish(Control::InternalReturn).unwrap();
        let bb1 = func.begin_basic_block().finish(Control::InternalReturn).unwrap();
        let bb2 = func.begin_basic_block().finish(Control::InternalReturn).unwrap();
        let fallback_bb = func.begin_basic_block().finish(Control::InternalReturn).unwrap();

        // Create switch using builder
        let condition = func.new_local();
        let mut switch_builder = func.begin_switch();
        switch_builder.push_case(U256::from(1), bb0);
        switch_builder.push_case(U256::from(2), bb1);
        switch_builder.push_case(U256::from(3), bb2);
        let switch = switch_builder.finish(condition, Some(fallback_bb));

        // Create entry block with switch
        let entry_bb = func.begin_basic_block().finish(Control::Switch(switch)).unwrap();

        let func_id = func.finish(entry_bb);

        let program = builder.build(func_id, None);

        // Verify the switch was created correctly
        let entry_bb_data = &program.basic_blocks[entry_bb];
        if let Control::Switch(sw) = &entry_bb_data.control {
            assert_eq!(sw.condition, condition);
            assert_eq!(sw.fallback, Some(fallback_bb));

            let cases = &program.cases[sw.cases];
            assert_eq!(cases.cases_count, 3);

            let values = cases.get_values(&program);
            assert_eq!(values.len(), 3);
            assert_eq!(values[cases.values_start_id], U256::from(1));
            assert_eq!(values[cases.values_start_id + 1], U256::from(2));
            assert_eq!(values[cases.values_start_id + 2], U256::from(3));

            let targets = cases.get_bb_ids(&program);
            assert_eq!(targets.len(), 3);
            assert_eq!(targets[cases.targets_start_id], bb0);
            assert_eq!(targets[cases.targets_start_id + 1], bb1);
            assert_eq!(targets[cases.targets_start_id + 2], bb2);
        } else {
            panic!("Expected Switch control flow");
        }
    }
}
