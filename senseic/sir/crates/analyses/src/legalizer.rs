use sir_data::{
    BasicBlock, BasicBlockId, Control, DataId, DenseIndexSet, EthIRProgram, Function, FunctionId,
    Idx, IndexVec, LargeConstId, LocalIdx, Operation, OperationIdx, StaticAllocId, index_vec,
    operation::{
        AllocatedIns, InternalCallData, SetDataOffsetData, SetLargeConstData, StaticAllocData,
    },
};

#[derive(Debug, Clone, Copy)]
pub enum SpanSource {
    Inputs(BasicBlockId),
    Outputs(BasicBlockId),
    Operations(BasicBlockId),
    OpInputs(BasicBlockId, OperationIdx),
    OpOutputs(BasicBlockId, OperationIdx),
}

#[derive(Debug)]
pub enum LegalizerError {
    InitHasInputs(u32),
    RuntimeHasInputs(u32),
    TerminatorNotLast(BasicBlockId, OperationIdx),
    TerminatorControlMismatch(BasicBlockId, OperationIdx),
    MissingTerminator(BasicBlockId),
    InvalidLargeConstId(LargeConstId),
    InvalidSegmentId(DataId),
    InvalidStaticAllocId(StaticAllocId),
    OverlappingSpans(SpanSource, SpanSource),
    SpanOutOfBounds(SpanSource),
    SharedBasicBlock(BasicBlockId, FunctionId, FunctionId),
    IncompatibleEdge { from: BasicBlockId, to: BasicBlockId },
    WrongOutputCount { block: BasicBlockId, expected: u32 },
    RecursiveCall(FunctionId, FunctionId),
}

pub fn legalize(program: &EthIRProgram) -> Result<(), LegalizerError> {
    Legalizer::new(program).legalize()
}

struct Legalizer<'a> {
    program: &'a EthIRProgram,
    locals_spans: Vec<TrackedSpan<LocalIdx>>,
    operations_spans: Vec<TrackedSpan<OperationIdx>>,
    block_owner: IndexVec<BasicBlockId, Option<FunctionId>>,
    call_edges: Vec<(FunctionId, FunctionId)>,
}

impl<'a> Legalizer<'a> {
    fn new(program: &'a EthIRProgram) -> Self {
        todo!()
    }

    fn legalize(&mut self) -> Result<(), LegalizerError> {
        self.validate_entry_points()?;
        self.validate_blocks()?;
        self.validate_cfg()?;
        todo!()
    }

    fn validate_cfg(&mut self) -> Result<(), LegalizerError> {
        let mut visited = DenseIndexSet::new();
        for (fn_id, function) in self.program.functions.enumerate_idx() {
            visited.clear();
            self.visit_block(fn_id, function.entry(), &mut visited)?;
        }
        self.validate_call_graph()
    }

    fn validate_call_graph(&self) -> Result<(), LegalizerError> {
        let mut callees: IndexVec<FunctionId, Vec<FunctionId>> =
            index_vec![Vec::new(); self.program.functions.len()];
        for (caller, callee) in &self.call_edges {
            callees[*caller].push(*callee);
        }

        // 0 = unvisited, 1 = in progress, 2 = done
        let mut color: IndexVec<FunctionId, u8> = index_vec![0; self.program.functions.len()];
        for fn_id in self.program.functions.iter_idx() {
            if color[fn_id] == 0 {
                detect_cycle(fn_id, &callees, &mut color)?;
            }
        }
        Ok(())
    }

    fn visit_block(
        &mut self,
        fn_id: FunctionId,
        bb: BasicBlockId,
        visited: &mut DenseIndexSet<BasicBlockId>,
    ) -> Result<(), LegalizerError> {
        if visited.contains(bb) {
            return Ok(());
        }
        visited.add(bb);

        // function end blocks have output count equal to the function's .outputs when Control::InternalReturn
        if matches!(self.program.basic_blocks[bb].control, Control::InternalReturn) {
            if self.program.basic_blocks[bb].outputs.len()
                != self.program.functions[fn_id].get_outputs()
            {
                return Err(LegalizerError::WrongOutputCount {
                    block: bb,
                    expected: self.program.functions[fn_id].get_outputs(),
                });
            }
        }

        // check no two functions share the same basic block
        if let Some(owner) = self.block_owner[bb] {
            return Err(LegalizerError::SharedBasicBlock(bb, owner, fn_id));
        }
        self.block_owner[bb] = Some(fn_id);

        // update call_edges
        for op_id in self.program.basic_blocks[bb].operations.iter() {
            let op = &self.program.operations[op_id];
            if let Operation::InternalCall(InternalCallData { function: callee, .. }) = op {
                self.call_edges.push((fn_id, *callee));
            }
        }

        for succ in self.program.basic_blocks[bb].control.iter_outgoing(self.program) {
            // input & output count of connected basic blocks
            if self.program.basic_blocks[bb].outputs.len()
                != self.program.basic_blocks[succ].inputs.len()
            {
                return Err(LegalizerError::IncompatibleEdge { from: bb, to: succ });
            }
            self.visit_block(fn_id, succ, visited)?;
        }
        Ok(())
    }

    fn validate_local_ids(&mut self) -> Result<(), LegalizerError> {
        // next_free_local_id & next_static_alloc_id are greater than all IDs used in the graph
        // Validate that every local ID is only assigned once
        // Validate that every referenced local ID is defined somewhere in the function (bb inputs, operation assignment)
        todo!()
    }

    fn validate_blocks(&mut self) -> Result<(), LegalizerError> {
        for (bb_id, bb) in self.program.basic_blocks.enumerate_idx() {
            self.validate_block_terminators(bb_id, bb)?;
            self.validate_block_ranges(bb_id, bb)?;
        }

        // final range validation for locals
        self.locals_spans.sort_by_key(|s| s.start);
        for window in self.locals_spans.windows(2) {
            if window[0].end > window[1].start {
                return Err(LegalizerError::OverlappingSpans(window[1].source, window[0].source));
            }
        }

        if let Some(last) = self.locals_spans.last() {
            if last.end.idx() > self.program.locals.len() {
                return Err(LegalizerError::SpanOutOfBounds(last.source));
            }
        }

        // final range validation for operations spans
        self.operations_spans.sort_by_key(|s| s.start);
        for window in self.operations_spans.windows(2) {
            if window[0].end > window[1].start {
                return Err(LegalizerError::OverlappingSpans(window[1].source, window[0].source));
            }
        }

        if let Some(last) = self.operations_spans.last() {
            if last.end.idx() > self.program.operations.len() {
                return Err(LegalizerError::SpanOutOfBounds(last.source));
            }
        }
        Ok(())
    }

    fn validate_block_terminators(
        &self,
        bb_id: BasicBlockId,
        bb: &BasicBlock,
    ) -> Result<(), LegalizerError> {
        // basic blocks may contain stop, invalid, return, revert, selfdestruct only if they're Control::LastOpTerminates
        // and only if it's their last operation
        // if Control is LastOpTerminates, the last op must be a terminator
        if matches!(bb.control, Control::LastOpTerminates) {
            if bb.operations.is_empty()
                || !matches!(
                    &self.program.operations[bb.operations.end - 1],
                    Operation::Return(_)
                        | Operation::Stop(_)
                        | Operation::Revert(_)
                        | Operation::Invalid(_)
                        | Operation::SelfDestruct(_)
                )
            {
                return Err(LegalizerError::MissingTerminator(bb_id));
            }
        }
        for op_id in bb.operations.iter() {
            let op = &self.program.operations[op_id];
            match op {
                Operation::Return(_)
                | Operation::Stop(_)
                | Operation::Revert(_)
                | Operation::Invalid(_)
                | Operation::SelfDestruct(_) => {
                    if op_id != bb.operations.end - 1 {
                        return Err(LegalizerError::TerminatorNotLast(bb_id, op_id));
                    }
                    if !matches!(bb.control, Control::LastOpTerminates) {
                        return Err(LegalizerError::TerminatorControlMismatch(bb_id, op_id));
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn validate_block_ranges(
        &mut self,
        bb_id: BasicBlockId,
        bb: &BasicBlock,
    ) -> Result<(), LegalizerError> {
        self.locals_spans.push(TrackedSpan {
            start: bb.inputs.start,
            end: bb.inputs.end,
            source: SpanSource::Inputs(bb_id),
        });
        self.locals_spans.push(TrackedSpan {
            start: bb.outputs.start,
            end: bb.outputs.end,
            source: SpanSource::Outputs(bb_id),
        });
        self.operations_spans.push(TrackedSpan {
            start: bb.operations.start,
            end: bb.operations.end,
            source: SpanSource::Operations(bb_id),
        });

        for op_id in bb.operations.iter() {
            let op = &self.program.operations[op_id];
            match op {
                Operation::AddMod(AllocatedIns { ins_start, outs: _ })
                | Operation::MulMod(AllocatedIns { ins_start, outs: _ })
                | Operation::ExtCodeCopy(AllocatedIns { ins_start, outs: _ })
                | Operation::Log2(AllocatedIns { ins_start, outs: _ })
                | Operation::Log3(AllocatedIns { ins_start, outs: _ })
                | Operation::Log4(AllocatedIns { ins_start, outs: _ })
                | Operation::Create(AllocatedIns { ins_start, outs: _ })
                | Operation::Create2(AllocatedIns { ins_start, outs: _ })
                | Operation::Call(AllocatedIns { ins_start, outs: _ })
                | Operation::CallCode(AllocatedIns { ins_start, outs: _ })
                | Operation::DelegateCall(AllocatedIns { ins_start, outs: _ })
                | Operation::StaticCall(AllocatedIns { ins_start, outs: _ }) => {
                    self.locals_spans.push(TrackedSpan {
                        start: *ins_start,
                        end: *ins_start + op.inputs(self.program).len() as u32,
                        source: SpanSource::OpInputs(bb_id, op_id),
                    });
                }
                Operation::InternalCall(InternalCallData {
                    function: _,
                    ins_start,
                    outs_start,
                }) => {
                    self.locals_spans.push(TrackedSpan {
                        start: *ins_start,
                        end: *ins_start + op.inputs(self.program).len() as u32,
                        source: SpanSource::OpInputs(bb_id, op_id),
                    });
                    self.locals_spans.push(TrackedSpan {
                        start: *outs_start,
                        end: *outs_start + op.outputs(self.program).len() as u32,
                        source: SpanSource::OpOutputs(bb_id, op_id),
                    });
                }

                Operation::SetLargeConst(SetLargeConstData { sets: _, value }) => {
                    if self.program.large_consts.get(*value).is_none() {
                        return Err(LegalizerError::InvalidLargeConstId(*value));
                    }
                }
                Operation::SetDataOffset(SetDataOffsetData { sets: _, segment_id }) => {
                    if self.program.data_segments_start.get(*segment_id).is_none() {
                        return Err(LegalizerError::InvalidSegmentId(*segment_id));
                    }
                }
                Operation::StaticAllocZeroed(StaticAllocData { size: _, ptr_out: _, alloc_id })
                | Operation::StaticAllocAnyBytes(StaticAllocData {
                    size: _,
                    ptr_out: _,
                    alloc_id,
                }) => {
                    if *alloc_id >= self.program.next_static_alloc_id {
                        return Err(LegalizerError::InvalidStaticAllocId(*alloc_id));
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn validate_entry_points(&mut self) -> Result<(), LegalizerError> {
        // init & runtime entry points have 0 inputs
        let entry_bb =
            &self.program.basic_blocks[self.program.functions[self.program.init_entry].entry()];
        if !entry_bb.inputs.is_empty() {
            return Err(LegalizerError::InitHasInputs(entry_bb.inputs.len()));
        }

        if let Some(main_entry) = self.program.main_entry {
            let main_bb = &self.program.basic_blocks[self.program.functions[main_entry].entry()];
            if !main_bb.inputs.is_empty() {
                return Err(LegalizerError::RuntimeHasInputs(main_bb.inputs.len()));
            }
        }
        Ok(())
    }
}

struct TrackedSpan<I> {
    start: I,
    end: I,
    source: SpanSource,
}

fn detect_cycle(
    fn_id: FunctionId,
    callees: &IndexVec<FunctionId, Vec<FunctionId>>,
    color: &mut IndexVec<FunctionId, u8>,
) -> Result<(), LegalizerError> {
    color[fn_id] = 1; // gray
    for &callee in &callees[fn_id] {
        if color[callee] == 1 {
            return Err(LegalizerError::RecursiveCall(fn_id, callee));
        }
        if color[callee] == 0 {
            detect_cycle(callee, callees, color)?;
        }
    }
    color[fn_id] = 2; // black
    Ok(())
}
