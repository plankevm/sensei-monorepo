use sir_data::{
    BasicBlock, BasicBlockId, Control, DataId, EthIRProgram, LargeConstId, LocalIndex, Operation,
    OperationIndex, StaticAllocId,
    operation::{
        AllocatedIns, InternalCallData, SetDataOffsetData, SetLargeConstData, StaticAllocData,
    },
};

#[derive(Debug, Clone, Copy)]
pub enum SpanSource {
    Inputs(BasicBlockId),
    Outputs(BasicBlockId),
    Operations(BasicBlockId),
    OpInputs(BasicBlockId, OperationIndex),
    OpOutputs(BasicBlockId, OperationIndex),
}

#[derive(Debug)]
pub enum LegalizerError {
    InitHasInputs(u32),
    RuntimeHasInputs(u32),
    TerminatorNotLast(BasicBlockId, OperationIndex),
    TerminatorControlMismatch(BasicBlockId, OperationIndex),
    MissingTerminator(BasicBlockId),
    InvalidLargeConstId(LargeConstId),
    InvalidSegmentId(DataId),
    InvalidStaticAllocId(StaticAllocId),
    OverlappingSpans(SpanSource, SpanSource),
    SpanOutOfBounds(SpanSource),
}

pub fn legalize(program: &EthIRProgram) -> Result<(), LegalizerError> {
    Legalizer::new(program).legalize()
}

struct Legalizer<'a> {
    program: &'a EthIRProgram,
    locals_spans: Vec<TrackedSpan<LocalIndex>>,
    operations_spans: Vec<TrackedSpan<OperationIndex>>,
}

impl<'a> Legalizer<'a> {
    fn new(program: &'a EthIRProgram) -> Self {
        todo!()
    }

    fn legalize(&mut self) -> Result<(), LegalizerError> {
        self.validate_entry_points()?;
        self.validate_blocks()?;
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

    fn validate_cfg(&mut self) -> Result<(), LegalizerError> {
        // The call graph is acyclic aka no recursion mutual or otherwise is present
        // The CFG of functions is disjoint (no two functions share the same basic block)
        // All function end blocks either terminate or have the same output count, equal to the function's .outputs (when Control::InternalReturn)
        // The input & output count of connected basic blocks lines up
        todo!()
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

    fn validate_local_ids(&mut self) -> Result<(), LegalizerError> {
        // next_free_local_id & next_static_alloc_id are greater than all IDs used in the graph
        // Validate that every local ID is only assigned once
        // Validate that every referenced local ID is defined somewhere in the function (bb inputs, operation assignment)
        todo!()
    }

    fn validate_entry_points(&mut self) -> Result<(), LegalizerError> {
        // init & runtime entry points have 0 inputs
        let entry_bb =
            &self.program.basic_blocks[self.program.functions[self.program.init_entry].entry()];
        let entry_input_count = entry_bb.inputs.end.get() - entry_bb.inputs.start.get();
        if entry_input_count != 0 {
            return Err(LegalizerError::InitHasInputs(entry_input_count));
        }

        if let Some(main_entry) = self.program.main_entry {
            let main_bb = &self.program.basic_blocks[self.program.functions[main_entry].entry()];
            let main_input_count = main_bb.inputs.end.get() - main_bb.inputs.start.get();
            if main_input_count != 0 {
                return Err(LegalizerError::RuntimeHasInputs(main_input_count));
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
