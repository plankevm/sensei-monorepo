use sir_data::{BasicBlockId, Control, EthIRProgram, FunctionId, Operation, OperationIndex};

pub fn legalize(program: &EthIRProgram) -> Result<(), LegalizerError> {
    Legalizer::new(program).legalize()
}

struct Legalizer<'a> {
    program: &'a EthIRProgram,
}

impl<'a> Legalizer<'a> {
    fn new(program: &'a EthIRProgram) -> Self {
        todo!()
    }

    fn legalize(&mut self) -> Result<(), LegalizerError> {
        self.validate_entry_points()?;
        self.validate_terminators()?;
        todo!()
    }

    fn validate_cfg(&mut self) -> Result<(), LegalizerError> {
        // The call graph is acyclic aka no recursion mutual or otherwise is present
        // The CFG of functions is disjoint (no two functions share the same basic block)
        // All function end blocks either terminate or have the same output count, equal to the function's .outputs (when Control::InternalReturn)
        // The input & output count of connected basic blocks lines up
        todo!()
    }

    fn validate_terminators(&mut self) -> Result<(), LegalizerError> {
        // basic blocks may contain stop, invalid, return, revert, selfdestruct only if they're Control::LastOpTerminates
        // and only if it's their last operation
        // if Control is LastOpTerminates, the last op must be a terminator
        for (bb_id, bb) in self.program.basic_blocks.enumerate_idx() {
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
        }
        Ok(())
    }

    fn validate_ranges(&mut self) -> Result<(), LegalizerError> {
        // References to continuously stored values (indices/ranges) are valid & non-overlapping:
        // BasicBlock inputs, outputs & operations
        // operation allocated ins/outs
        // operation special ids (data, large consts, static alloc, may be reused, just needs to be valid)
        todo!()
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

#[derive(Debug)]
pub enum LegalizerError {
    InitHasInputs(u32),
    RuntimeHasInputs(u32),
    TerminatorNotLast(BasicBlockId, OperationIndex),
    TerminatorControlMismatch(BasicBlockId, OperationIndex),
    MissingTerminator(BasicBlockId),
}
