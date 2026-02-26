use sir_data::{
    BasicBlock, BasicBlockId, Control, DataId, DenseIndexSet, EthIRProgram, FunctionId, Idx,
    IndexVec, LargeConstId, LocalId, LocalIdx, Operation, OperationIdx, StaticAllocId, index_vec,
};

use crate::{UseKind, compute_dominators};

/// Identifies which IR construct a tracked span belongs to, used in span overlap diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanSource {
    Inputs(BasicBlockId),
    Outputs(BasicBlockId),
    Operations(BasicBlockId),
    OpInputs(BasicBlockId, OperationIdx),
    OpOutputs(BasicBlockId, OperationIdx),
}

impl std::fmt::Display for SpanSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpanSource::Inputs(bb) => write!(f, "@{bb} inputs"),
            SpanSource::Outputs(bb) => write!(f, "@{bb} outputs"),
            SpanSource::Operations(bb) => write!(f, "@{bb} operations"),
            SpanSource::OpInputs(bb, op) => write!(f, "@{bb} operation {op} inputs"),
            SpanSource::OpOutputs(bb, op) => write!(f, "@{bb} operation {op} outputs"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum LegalizerError {
    #[error("init entry block must not have inputs, found {0}")]
    InitHasInputs(u32),
    #[error("runtime entry block must not have inputs, found {0}")]
    RuntimeHasInputs(u32),
    #[error("terminator operation {1} is not last in @{0}")]
    TerminatorNotLast(BasicBlockId, OperationIdx),
    #[error("terminator operation {1} in @{0} without LastOpTerminates control")]
    TerminatorControlMismatch(BasicBlockId, OperationIdx),
    #[error("@{0} has no terminator operation")]
    MissingTerminator(BasicBlockId),
    #[error("invalid large constant id {0}")]
    InvalidLargeConstId(LargeConstId),
    #[error("invalid data segment id {0}")]
    InvalidSegmentId(DataId),
    #[error("invalid static allocation id {0}")]
    InvalidStaticAllocId(StaticAllocId),
    #[error("overlapping spans: {0} and {1}")]
    OverlappingSpans(SpanSource, SpanSource),
    #[error("span out of bounds: {0}")]
    SpanOutOfBounds(SpanSource),
    #[error("@{0} shared between functions @{1} and @{2}")]
    SharedBasicBlock(BasicBlockId, FunctionId, FunctionId),
    #[error("incompatible edge: @{from} outputs don't match @{to} inputs")]
    IncompatibleEdge { from: BasicBlockId, to: BasicBlockId },
    #[error("@{block} has {actual} outputs, expected {expected}")]
    WrongOutputCount { block: BasicBlockId, expected: u32, actual: u32 },
    #[error("operation {op} has {actual} call inputs, expected {expected}")]
    WrongCallInputCount { op: OperationIdx, expected: u32, actual: u32 },
    #[error("recursive call detected: @{0} calls @{1}")]
    RecursiveCall(FunctionId, FunctionId),
    #[error("invalid local id ${0}")]
    InvalidLocalId(LocalId),
    #[error("local ${0} defined more than once")]
    DoubleDefinition(LocalId),
    #[error("invalid function id @{0}")]
    InvalidFunctionId(FunctionId),
    #[error("invalid basic block id {0}")]
    InvalidBasicBlockId(BasicBlockId),
    #[error("local ${local} not in scope at @{block} ({use_kind})")]
    LocalNotInScope { block: BasicBlockId, local: LocalId, use_kind: UseKind },
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
        let block_owner = index_vec![None; program.basic_blocks.len()];
        Self {
            program,
            locals_spans: Vec::new(),
            operations_spans: Vec::new(),
            block_owner,
            call_edges: Vec::new(),
        }
    }

    fn legalize(&mut self) -> Result<(), LegalizerError> {
        self.validate_entry_points()?;
        self.validate_blocks()?;
        self.validate_cfg()?;
        self.validate_local_ids()
    }

    fn validate_entry_points(&self) -> Result<(), LegalizerError> {
        if self.program.functions.get(self.program.init_entry).is_none() {
            return Err(LegalizerError::InvalidFunctionId(self.program.init_entry));
        }
        let entry_bb =
            &self.program.basic_blocks[self.program.functions[self.program.init_entry].entry()];
        if !entry_bb.inputs.is_empty() {
            return Err(LegalizerError::InitHasInputs(entry_bb.inputs.len()));
        }

        if let Some(main_entry) = self.program.main_entry {
            if self.program.functions.get(main_entry).is_none() {
                return Err(LegalizerError::InvalidFunctionId(main_entry));
            }
            let main_bb = &self.program.basic_blocks[self.program.functions[main_entry].entry()];
            if !main_bb.inputs.is_empty() {
                return Err(LegalizerError::RuntimeHasInputs(main_bb.inputs.len()));
            }
        }
        Ok(())
    }

    fn validate_basic_block_id(&self, bb_id: BasicBlockId) -> Result<(), LegalizerError> {
        if self.program.basic_blocks.get(bb_id).is_none() {
            return Err(LegalizerError::InvalidBasicBlockId(bb_id));
        }
        Ok(())
    }

    fn validate_blocks(&mut self) -> Result<(), LegalizerError> {
        for (bb_id, bb) in self.program.basic_blocks.enumerate_idx() {
            self.validate_block_terminators(bb_id, bb)?;
            self.validate_block_indices(bb_id, bb)?;
        }

        validate_spans(&mut self.locals_spans, self.program.locals.len())?;
        validate_spans(&mut self.operations_spans, self.program.operations.len())
    }

    fn validate_block_terminators(
        &self,
        bb_id: BasicBlockId,
        bb: &BasicBlock,
    ) -> Result<(), LegalizerError> {
        if matches!(bb.control, Control::LastOpTerminates)
            && self.program.operations[bb.operations].last().is_none_or(|op| {
                !matches!(
                    op,
                    Operation::Return(_)
                        | Operation::Stop(_)
                        | Operation::Revert(_)
                        | Operation::Invalid(_)
                        | Operation::SelfDestruct(_)
                )
            })
        {
            return Err(LegalizerError::MissingTerminator(bb_id));
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

    fn validate_block_indices(
        &mut self,
        bb_id: BasicBlockId,
        bb: &BasicBlock,
    ) -> Result<(), LegalizerError> {
        if !bb.inputs.is_empty() {
            self.locals_spans.push(TrackedSpan {
                start: bb.inputs.start,
                end: bb.inputs.end,
                source: SpanSource::Inputs(bb_id),
            });
        }
        if !bb.outputs.is_empty() {
            self.locals_spans.push(TrackedSpan {
                start: bb.outputs.start,
                end: bb.outputs.end,
                source: SpanSource::Outputs(bb_id),
            });
        }
        if !bb.operations.is_empty() {
            self.operations_spans.push(TrackedSpan {
                start: bb.operations.start,
                end: bb.operations.end,
                source: SpanSource::Operations(bb_id),
            });
        }

        match &bb.control {
            Control::Branches(branch) => {
                if branch.condition >= self.program.next_free_local_id {
                    return Err(LegalizerError::InvalidLocalId(branch.condition));
                }
                self.validate_basic_block_id(branch.non_zero_target)?;
                self.validate_basic_block_id(branch.zero_target)?;
            }
            Control::Switch(switch) => {
                if switch.condition >= self.program.next_free_local_id {
                    return Err(LegalizerError::InvalidLocalId(switch.condition));
                }
                if let Some(fallback) = switch.fallback {
                    self.validate_basic_block_id(fallback)?;
                }
                for &target in self.program.cases[switch.cases].get_bb_ids(self.program).iter() {
                    self.validate_basic_block_id(target)?;
                }
            }
            Control::ContinuesTo(target) => {
                self.validate_basic_block_id(*target)?;
            }
            Control::LastOpTerminates | Control::InternalReturn => {}
        }

        for op_id in bb.operations.iter() {
            let op = &self.program.operations[op_id];

            match op {
                Operation::SetLargeConst(data) => {
                    if self.program.large_consts.get(data.value).is_none() {
                        return Err(LegalizerError::InvalidLargeConstId(data.value));
                    }
                }
                Operation::SetDataOffset(data) => {
                    if self.program.data_segments.get(data.segment_id).is_none() {
                        return Err(LegalizerError::InvalidSegmentId(data.segment_id));
                    }
                }
                Operation::StaticAllocZeroed(data) | Operation::StaticAllocAnyBytes(data) => {
                    if data.alloc_id >= self.program.next_static_alloc_id {
                        return Err(LegalizerError::InvalidStaticAllocId(data.alloc_id));
                    }
                }
                Operation::InternalCall(data) => {
                    if self.program.functions.get(data.function).is_none() {
                        return Err(LegalizerError::InvalidFunctionId(data.function));
                    }
                }
                _ => {}
            }

            for local_id in op.inputs(self.program).iter().chain(op.outputs(self.program)) {
                if *local_id >= self.program.next_free_local_id {
                    return Err(LegalizerError::InvalidLocalId(*local_id));
                }
            }

            let spans = op.allocated_spans(self.program);
            if let Some(span) = spans.input {
                self.locals_spans.push(TrackedSpan {
                    start: span.start,
                    end: span.end,
                    source: SpanSource::OpInputs(bb_id, op_id),
                });
            }
            if let Some(span) = spans.output {
                self.locals_spans.push(TrackedSpan {
                    start: span.start,
                    end: span.end,
                    source: SpanSource::OpOutputs(bb_id, op_id),
                });
            }
        }
        Ok(())
    }

    fn validate_cfg(&mut self) -> Result<(), LegalizerError> {
        let mut visited = DenseIndexSet::new();
        for (fn_id, function) in self.program.functions.enumerate_idx() {
            visited.clear();
            self.validate_cfg_visit_block(fn_id, function.entry(), &mut visited)?;
        }
        self.validate_call_graph()
    }

    fn validate_call_graph(&self) -> Result<(), LegalizerError> {
        let mut callees: IndexVec<FunctionId, Vec<FunctionId>> =
            index_vec![Vec::new(); self.program.functions.len()];
        for (caller, callee) in &self.call_edges {
            callees[*caller].push(*callee);
        }

        #[derive(PartialEq, Clone, Copy)]
        enum VisitState {
            Unvisited,
            InProgress,
            Done,
        }

        fn detect_cycle(
            fn_id: FunctionId,
            callees: &IndexVec<FunctionId, Vec<FunctionId>>,
            state: &mut IndexVec<FunctionId, VisitState>,
        ) -> Result<(), LegalizerError> {
            state[fn_id] = VisitState::InProgress;
            for &callee in &callees[fn_id] {
                if state[callee] == VisitState::InProgress {
                    return Err(LegalizerError::RecursiveCall(fn_id, callee));
                }
                if state[callee] == VisitState::Unvisited {
                    detect_cycle(callee, callees, state)?;
                }
            }
            state[fn_id] = VisitState::Done;
            Ok(())
        }

        let mut visit_state = index_vec![VisitState::Unvisited; self.program.functions.len()];
        for fn_id in self.program.functions.iter_idx() {
            if visit_state[fn_id] == VisitState::Unvisited {
                detect_cycle(fn_id, &callees, &mut visit_state)?;
            }
        }
        Ok(())
    }

    fn validate_cfg_visit_block(
        &mut self,
        fn_id: FunctionId,
        bb: BasicBlockId,
        visited: &mut DenseIndexSet<BasicBlockId>,
    ) -> Result<(), LegalizerError> {
        if visited.contains(bb) {
            return Ok(());
        }
        visited.add(bb);

        if matches!(self.program.basic_blocks[bb].control, Control::InternalReturn)
            && self.program.basic_blocks[bb].outputs.len()
                != self.program.functions[fn_id].get_outputs()
        {
            return Err(LegalizerError::WrongOutputCount {
                block: bb,
                expected: self.program.functions[fn_id].get_outputs(),
                actual: self.program.basic_blocks[bb].outputs.len(),
            });
        }

        if let Some(owner) = self.block_owner[bb] {
            return Err(LegalizerError::SharedBasicBlock(bb, owner, fn_id));
        }
        self.block_owner[bb] = Some(fn_id);

        for op_id in self.program.basic_blocks[bb].operations.iter() {
            let op = &self.program.operations[op_id];
            let Operation::InternalCall(data) = op else { continue };
            let expected_ins =
                self.program.functions[data.function].get_inputs(&self.program.basic_blocks);
            let actual_ins = data.outs_start - data.ins_start;
            if actual_ins != expected_ins {
                return Err(LegalizerError::WrongCallInputCount {
                    op: op_id,
                    expected: expected_ins,
                    actual: actual_ins,
                });
            }
            self.call_edges.push((fn_id, data.function));
        }

        for succ in self.program.basic_blocks[bb].control.iter_outgoing(self.program) {
            if self.program.basic_blocks[bb].outputs.len()
                != self.program.basic_blocks[succ].inputs.len()
            {
                return Err(LegalizerError::IncompatibleEdge { from: bb, to: succ });
            }
            self.validate_cfg_visit_block(fn_id, succ, visited)?;
        }
        Ok(())
    }

    fn validate_local_ids(&self) -> Result<(), LegalizerError> {
        self.validate_single_assignment()?;
        self.validate_scope()
    }

    fn validate_single_assignment(&self) -> Result<(), LegalizerError> {
        let mut defs = DenseIndexSet::new();
        for bb in self.program.basic_blocks.iter() {
            for local in self.program.locals[bb.inputs].iter() {
                if !defs.add(*local) {
                    return Err(LegalizerError::DoubleDefinition(*local));
                }
            }
            for op_idx in bb.operations.iter() {
                for local in self.program.operations[op_idx].outputs(self.program) {
                    if !defs.add(*local) {
                        return Err(LegalizerError::DoubleDefinition(*local));
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_scope(&self) -> Result<(), LegalizerError> {
        let dominators = compute_dominators(self.program);

        let mut dom_children: IndexVec<BasicBlockId, Vec<BasicBlockId>> =
            index_vec![Vec::new(); self.program.basic_blocks.len()];

        for (bb_id, &idom) in dominators.enumerate_idx() {
            if let Some(parent) = idom
                && parent != bb_id
            {
                dom_children[parent].push(bb_id);
            }
        }

        let mut in_scope = DenseIndexSet::new();
        let mut added = Vec::new();
        for function in self.program.functions.iter() {
            in_scope.clear();
            self.validate_block_scope(function.entry(), &mut in_scope, &mut added, &dom_children)?;
        }
        Ok(())
    }

    fn validate_block_scope(
        &self,
        bb_id: BasicBlockId,
        in_scope: &mut DenseIndexSet<LocalId>,
        added: &mut Vec<LocalId>,
        dom_children: &IndexVec<BasicBlockId, Vec<BasicBlockId>>,
    ) -> Result<(), LegalizerError> {
        let bb = &self.program.basic_blocks[bb_id];
        let prev_len = added.len();

        for &local in &self.program.locals[bb.inputs] {
            added.push(local);
            in_scope.add(local);
        }

        for op_idx in bb.operations.iter() {
            for local_id in self.program.operations[op_idx].inputs(self.program) {
                if !in_scope.contains(*local_id) {
                    return Err(LegalizerError::LocalNotInScope {
                        block: bb_id,
                        local: *local_id,
                        use_kind: UseKind::Operation(op_idx),
                    });
                }
            }

            for &local_id in self.program.operations[op_idx].outputs(self.program) {
                added.push(local_id);
                in_scope.add(local_id);
            }
        }

        for &local_id in &self.program.locals[bb.outputs] {
            if !in_scope.contains(local_id) {
                return Err(LegalizerError::LocalNotInScope {
                    block: bb_id,
                    local: local_id,
                    use_kind: UseKind::BlockOutput,
                });
            }
        }

        match &bb.control {
            Control::Branches(branch) => {
                if !in_scope.contains(branch.condition) {
                    return Err(LegalizerError::LocalNotInScope {
                        block: bb_id,
                        local: branch.condition,
                        use_kind: UseKind::Control,
                    });
                }
            }
            Control::Switch(switch) => {
                if !in_scope.contains(switch.condition) {
                    return Err(LegalizerError::LocalNotInScope {
                        block: bb_id,
                        local: switch.condition,
                        use_kind: UseKind::Control,
                    });
                }
            }
            _ => {}
        }

        for &child in &dom_children[bb_id] {
            self.validate_block_scope(child, in_scope, added, dom_children)?;
        }

        for &local in &added[prev_len..] {
            in_scope.remove(local);
        }
        added.truncate(prev_len);

        Ok(())
    }
}

struct TrackedSpan<I> {
    start: I,
    end: I,
    source: SpanSource,
}

fn validate_spans<I: Ord + Idx>(
    spans: &mut [TrackedSpan<I>],
    max_bound: usize,
) -> Result<(), LegalizerError> {
    spans.sort_by_key(|s| s.start);
    for window in spans.windows(2) {
        if window[0].end > window[1].start {
            return Err(LegalizerError::OverlappingSpans(window[0].source, window[1].source));
        }
    }
    if let Some(last) = spans.last()
        && last.end.idx() > max_bound
    {
        return Err(LegalizerError::SpanOutOfBounds(last.source));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::U256;
    use sir_data::{
        Branch, Control,
        builder::EthIRBuilder,
        operation::{
            InlineOperands, InternalCallData, SetDataOffsetData, SetLargeConstData,
            SetSmallConstData, StaticAllocData,
        },
    };
    use sir_parser::{EmitConfig, parse_without_legalization};

    // Note: WrongOutputCount cannot be triggered via the builder because the builder
    // catches conflicting function outputs (ConflictingFunctionOutputs error).
    // This check exists for malformed IR constructed outside the builder.

    #[test]
    fn test_valid_ir_passes() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    x = const 42
                    y = large_const 0xdeadbeefcafebabe1234567890abcdef
                    z = chainid
                    w = add x z
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert!(legalize(&program).is_ok());
    }

    #[test]
    fn test_valid_ir_with_branches() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    cond = calldatasize
                    => cond ? @then : @else
                }
                then {
                    ptr = freeptr
                    val = mload256 ptr
                    stop
                }
                else {
                    invalid
                }
            "#,
            EmitConfig::init_only(),
        );
        assert!(legalize(&program).is_ok());
    }

    #[test]
    fn test_valid_ir_with_internal_call() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    x = caller
                    y = icall @helper x
                    stop
                }
            fn helper:
                body a -> b {
                    b = iszero a
                    iret
                }
            "#,
            EmitConfig::init_only(),
        );
        assert!(legalize(&program).is_ok());
    }

    #[test]
    fn test_valid_ir_with_block_io() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry -> a b c {
                    a = selfbalance
                    b = chainid
                    c = gas
                    => @next
                }
                next x y z {
                    sum = add x y
                    result = add sum z
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert!(legalize(&program).is_ok());
    }

    #[test]
    fn test_rejects_missing_terminator() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    x = caller
                }
            "#,
            EmitConfig::init_only(),
        );
        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::MissingTerminator(BasicBlockId::new(0))
        );
    }

    #[test]
    fn test_rejects_incompatible_edge() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry -> x {
                    x = large_const 0xdeadbeef
                    => @next
                }
                next {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::IncompatibleEdge {
                from: BasicBlockId::new(0),
                to: BasicBlockId::new(1)
            }
        );
    }

    #[test]
    fn test_valid_loop() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    limit = large_const 0xffffffffffffffff
                    => @loop_header
                }
                loop_header {
                    cond = returndatasize
                    => cond ? @loop_header : @exit
                }
                exit {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert!(legalize(&program).is_ok());
    }

    #[test]
    fn test_valid_diamond() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    cond = gas
                    => cond ? @left : @right
                }
                left {
                    ptr_l = freeptr
                    val_l = const 1
                    mstore256 ptr_l val_l
                    => @merge
                }
                right {
                    ptr_r = freeptr
                    val_r = large_const 0xcafebabe
                    mstore256 ptr_r val_r
                    => @merge
                }
                merge {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert!(legalize(&program).is_ok());
    }

    #[test]
    fn test_valid_local_from_dominator_ancestor() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    x = gas
                    => @a
                }
                a {
                    => @b
                }
                b {
                    => @c
                }
                c {
                    y = iszero x
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert!(legalize(&program).is_ok());
    }

    #[test]
    fn test_rejects_local_not_in_scope_control() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    => @header
                }
                header {
                    => cond ? @body : @exit
                }
                body {
                    cond = gas
                    => @header
                }
                exit {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::LocalNotInScope {
                block: BasicBlockId::new(1),
                local: LocalId::new(0),
                use_kind: UseKind::Control,
            }
        );
    }

    #[test]
    fn test_rejects_incompatible_merge() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let cond = func.new_local();
        let out_left = func.new_local();
        let merge_id = BasicBlockId::new(3);
        let left_id = BasicBlockId::new(1);
        let right_id = BasicBlockId::new(2);

        let mut entry = func.begin_basic_block();
        entry.add_operation(Operation::Gas(InlineOperands { ins: [], outs: [cond] }));
        let entry_id = entry
            .finish(Control::Branches(Branch {
                condition: cond,
                non_zero_target: left_id,
                zero_target: right_id,
            }))
            .unwrap();

        let mut left = func.begin_basic_block();
        left.add_operation(Operation::SetSmallConst(SetSmallConstData {
            sets: out_left,
            value: 1,
        }));
        left.set_outputs(&[out_left]);
        left.finish(Control::ContinuesTo(merge_id)).unwrap();

        let mut right = func.begin_basic_block();
        right.add_operation(Operation::Noop(()));
        right.finish(Control::ContinuesTo(merge_id)).unwrap();

        let merge_in = func.new_local();
        let mut merge = func.begin_basic_block();
        merge.set_inputs(&[merge_in]);
        merge.add_operation(Operation::Stop(()));
        merge.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(entry_id);
        let program = builder.build(func_id, None);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::IncompatibleEdge { from: right_id, to: merge_id }
        );
    }

    #[test]
    fn test_rejects_invalid_basic_block_id() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();
        let invalid_bb = BasicBlockId::new(999);

        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::Noop(()));
        let bb_id = bb.finish(Control::ContinuesTo(invalid_bb)).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::InvalidBasicBlockId(invalid_bb)
        );
    }

    #[test]
    fn test_rejects_invalid_function_id() {
        let mut builder = EthIRBuilder::new();
        let invalid_id = FunctionId::new(999);

        let mut func = builder.begin_function();
        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::InternalCall(InternalCallData {
            function: invalid_id,
            ins_start: LocalIdx::new(0),
            outs_start: LocalIdx::new(0),
        }));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();
        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(legalize(&program).unwrap_err(), LegalizerError::InvalidFunctionId(invalid_id));
    }

    #[test]
    fn test_rejects_wrong_call_input_count() {
        let mut program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    x = caller
                    y = icall @helper x
                    stop
                }
            fn helper:
                body a -> b {
                    b = iszero a
                    iret
                }
            "#,
            EmitConfig::init_only(),
        );

        let icall_idx = program
            .operations
            .iter_idx()
            .find(|op_id| matches!(program.operations[*op_id], Operation::InternalCall(_)))
            .unwrap();

        if let Operation::InternalCall(data) = &mut program.operations[icall_idx] {
            data.ins_start = data.outs_start;
        }

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::WrongCallInputCount { op: icall_idx, expected: 1, actual: 0 }
        );
    }

    #[test]
    fn test_rejects_direct_recursion() {
        let mut builder = EthIRBuilder::new();
        let func_id = FunctionId::new(0);

        let mut func = builder.begin_function();
        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::InternalCall(InternalCallData {
            function: func_id,
            ins_start: LocalIdx::new(0),
            outs_start: LocalIdx::new(0),
        }));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();
        func.finish(bb_id);

        let program = builder.build(func_id, None);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::RecursiveCall(func_id, func_id)
        );
    }

    #[test]
    fn test_rejects_mutual_recursion() {
        let mut builder = EthIRBuilder::new();

        let func_a_id = FunctionId::new(0);
        let func_b_id = FunctionId::new(1);

        let mut func_a = builder.begin_function();
        let mut bb_a = func_a.begin_basic_block();
        bb_a.add_operation(Operation::InternalCall(InternalCallData {
            function: func_b_id,
            ins_start: LocalIdx::new(0),
            outs_start: LocalIdx::new(0),
        }));
        bb_a.add_operation(Operation::Stop(()));
        let bb_a_id = bb_a.finish(Control::LastOpTerminates).unwrap();
        func_a.finish(bb_a_id);

        let mut func_b = builder.begin_function();
        let mut bb_b = func_b.begin_basic_block();
        bb_b.add_operation(Operation::InternalCall(InternalCallData {
            function: func_a_id,
            ins_start: LocalIdx::new(0),
            outs_start: LocalIdx::new(0),
        }));
        bb_b.add_operation(Operation::Stop(()));
        let bb_b_id = bb_b.finish(Control::LastOpTerminates).unwrap();
        func_b.finish(bb_b_id);

        let program = builder.build(func_a_id, None);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::RecursiveCall(func_b_id, func_a_id)
        );
    }

    #[test]
    fn test_rejects_double_definition() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let local = func.new_local();

        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::SetSmallConst(SetSmallConstData { sets: local, value: 1 }));
        bb.add_operation(Operation::SetSmallConst(SetSmallConstData { sets: local, value: 2 }));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(legalize(&program).unwrap_err(), LegalizerError::DoubleDefinition(local));
    }

    #[test]
    fn test_rejects_local_not_in_scope_operation() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    x = gas
                    => x ? @left : @right
                }
                left {
                    c = gas
                    => c ? @left_inner : @left_exit
                }
                left_inner {
                    y = const 1
                    stop
                }
                left_exit {
                    stop
                }
                right {
                    z = iszero y
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::LocalNotInScope {
                block: BasicBlockId::new(4),
                local: LocalId::new(2),
                use_kind: UseKind::Operation(OperationIdx::new(5)),
            }
        );
    }

    #[test]
    fn test_rejects_local_not_in_scope_block_output() {
        let program = parse_without_legalization(
            r#"
            fn init:
                entry {
                    c = gas
                    => c ? @left : @right
                }
                left {
                    x = const 1
                    stop
                }
                right -> x {
                    => @next
                }
                next y {
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );
        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::LocalNotInScope {
                block: BasicBlockId::new(2),
                local: LocalId::new(1),
                use_kind: UseKind::BlockOutput,
            }
        );
    }

    #[test]
    fn test_rejects_init_has_inputs() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let input = func.new_local();
        let mut bb = func.begin_basic_block();
        bb.set_inputs(&[input]);
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(legalize(&program).unwrap_err(), LegalizerError::InitHasInputs(1));
    }

    #[test]
    fn test_rejects_runtime_has_inputs() {
        let mut builder = EthIRBuilder::new();

        let mut init_func = builder.begin_function();
        let mut init_bb = init_func.begin_basic_block();
        init_bb.add_operation(Operation::Stop(()));
        let init_bb_id = init_bb.finish(Control::LastOpTerminates).unwrap();
        let init_func_id = init_func.finish(init_bb_id);

        let mut main_func = builder.begin_function();
        let input1 = main_func.new_local();
        let input2 = main_func.new_local();
        let input3 = main_func.new_local();
        let mut main_bb = main_func.begin_basic_block();
        main_bb.set_inputs(&[input1, input2, input3]);
        main_bb.add_operation(Operation::Stop(()));
        let main_bb_id = main_bb.finish(Control::LastOpTerminates).unwrap();
        let main_func_id = main_func.finish(main_bb_id);

        let program = builder.build(init_func_id, Some(main_func_id));

        assert_eq!(legalize(&program).unwrap_err(), LegalizerError::RuntimeHasInputs(3));
    }

    #[test]
    fn test_rejects_terminator_not_last() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::Stop(()));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::TerminatorNotLast(bb_id, OperationIdx::new(0))
        );
    }

    #[test]
    fn test_rejects_terminator_control_mismatch() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let next_bb_id = BasicBlockId::new(1);
        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::ContinuesTo(next_bb_id)).unwrap();

        {
            let mut next_bb = func.begin_basic_block();
            next_bb.add_operation(Operation::Stop(()));
            next_bb.finish(Control::LastOpTerminates).unwrap();
        }

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::TerminatorControlMismatch(bb_id, OperationIdx::new(0))
        );
    }

    #[test]
    fn test_rejects_invalid_large_const_id() {
        let mut builder = EthIRBuilder::new();
        let valid_id = builder.alloc_u256(U256::from(42));
        assert_eq!(valid_id, LargeConstId::new(0));

        let mut func = builder.begin_function();
        let local = func.new_local();
        let invalid_id = LargeConstId::new(1);

        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::SetLargeConst(SetLargeConstData {
            sets: local,
            value: invalid_id,
        }));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::InvalidLargeConstId(invalid_id)
        );
    }

    #[test]
    fn test_rejects_invalid_segment_id() {
        let mut builder = EthIRBuilder::new();
        let valid_id = builder.push_data_bytes(&[0xde, 0xad, 0xbe, 0xef]);
        assert_eq!(valid_id, DataId::new(0));

        let mut func = builder.begin_function();
        let local = func.new_local();
        let invalid_id = DataId::new(1);

        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::SetDataOffset(SetDataOffsetData {
            sets: local,
            segment_id: invalid_id,
        }));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(legalize(&program).unwrap_err(), LegalizerError::InvalidSegmentId(invalid_id));
    }

    #[test]
    fn test_rejects_invalid_static_alloc_id() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();
        let local = func.new_local();
        let invalid_id = StaticAllocId::new(999);

        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::StaticAllocZeroed(StaticAllocData {
            size: 32,
            ptr_out: local,
            alloc_id: invalid_id,
        }));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::InvalidStaticAllocId(invalid_id)
        );
    }

    #[test]
    fn test_rejects_invalid_local_id() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let invalid_id = LocalId::new(0);
        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::SetSmallConst(SetSmallConstData {
            sets: invalid_id,
            value: 1,
        }));
        bb.add_operation(Operation::Stop(()));
        let bb_id = bb.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb_id);
        let program = builder.build(func_id, None);

        assert_eq!(legalize(&program).unwrap_err(), LegalizerError::InvalidLocalId(invalid_id));
    }

    #[test]
    fn test_rejects_shared_basic_block() {
        let mut builder = EthIRBuilder::new();

        let mut func_a = builder.begin_function();
        let mut bb_shared = func_a.begin_basic_block();
        bb_shared.add_operation(Operation::Stop(()));
        let bb_shared_id = bb_shared.finish(Control::LastOpTerminates).unwrap();
        let func_a_id = func_a.finish(bb_shared_id);

        let mut program = builder.build(func_a_id, None);

        let func_b_id = program.functions.push(sir_data::Function::new(bb_shared_id, 0));

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::SharedBasicBlock(bb_shared_id, func_a_id, func_b_id)
        );
    }

    #[test]
    fn test_rejects_overlapping_local_spans() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let local = func.new_local();

        let mut bb1 = func.begin_basic_block();
        bb1.add_operation(Operation::SetSmallConst(SetSmallConstData { sets: local, value: 1 }));
        bb1.set_outputs(&[local]);
        let bb1_id = bb1.finish(Control::ContinuesTo(BasicBlockId::new(1))).unwrap();

        let in2 = func.new_local();
        let mut bb2 = func.begin_basic_block();
        bb2.set_inputs(&[in2]);
        bb2.add_operation(Operation::Stop(()));
        bb2.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb1_id);
        let mut program = builder.build(func_id, None);

        let bb2_id = BasicBlockId::new(1);
        program.basic_blocks[bb2_id].inputs = program.basic_blocks[bb1_id].outputs;

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::OverlappingSpans(
                SpanSource::Outputs(bb1_id),
                SpanSource::Inputs(bb2_id)
            )
        );
    }

    #[test]
    fn test_rejects_overlapping_operation_spans() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let mut bb1 = func.begin_basic_block();
        bb1.add_operation(Operation::Stop(()));
        let bb1_id = bb1.finish(Control::LastOpTerminates).unwrap();

        let mut bb2 = func.begin_basic_block();
        bb2.add_operation(Operation::Stop(()));
        bb2.finish(Control::LastOpTerminates).unwrap();

        let func_id = func.finish(bb1_id);
        let mut program = builder.build(func_id, None);

        let bb2_id = BasicBlockId::new(1);
        program.basic_blocks[bb2_id].operations = program.basic_blocks[bb1_id].operations;

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::OverlappingSpans(
                SpanSource::Operations(bb1_id),
                SpanSource::Operations(bb2_id)
            )
        );
    }

    #[test]
    fn test_rejects_span_out_of_bounds() {
        let mut builder = EthIRBuilder::new();
        let mut func = builder.begin_function();

        let out_local = func.new_local();

        let mut bb = func.begin_basic_block();
        bb.add_operation(Operation::SetSmallConst(SetSmallConstData { sets: out_local, value: 1 }));
        bb.set_outputs(&[out_local]);
        let bb_id = bb.finish(Control::InternalReturn).unwrap();

        let func_id = func.finish(bb_id);
        let mut program = builder.build(func_id, None);

        program.locals.truncate(0);

        assert_eq!(
            legalize(&program).unwrap_err(),
            LegalizerError::SpanOutOfBounds(SpanSource::Outputs(bb_id))
        );
    }
}
