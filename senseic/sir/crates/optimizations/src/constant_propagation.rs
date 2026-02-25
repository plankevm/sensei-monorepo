use alloy_primitives::{I256, U256, U512};
use sir_analyses::{DefUse, UseKind, compute_def_use, compute_predecessors};
use sir_data::{operation::*, *};
use std::cmp::{Ordering, PartialOrd};

pub struct SCCPAnalysis {
    lattice: IndexVec<LocalId, LatticeValue>,
    pub reachable: DenseIndexSet<BasicBlockId>,
    cfg_worklist: Vec<BasicBlockId>,
    values_worklist: Vec<LocalId>,
    predecessors: IndexVec<BasicBlockId, Vec<BasicBlockId>>,
}

impl SCCPAnalysis {
    pub fn new() -> Self {
        Self {
            lattice: IndexVec::new(),
            reachable: DenseIndexSet::new(),
            cfg_worklist: Vec::new(),
            values_worklist: Vec::new(),
            predecessors: IndexVec::new(),
        }
    }

    pub fn reset(&mut self, program: &EthIRProgram) {
        self.lattice.clear();
        self.lattice.resize(program.next_free_local_id.idx(), LatticeValue::Unknown);
        self.reachable.clear();
        self.cfg_worklist.clear();
        self.values_worklist.clear();
        compute_predecessors(program, &mut self.predecessors);
        self.init_state(program);
    }

    fn init_state(&mut self, program: &EthIRProgram) {
        for func in program.functions_iter() {
            let entry_id = func.entry().id();
            self.reachable.add(entry_id);
            self.cfg_worklist.push(entry_id);
            for &input in func.entry().inputs() {
                self.lattice[input] = LatticeValue::Overdefined;
            }
        }
    }

    pub fn analysis(&mut self, program: &EthIRProgram, uses: &mut DefUse) {
        self.reset(program);
        compute_def_use(program, uses);
        while let Some(bb_id) = self.cfg_worklist.pop() {
            self.process_block(program, bb_id, uses);
        }
    }

    pub fn apply(&self, program: &mut EthIRProgram) {
        for bb_id in program.basic_blocks.iter_idx() {
            if self.reachable.contains(bb_id) {
                self.rewrite_constants(program, bb_id);
                self.simplify_control(program, bb_id);
            }
        }
    }

    #[cfg(test)]
    fn get_lattice(&self) -> &IndexVec<LocalId, LatticeValue> {
        &self.lattice
    }

    fn rewrite_constants(&self, program: &mut EthIRProgram, bb_id: BasicBlockId) {
        let ops = program.basic_blocks[bb_id].operations;
        for op_idx in ops.iter() {
            let op = &program.operations[op_idx];
            let mut outs = op.outputs(program).iter();
            let out = outs.next().copied();
            debug_assert!(
                outs.next().is_none(),
                "no operation with several outputs should be rewritable"
            );

            let Some(out) = out else { continue };
            let LatticeValue::Const(cv) = self.lattice[out] else { continue };
            // Heuristic: Only inline constants that fit in 4 bytes or less.
            let new_op = match u32::try_from(cv) {
                Ok(value) => Operation::SetSmallConst(SetSmallConstData { sets: out, value }),
                Err(_) => continue,
            };
            program.operations[op_idx] = new_op;
        }
    }

    fn simplify_control(&self, program: &mut EthIRProgram, bb_id: BasicBlockId) {
        match &program.basic_blocks[bb_id].control {
            Control::Branches(branch) => {
                if let Some(cv) = self.const_u256(branch.condition) {
                    let target =
                        if cv.is_zero() { branch.zero_target } else { branch.non_zero_target };
                    program.basic_blocks[bb_id].control = Control::ContinuesTo(target);
                }
            }
            Control::Switch(switch) => {
                if let Some(val) = self.const_u256(switch.condition) {
                    let target = program.cases[switch.cases]
                        .iter(program)
                        .find(|(case_val, _)| val == *case_val)
                        .map(|(_, t)| t)
                        .or(switch.fallback)
                        .expect("illegal behavior: switch has no matching case and no fallback");

                    program.basic_blocks[bb_id].control = Control::ContinuesTo(target);
                }
            }
            _ => {}
        }
    }

    fn process_operations(&mut self, program: &EthIRProgram, bb_id: BasicBlockId) {
        for op_view in program.block(bb_id).operations() {
            let op = op_view.op();
            if let Some((local, value)) = constant(&op, &program.large_consts) {
                // Will always be constant here, but detects whether it changed.
                if self.lattice[local].meet(value) {
                    self.values_worklist.push(local);
                }
                continue;
            }

            if let Some((out, value)) = self.evaluate(program, &op) {
                if self.lattice[out].meet(LatticeValue::Const(value)) {
                    self.values_worklist.push(out);
                }
                continue;
            }

            // Any operation that isn't const or evaluates to a constant is overdefined (aka
            // bottom).
            for &out in op_view.outputs() {
                if self.lattice[out].meet(LatticeValue::Overdefined) {
                    self.values_worklist.push(out);
                }
            }
        }
    }

    fn process_control(&mut self, program: &EthIRProgram, bb_id: BasicBlockId) {
        for succ in program.block(bb_id).successors() {
            if self.is_edge_reachable(program, bb_id, succ) {
                self.mark_reachable(program, bb_id, succ);
            }
        }
    }

    fn is_edge_reachable(
        &self,
        program: &EthIRProgram,
        from: BasicBlockId,
        to: BasicBlockId,
    ) -> bool {
        match program.block(from).control() {
            ControlView::ContinuesTo(target) => target == to,
            ControlView::Branches { condition, zero_target, non_zero_target } => {
                match self.lattice[condition] {
                    LatticeValue::Const(cv) => {
                        if cv.is_zero() {
                            to == zero_target
                        } else {
                            to == non_zero_target
                        }
                    }
                    // Some more constants may be guaranteed non-zero (e.g. number,
                    // runtime_start_offset), not including conservatively.
                    LatticeValue::EvmConst(
                        EvmConstKind::Address
                        | EvmConstKind::Origin
                        | EvmConstKind::Caller
                        | EvmConstKind::Timestamp
                        | EvmConstKind::GasLimit
                        | EvmConstKind::ChainId,
                    ) => to == non_zero_target,
                    either => {
                        debug_assert!(either != LatticeValue::Unknown);
                        to == zero_target || to == non_zero_target
                    }
                }
            }
            ControlView::Switch(switch) => self.const_u256(switch.condition()).is_none_or(|val| {
                let target = switch
                    .cases()
                    .find(|(case_val, _)| val == *case_val)
                    .map(|(_, target)| target)
                    .or(switch.fallback())
                    .expect("illegal behavior: switch has no matching case and no fallback");
                to == target
            }),
            ControlView::LastOpTerminates | ControlView::InternalReturn => false,
        }
    }

    fn process_values(&mut self, program: &EthIRProgram, uses: &DefUse) {
        while let Some(value) = self.values_worklist.pop() {
            for use_loc in &uses[value] {
                if !self.reachable.contains(use_loc.block_id) {
                    continue;
                }
                self.process_use(program, use_loc.block_id, use_loc.kind, value);
            }
        }
    }

    fn process_use(
        &mut self,
        program: &EthIRProgram,
        block_id: BasicBlockId,
        kind: UseKind,
        value: LocalId,
    ) {
        match kind {
            UseKind::Operation(op_id) => {
                let outputs = program.operations[op_id].outputs(program);
                if outputs.iter().all(|o| matches!(self.lattice[*o], LatticeValue::Overdefined)) {
                    return;
                }

                if let Some((out, value)) = self.evaluate(program, &program.operations[op_id]) {
                    if self.lattice[out].meet(LatticeValue::Const(value)) {
                        self.values_worklist.push(out);
                    }
                } else {
                    for &out in outputs {
                        if self.lattice[out].meet(LatticeValue::Overdefined) {
                            self.values_worklist.push(out);
                        }
                    }
                }
            }
            UseKind::Control => {
                self.process_control(program, block_id);
            }
            UseKind::BlockOutput => {
                let block = program.block(block_id);
                let idx = block
                    .outputs()
                    .iter()
                    .position(|&o| o == value)
                    .expect("value should be in outputs");
                for succ in block.successors() {
                    if !self.is_edge_reachable(program, block_id, succ) {
                        continue;
                    }
                    self.flow_single_output_to(program, block_id, succ, idx);
                }
            }
        }
    }

    fn process_block(&mut self, program: &EthIRProgram, bb_id: BasicBlockId, uses: &DefUse) {
        self.process_operations(program, bb_id);
        self.process_control(program, bb_id);
        self.process_values(program, uses);
    }

    fn mark_reachable(&mut self, program: &EthIRProgram, from: BasicBlockId, to: BasicBlockId) {
        if !self.reachable.contains(to) {
            self.reachable.add(to);
            self.cfg_worklist.push(to);
            self.flow_outputs_to(program, from, to);
        }
    }

    fn flow_outputs_to(&mut self, program: &EthIRProgram, from: BasicBlockId, to: BasicBlockId) {
        let from_outputs = program.block(from).outputs();
        let to_inputs = program.block(to).inputs();
        for (&output, &input) in from_outputs.iter().zip(to_inputs) {
            let value = self.lattice[output];
            if self.lattice[input].meet(value) {
                self.values_worklist.push(input);
            }
        }
    }

    fn flow_single_output_to(
        &mut self,
        program: &EthIRProgram,
        from: BasicBlockId,
        to: BasicBlockId,
        idx: usize,
    ) {
        let output = program.block(from).outputs()[idx];
        let input = program.block(to).inputs()[idx];

        let value = self.lattice[output];
        if self.lattice[input].meet(value) {
            self.values_worklist.push(input);
        }
    }

    // TODO: (worth?) A minor optimization is to skip the evaluation if output is Overdefined
    fn evaluate(&self, program: &EthIRProgram, op: &Operation) -> Option<(LocalId, U256)> {
        match op {
            Operation::Add(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, U256::wrapping_add)
            }
            Operation::Mul(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, U256::wrapping_mul)
            }
            Operation::Sub(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, U256::wrapping_sub)
            }
            Operation::Div(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| va.checked_div(vb).unwrap_or(U256::ZERO))
            }
            Operation::SDiv(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| {
                    let sa = I256::from_raw(va);
                    let sb = I256::from_raw(vb);
                    sa.checked_div(sb)
                        .unwrap_or_else(|| if sb.is_zero() { I256::ZERO } else { sa })
                        .into_raw()
                })
            }
            Operation::Mod(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| va.checked_rem(vb).unwrap_or(U256::ZERO))
            }
            Operation::SMod(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| {
                    let sa = I256::from_raw(va);
                    let sb = I256::from_raw(vb);
                    sa.checked_rem(sb).unwrap_or(I256::ZERO).into_raw()
                })
            }
            Operation::AddMod(AllocatedIns { ins_start, outs: [out] }) => {
                let a = program.locals[*ins_start];
                let b = program.locals[*ins_start + 1];
                let n = program.locals[*ins_start + 2];

                self.const_u256(a).and_then(|va| self.const_u256(b).map(|vb| (va, vb))).and_then(
                    |(va, vb)| {
                        self.const_u256(n).map(|vn| {
                            let result = if vn.is_zero() {
                                U256::ZERO
                            } else {
                                let sum = U512::from(va) + U512::from(vb);
                                U256::from(sum % U512::from(vn))
                            };
                            (*out, result)
                        })
                    },
                )
            }
            Operation::MulMod(AllocatedIns { ins_start, outs: [out] }) => {
                let a = program.locals[*ins_start];
                let b = program.locals[*ins_start + 1];
                let n = program.locals[*ins_start + 2];

                let va = self.const_u256(a)?;
                let vb = self.const_u256(b)?;
                let vn = self.const_u256(n)?;
                let result = if vn.is_zero() {
                    U256::ZERO
                } else {
                    let prod = U512::from(va) * U512::from(vb);
                    U256::from(prod % U512::from(vn))
                };
                Some((*out, result))
            }
            Operation::Exp(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| va.pow(vb))
            }
            Operation::SignExtend(InlineOperands { ins: [b, x], outs: [out] }) => {
                self.eval_binary(b, x, out, |vb, vx| {
                    if vb >= U256::from(31) {
                        vx
                    } else {
                        let sign_bit_pos = (vb.to::<usize>() + 1) * 8 - 1;
                        let sign_bit_mask = U256::ONE << sign_bit_pos;

                        if (vx & sign_bit_mask) != U256::ZERO {
                            vx | (U256::MAX << (sign_bit_pos + 1))
                        } else {
                            vx & ((U256::ONE << (sign_bit_pos + 1)) - U256::ONE)
                        }
                    }
                })
            }
            Operation::Lt(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| U256::from(va < vb))
            }
            Operation::Gt(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| U256::from(va > vb))
            }
            Operation::SLt(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| {
                    U256::from(I256::from_raw(va) < I256::from_raw(vb))
                })
            }
            Operation::SGt(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| {
                    U256::from(I256::from_raw(va) > I256::from_raw(vb))
                })
            }
            Operation::Eq(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| U256::from(va == vb))
            }
            Operation::And(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| va & vb)
            }
            Operation::Or(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| va | vb)
            }
            Operation::Xor(InlineOperands { ins: [a, b], outs: [out] }) => {
                self.eval_binary(a, b, out, |va, vb| va ^ vb)
            }
            Operation::Byte(InlineOperands { ins: [i, x], outs: [out] }) => {
                self.eval_binary(i, x, out, |vi, vx| {
                    if vi >= U256::from(32) {
                        U256::ZERO
                    } else {
                        U256::from(vx.byte(31 - vi.to::<usize>()))
                    }
                })
            }
            Operation::Shl(InlineOperands { ins: [shift, value], outs: [out] }) => {
                self.eval_binary(shift, value, out, |vshift, vvalue| vvalue << vshift)
            }
            Operation::Shr(InlineOperands { ins: [shift, value], outs: [out] }) => {
                self.eval_binary(shift, value, out, |vshift, vvalue| vvalue >> vshift)
            }
            Operation::Sar(InlineOperands { ins: [shift, value], outs: [out] }) => self
                .eval_binary(shift, value, out, |vshift, vvalue| {
                    if vshift >= U256::from(256) {
                        if vvalue.bit(255) { U256::MAX } else { U256::ZERO }
                    } else {
                        I256::from_raw(vvalue).asr(vshift.to::<usize>()).into_raw()
                    }
                }),
            Operation::Not(InlineOperands { ins: [a], outs: [out] }) => {
                let va = self.const_u256(*a)?;
                Some((*out, !va))
            }
            Operation::IsZero(InlineOperands { ins: [a], outs: [out] }) => {
                let va = self.const_u256(*a)?;
                Some((*out, U256::from(va.is_zero())))
            }
            _ => None,
        }
    }

    fn const_u256(&self, local: LocalId) -> Option<U256> {
        match self.lattice[local] {
            LatticeValue::Const(cv) => Some(cv),
            _ => None,
        }
    }

    fn eval_binary(
        &self,
        a: &LocalId,
        b: &LocalId,
        out: &LocalId,
        op: impl FnOnce(U256, U256) -> U256,
    ) -> Option<(LocalId, U256)> {
        let (va, vb) = self.binary_const_u256(*a, *b)?;
        Some((*out, op(va, vb)))
    }

    fn binary_const_u256(&self, a: LocalId, b: LocalId) -> Option<(U256, U256)> {
        Some((self.const_u256(a)?, self.const_u256(b)?))
    }
}

#[derive(Clone, Eq, PartialEq, Copy, Debug)]
enum LatticeValue {
    Unknown,
    Const(U256),
    EvmConst(EvmConstKind),
    Overdefined,
}

impl PartialOrd for LatticeValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (x, y) if x == y => Some(Ordering::Equal),
            (Self::Unknown, _) => Some(Ordering::Greater),
            (Self::Overdefined, _) => Some(Ordering::Less),
            (_, Self::Unknown) => Some(Ordering::Less),
            (_, Self::Overdefined) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl LatticeValue {
    /// Returns whether the value was updated.
    fn meet(&mut self, other: Self) -> bool {
        let met = match (*self).partial_cmp(&other) {
            None => LatticeValue::Overdefined,
            Some(Ordering::Less | Ordering::Equal) => *self,
            Some(Ordering::Greater) => other,
        };
        let changed = met != *self;
        *self = met;
        changed
    }
}

macro_rules! define_consts {
    ($($name:ident),* $(,)?) => {
        #[derive(PartialEq, Clone, Eq, Hash, Copy, Debug)]
        enum EvmConstKind {
            $($name),*
        }

        fn constant(op: &Operation, large_consts: &IndexVec<LargeConstId, U256>) -> Option<(LocalId, LatticeValue)> {
            match op {
                $(
                    Operation::$name(InlineOperands { ins: [], outs: [out] }) => {
                        Some((*out, LatticeValue::EvmConst(EvmConstKind::$name)))
                    }
                )*
                Operation::SetSmallConst(SetSmallConstData { value, sets }) => {
                    Some((*sets, LatticeValue::Const(U256::from(*value))))
                }
                Operation::SetLargeConst(SetLargeConstData { value, sets }) => {
                    Some((*sets, LatticeValue::Const(large_consts[*value])))
                }
                _ => None
            }
        }
    };
}

define_consts!(
    Address,
    Origin,
    Caller,
    CallValue,
    CallDataSize,
    CodeSize,
    GasPrice,
    Coinbase,
    Timestamp,
    Number,
    Difficulty,
    GasLimit,
    ChainId,
    BaseFee,
    BlobBaseFee,
    RuntimeStartOffset,
    InitEndOffset,
    RuntimeLength,
);

#[cfg(test)]
mod tests {
    use super::*;
    use sir_parser::{EmitConfig, parse_or_panic};
    use sir_test_utils::assert_trim_strings_eq_with_diff;

    fn run_const_prop(source: &str) -> (String, IndexVec<LocalId, LatticeValue>) {
        let mut ir = parse_or_panic(source, EmitConfig::init_only());
        let mut uses = DefUse::new();
        let mut sccp = SCCPAnalysis::new();
        sccp.analysis(&ir, &mut uses);
        let lattice = sccp.get_lattice().clone();
        sccp.apply(&mut ir);
        (sir_data::display_program(&ir), lattice)
    }

    #[test]
    fn test_block_inputs_propagate_only_when_predecessors_agree() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry x {
                    => x ? @block_a : @block_b
                }
                block_a -> same_a diff_a {
                    same_a = const 42
                    diff_a = const 10
                    => @merge
                }
                block_b -> same_b diff_b {
                    same_b = const 42
                    diff_b = const 20
                    => @merge
                }
                merge input_same input_diff {
                    result1 = add input_same input_same
                    result2 = add input_same input_diff
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 {
        => $0 ? @2 : @3
    }

    @2 -> $1 $2 {
        $1 = const 0x2a
        $2 = const 0xa
        => @4
    }

    @3 -> $3 $4 {
        $3 = const 0x2a
        $4 = const 0x14
        => @4
    }

    @4 $5 $6 {
        $7 = const 0x54
        $8 = add $5 $6
        stop
    }
        "#;

        let (actual, lattice) = run_const_prop(input);
        assert_trim_strings_eq_with_diff(
            &actual,
            expected,
            "block inputs propagate only when predecessors agree",
        );

        assert_eq!(lattice[LocalId::new(6)], LatticeValue::Overdefined);
        assert_eq!(lattice[LocalId::new(8)], LatticeValue::Overdefined);
    }

    #[test]
    fn test_branch_zero_takes_false() {
        let input = r#"
            fn init:
                entry {
                    cond = const 0
                    => cond ? @if_true : @if_false
                }
                if_true { stop }
                if_false { stop }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x0
        => @2
    }

    @1 {
        stop
    }

    @2 {
        stop
    }
        "#;

        let (actual, _) = run_const_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "branch zero takes false");
    }

    #[test]
    fn test_branch_nonzero_takes_true() {
        let input = r#"
            fn init:
                entry {
                    cond = large_const 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6
                    => cond ? @if_true : @if_false
                }
                if_true { stop }
                if_false { stop }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = large_const 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6
        => @1
    }

    @1 {
        stop
    }

    @2 {
        stop
    }
        "#;

        let (actual, _) = run_const_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "branch nonzero takes true");
    }

    #[test]
    fn test_switch_with_folded_condition() {
        let input = r#"
            fn init:
                entry {
                    a = const 7
                    b = const 5
                    cond = gt a b
                    switch cond {
                        1 => @matched
                        default => @fallback
                    }
                }
                matched { stop }
                fallback { stop }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x7
        $1 = const 0x5
        $2 = const 0x1
        => @1
    }

    @1 {
        stop
    }

    @2 {
        stop
    }
        "#;

        let (actual, _) = run_const_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "switch with folded condition");
    }

    #[test]
    fn test_switch_no_match_takes_default() {
        let input = r#"
            fn init:
                entry {
                    a = const 17
                    b = const 5
                    cond = mod a b
                    switch cond {
                        5 => @matched
                        default => @fallback
                    }
                }
                matched { stop }
                fallback { stop }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x11
        $1 = const 0x5
        $2 = const 0x2
        => @2
    }

    @1 {
        stop
    }

    @2 {
        stop
    }
        "#;

        let (actual, _) = run_const_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "switch no match takes default");
    }

    #[test]
    fn test_internal_function_inputs_are_overdefined() {
        let input = r#"
            fn init:
                entry {
                    stop
                }

            fn helper:
                entry a -> a {
                    => @next
                }
                next v -> c {
                    c = const 0
                    => v ? @end : @next
                }
                end _1 {
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 -> $0 {
        => @2
    }

    @2 $1 -> $2 {
        $2 = const 0x0
        => $1 ? @3 : @2
    }

    @3 $3 {
        stop
    }
        "#;

        let (actual, lattice) = run_const_prop(input);
        assert_trim_strings_eq_with_diff(
            &actual,
            expected,
            "internal function inputs remain overdefined and don't propagate constants incorrectly",
        );

        assert_eq!(lattice[LocalId::new(0)], LatticeValue::Overdefined);
        assert_eq!(lattice[LocalId::new(1)], LatticeValue::Overdefined);
    }

    #[test]
    fn test_constant_evaluation() {
        let input = r#"
            fn init:
                entry {
                    zero = const 0                  // $0
                    one = const 1                   // $1
                    three = const 3                 // $2
                    seven = const 7                 // $3
                    _0x80 = const 0x80              // $4
                    _0xff = const 0xff              // $5
                    _32 = const 32                  // $6
                    _256 = const 256                // $7

                    neg1 = large_const 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff   // $8
                    neg7 = large_const 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9   // $9
                    int_max = large_const 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff // $10
                    int_min = large_const 0x8000000000000000000000000000000000000000000000000000000000000000 // $11

                    a = add int_max one             // $12
                    b = sub int_min one             // $13
                    mul_wrap = mul int_max int_max   // $14
                    d = div neg1 neg1               // $15
                    e = mod a seven                 // $16
                    f = sdiv neg7 three             // $17
                    g = smod neg7 three             // $18
                    ab_diff = sub a b               // $19

                    smod_special = smod int_min neg1 // $20

                    div_by_zero = div seven zero    // $21
                    sdiv_by_zero = sdiv seven zero  // $22
                    mod_by_zero = mod seven zero    // $23
                    smod_by_zero = smod seven zero  // $24

                    h = addmod neg1 one seven       // $25
                    i = mulmod int_max int_max seven // $26
                    addmod_zero_n = addmod one one zero // $27
                    mulmod_zero_n = mulmod one one zero // $28

                    j = exp zero zero               // $29
                    exp_wrap = exp neg1 _32         // $30

                    c = sdiv int_min int_max        // $31
                    sdiv_overflow = sdiv int_min neg1 // $32
                    fg_diff = sub g f               // $33
                    sar_pos_256 = sar _256 b        // $34
                    overflow_xor_a = xor sdiv_overflow a // $35

                    gt_unsigned = gt a b            // $36
                    sgt_signed = sgt a b            // $37
                    lt_unsigned = lt a b            // $38
                    slt_signed = slt a b            // $39
                    o = iszero neg1                 // $40
                    iszero_zero = iszero zero       // $41

                    eq_computed = eq c g            // $42
                    q = or int_min neg1             // $43
                    s = not zero                    // $44
                    qs_xor = xor q s                // $45
                    r = not f                       // $46

                    t = shl _256 one                // $47
                    u = shr _256 neg1               // $48
                    v = sar _0xff neg1              // $49
                    sar_256 = sar _256 neg1         // $50
                    vsar_xor = xor v sar_256        // $51

                    w = byte _32 _0x80              // $52
                    byte_msb = byte zero neg1       // $53

                    x = signextend zero _0x80       // $54
                    x2 = byte zero x                // $55
                    signext_noop = signextend _32 _0x80 // $56

                    z0 = add d j                    // $57
                    z1 = and s _0xff                // $58

                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x0
        $1 = const 0x1
        $2 = const 0x3
        $3 = const 0x7
        $4 = const 0x80
        $5 = const 0xff
        $6 = const 0x20
        $7 = const 0x100
        $8 = large_const 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
        $9 = large_const 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9
        $10 = large_const 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
        $11 = large_const 0x8000000000000000000000000000000000000000000000000000000000000000
        $12 = add $10 $1
        $13 = sub $11 $1
        $14 = const 0x1
        $15 = const 0x1
        $16 = const 0x1
        $17 = sdiv $9 $2
        $18 = smod $9 $2
        $19 = const 0x1
        $20 = const 0x0
        $21 = const 0x0
        $22 = const 0x0
        $23 = const 0x0
        $24 = const 0x0
        $25 = const 0x2
        $26 = const 0x0
        $27 = const 0x0
        $28 = const 0x0
        $29 = const 0x1
        $30 = const 0x1
        $31 = sdiv $11 $10
        $32 = sdiv $11 $8
        $33 = const 0x1
        $34 = const 0x0
        $35 = const 0x0
        $36 = const 0x1
        $37 = const 0x0
        $38 = const 0x0
        $39 = const 0x1
        $40 = const 0x0
        $41 = const 0x1
        $42 = const 0x1
        $43 = or $11 $8
        $44 = not $0
        $45 = const 0x0
        $46 = const 0x1
        $47 = const 0x0
        $48 = const 0x0
        $49 = sar $5 $8
        $50 = sar $7 $8
        $51 = const 0x0
        $52 = const 0x0
        $53 = const 0xff
        $54 = signextend $0 $4
        $55 = const 0xff
        $56 = const 0x80
        $57 = const 0x2
        $58 = const 0xff
        stop
    }
        "#;

        let (actual, lattice) = run_const_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "constant evaluation");

        let neg1 = U256::from_str_radix(
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        let int_max = U256::from_str_radix(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        let int_min = U256::from_str_radix(
            "8000000000000000000000000000000000000000000000000000000000000000",
            16,
        )
        .unwrap();
        let neg2 = U256::from_str_radix(
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
            16,
        )
        .unwrap();

        assert_eq!(lattice[LocalId::new(12)], LatticeValue::Const(int_min));
        assert_eq!(lattice[LocalId::new(13)], LatticeValue::Const(int_max));
        assert_eq!(lattice[LocalId::new(17)], LatticeValue::Const(neg2));
        assert_eq!(lattice[LocalId::new(18)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(31)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(32)], LatticeValue::Const(int_min));
        assert_eq!(lattice[LocalId::new(43)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(44)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(49)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(50)], LatticeValue::Const(neg1));
        assert_eq!(
            lattice[LocalId::new(54)],
            LatticeValue::Const(
                U256::from_str_radix(
                    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80",
                    16
                )
                .unwrap()
            )
        );
    }

    #[test]
    fn test_additional_cases() {
        let input = r#"
            fn init:
                entry {
                    zero = const 0                  // $0
                    one = const 1                   // $1
                    two = const 2                   // $2
                    _31 = const 31                  // $3
                    _32 = const 32                  // $4
                    _128 = const 128                // $5
                    _255 = const 255                // $6
                    _0x1_0000_0000 = large_const 0x0000000000000000000000000000000000000000000000000000000100000000 // $7
                    neg1 = large_const 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff   // $8
                    int_max = large_const 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff // $9
                    int_min = large_const 0x8000000000000000000000000000000000000000000000000000000000000000 // $10

                    a = add int_max int_max         // $11
                    b = sub int_min int_min         // $12

                    and_identity = and a neg1        // $13
                    or_identity = or b zero         // $14

                    shl_zero = shl zero a           // $15
                    shr_zero = shr zero b           // $16
                    sar_zero = sar zero neg1         // $17

                    exp_zero_large = exp zero int_max // $18
                    exp_neg1_odd = exp neg1 _255    // $19

                    sar_255_neg = sar _255 neg1      // $20
                    sar_255_pos = sar _255 int_max  // $21

                    byte_lsb = byte _31 neg1         // $22
                    signext_31 = signextend _31 int_min // $23

                    slt_zero_neg1 = slt zero neg1    // $24

                    sdiv_zero_x = sdiv zero int_max // $25
                    smod_x_one = smod neg1 one       // $26

                    shl_255 = shl _255 one          // $27
                    shr_255 = shr _255 neg1          // $28

                    signext_pos = signextend zero one // $29

                    addmod_one = addmod neg1 neg1 one // $30
                    mulmod_one = mulmod int_max int_max one // $31

                    sgt_neg1_zero = sgt neg1 zero    // $32

                    add_large = add _0x1_0000_0000 one // $33
                    mul_large = mul _0x1_0000_0000 _0x1_0000_0000 // $34
                    exp_large = exp _0x1_0000_0000 two // $35

                    shl_32 = shl _32 one            // $36
                    shl_128 = shl _128 one          // $37

                    shl_big = shl _128 _0x1_0000_0000        // $38
                    shr_big = shr _128 neg1                   // $39
                    sar_big_neg = sar _0x1_0000_0000 neg1    // $40
                    sar_big_pos = sar _128 int_max            // $41

                    sub_underflow = sub zero one              // $42

                    signext_0_ff = signextend zero _255       // $43
                    signext_1_trunc = signextend one _0x1_0000_0000 // $44

                    exp_identity = exp int_max one            // $45
                    exp_one_large = exp one _0x1_0000_0000    // $46
                    exp_full_wrap = exp two _255              // $47

                    sar_1_intmin = sar one int_min            // $48

                    exp_x_zero = exp neg1 zero               // $49
                    eq_unequal = eq one two                   // $50
                    and_zero = and int_min zero               // $51
                    xor_identity = xor int_min zero           // $52
                    lt_self = lt neg1 neg1                    // $53
                    gt_self = gt neg1 neg1                    // $54

                    stop
                }
        "#;

        let (_, lattice) = run_const_prop(input);

        let neg2 = U256::from_str_radix(
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
            16,
        )
        .unwrap();
        let neg1 = U256::from_str_radix(
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        let int_min = U256::from_str_radix(
            "8000000000000000000000000000000000000000000000000000000000000000",
            16,
        )
        .unwrap();
        let int_max = U256::from_str_radix(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();

        assert_eq!(lattice[LocalId::new(11)], LatticeValue::Const(neg2));
        assert_eq!(lattice[LocalId::new(12)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(13)], LatticeValue::Const(neg2));
        assert_eq!(lattice[LocalId::new(14)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(15)], LatticeValue::Const(neg2));
        assert_eq!(lattice[LocalId::new(16)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(17)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(18)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(19)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(20)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(21)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(22)], LatticeValue::Const(U256::from(0xff)));
        assert_eq!(lattice[LocalId::new(23)], LatticeValue::Const(int_min));
        assert_eq!(lattice[LocalId::new(24)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(25)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(26)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(27)], LatticeValue::Const(U256::from(1) << 255));
        assert_eq!(lattice[LocalId::new(28)], LatticeValue::Const(U256::ONE));
        assert_eq!(lattice[LocalId::new(29)], LatticeValue::Const(U256::ONE));
        assert_eq!(lattice[LocalId::new(30)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(31)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(32)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(33)], LatticeValue::Const(U256::from(0x100000001u64)));
        assert_eq!(lattice[LocalId::new(34)], LatticeValue::Const(U256::from(1u128 << 64)));
        assert_eq!(lattice[LocalId::new(35)], LatticeValue::Const(U256::from(1u128 << 64)));
        assert_eq!(lattice[LocalId::new(36)], LatticeValue::Const(U256::from(1u64 << 32)));
        assert_eq!(lattice[LocalId::new(37)], LatticeValue::Const(U256::from(1) << 128));
        assert_eq!(lattice[LocalId::new(38)], LatticeValue::Const(U256::from(1) << 160));
        assert_eq!(
            lattice[LocalId::new(39)],
            LatticeValue::Const((U256::from(1) << 128) - U256::from(1))
        );
        assert_eq!(lattice[LocalId::new(40)], LatticeValue::Const(neg1));
        assert_eq!(
            lattice[LocalId::new(41)],
            LatticeValue::Const((U256::from(1) << 127) - U256::from(1))
        );
        assert_eq!(lattice[LocalId::new(42)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(43)], LatticeValue::Const(neg1));
        assert_eq!(lattice[LocalId::new(44)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(45)], LatticeValue::Const(int_max));
        assert_eq!(lattice[LocalId::new(46)], LatticeValue::Const(U256::ONE));
        assert_eq!(lattice[LocalId::new(47)], LatticeValue::Const(int_min));
        assert_eq!(lattice[LocalId::new(48)], LatticeValue::Const(U256::from(3) << 254));
        assert_eq!(lattice[LocalId::new(49)], LatticeValue::Const(U256::ONE));
        assert_eq!(lattice[LocalId::new(50)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(51)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(52)], LatticeValue::Const(int_min));
        assert_eq!(lattice[LocalId::new(53)], LatticeValue::Const(U256::ZERO));
        assert_eq!(lattice[LocalId::new(54)], LatticeValue::Const(U256::ZERO));
    }

    #[test]
    fn test_evm_const_branch() {
        let input = r#"
            fn init:
                entry {                             // @0
                    a = address
                    => a ? @if_true : @if_false
                }
                if_true { stop }                    // @1
                if_false { stop }                   // @2
        "#;

        let ir = parse_or_panic(input, EmitConfig::init_only());
        let mut uses = DefUse::new();
        let mut sccp = SCCPAnalysis::new();
        sccp.analysis(&ir, &mut uses);

        assert!(sccp.reachable.contains(BasicBlockId::new(1)));
        assert!(!sccp.reachable.contains(BasicBlockId::new(2)));
    }

    #[test]
    fn test_evm_const_meet() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry x {                          // x = $0
                    => x ? @block_a : @block_b
                }
                block_a -> same_a diff_a {
                    same_a = address                // $1
                    diff_a = address                // $2
                    => @merge
                }
                block_b -> same_b diff_b {
                    same_b = address                // $3
                    diff_b = caller                 // $4
                    => @merge
                }
                merge same_input diff_input {       // $5, $6
                    // TODO: same_input is EvmConst(Address) from both predecessors,
                    // so eq(x, x) could fold to 1 if we tracked EvmConst identity.
                    eq_same = eq same_input same_input   // $7
                    stop
                }
        "#;

        let ir = parse_or_panic(input, EmitConfig::init_only());
        let mut uses = DefUse::new();
        let mut sccp = SCCPAnalysis::new();
        sccp.analysis(&ir, &mut uses);
        let lattice = sccp.get_lattice();

        assert_eq!(lattice[LocalId::new(5)], LatticeValue::EvmConst(EvmConstKind::Address));
        assert_eq!(lattice[LocalId::new(6)], LatticeValue::Overdefined);
        assert_eq!(lattice[LocalId::new(7)], LatticeValue::Overdefined);
    }

    #[test]
    fn test_overdefined_input_makes_both_branch_targets_reachable() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry cond {
                    => cond ? @A : @B
                }
                A -> out_a {
                    out_a = const 1
                    => @C
                }
                B -> out_b {
                    out_b = const 0
                    => @C
                }
                C input_x {
                    => input_x ? @true_target : @false_target
                }
                true_target { stop }
                false_target { stop }
        "#;

        let expected_ir = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 {
        => $0 ? @2 : @3
    }

    @2 -> $1 {
        $1 = const 0x1
        => @4
    }

    @3 -> $2 {
        $2 = const 0x0
        => @4
    }

    @4 $3 {
        => $3 ? @5 : @6
    }

    @5 {
        stop
    }

    @6 {
        stop
    }
        "#;

        let ir = parse_or_panic(input, EmitConfig::init_only());
        assert_trim_strings_eq_with_diff(
            &sir_data::display_program(&ir),
            expected_ir,
            "overdefined input makes both branch targets reachable",
        );

        let mut uses = DefUse::new();
        let mut sccp = SCCPAnalysis::new();
        sccp.analysis(&ir, &mut uses);

        assert!(
            sccp.reachable.contains(BasicBlockId::new(5)),
            "true_target (@5) should be reachable"
        );
        assert!(
            sccp.reachable.contains(BasicBlockId::new(6)),
            "false_target (@6) should be reachable"
        );
    }

    #[test]
    fn test_block_output_use_propagates_overdefined_to_successor() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry x {
                    => x ? @A : @B
                }
                A -> val_a {
                    val_a = const 5
                    => @C
                }
                B -> val_b {
                    val_b = const 10
                    => @C
                }
                C pass_through -> pass_through {
                    => @D
                }
                D final_val {
                    stop
                }
        "#;

        let expected_ir = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)
    fn @1 -> entry @1  (outputs: 0)

Basic Blocks:
    @0 {
        stop
    }

    @1 $0 {
        => $0 ? @2 : @3
    }

    @2 -> $1 {
        $1 = const 0x5
        => @4
    }

    @3 -> $2 {
        $2 = const 0xa
        => @4
    }

    @4 $3 -> $3 {
        => @5
    }

    @5 $4 {
        stop
    }
        "#;

        let ir = parse_or_panic(input, EmitConfig::init_only());
        assert_trim_strings_eq_with_diff(
            &sir_data::display_program(&ir),
            expected_ir,
            "block output use propagates overdefined to successor",
        );

        let mut uses = DefUse::new();
        let mut sccp = SCCPAnalysis::new();
        sccp.analysis(&ir, &mut uses);
        let lattice = sccp.get_lattice();

        assert_eq!(
            lattice[LocalId::new(3)],
            LatticeValue::Overdefined,
            "pass_through ($3) should be overdefined"
        );
        assert_eq!(
            lattice[LocalId::new(4)],
            LatticeValue::Overdefined,
            "final_val ($4) should be overdefined"
        );
    }

    #[test]
    fn test_reset_clears_state_and_reinitializes() {
        let large_ir = parse_or_panic(
            r#"
            fn init:
                entry {
                    a = const 10
                    b = const 20
                    c = add a b
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let small_ir = parse_or_panic(
            r#"
            fn init:
                entry {
                    x = const 5
                    stop
                }
            "#,
            EmitConfig::init_only(),
        );

        let mut uses = DefUse::new();
        let mut sccp = SCCPAnalysis::new();
        sccp.analysis(&large_ir, &mut uses);
        assert_eq!(sccp.get_lattice()[LocalId::new(0)], LatticeValue::Const(U256::from(10)));
        assert_eq!(sccp.get_lattice()[LocalId::new(1)], LatticeValue::Const(U256::from(20)));
        assert_eq!(sccp.get_lattice()[LocalId::new(2)], LatticeValue::Const(U256::from(30)));

        sccp.analysis(&small_ir, &mut uses);
        let lattice = sccp.get_lattice();

        assert_eq!(lattice.len(), 1);
        assert_eq!(lattice[LocalId::new(0)], LatticeValue::Const(U256::from(5)));
    }
}
