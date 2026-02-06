use alloy_primitives::{I256, U256, U512};
use sir_analyses::{DefUse, UseLocation, compute_def_use, compute_predecessors};
use sir_data::{
    BasicBlockId, BasicBlockIdMarker, Control, DenseIndexSet, EthIRProgram, IndexVec,
    LargeConstIdMarker, LocalId, LocalIdMarker, Operation, X32, index_vec,
    operation::{AllocatedIns, InlineOperands, SetLargeConstData, SetSmallConstData},
};

pub fn run(program: &mut EthIRProgram) {
    let mut sccp = SCCPAnalysis::new(program);
    sccp.analysis();
    sccp.get_unreachable_blocks();
    sccp.apply();
}

pub struct SCCPAnalysis<'a> {
    program: &'a mut EthIRProgram,
    lattice: IndexVec<LocalIdMarker, LatticeValue>,
    reachable: IndexVec<BasicBlockIdMarker, bool>,
    cfg_worklist: Vec<BasicBlockId>,
    values_worklist: Vec<LocalId>,
    predecessors: IndexVec<BasicBlockIdMarker, Vec<BasicBlockId>>,
    uses: DefUse,
    unreachable_blocks: DenseIndexSet<BasicBlockIdMarker>,
}

impl<'a> SCCPAnalysis<'a> {
    pub fn new(program: &'a mut EthIRProgram) -> Self {
        let predecessors = compute_predecessors(program);
        let mut reachable = index_vec![false; program.basic_blocks.len()];
        let mut cfg_worklist = Vec::new();
        for func in program.functions.iter() {
            let entry = func.entry();
            reachable[entry] = true;
            cfg_worklist.push(entry);
        }
        let uses = compute_def_use(program);
        let num_values = program.next_free_local_id.idx();
        Self {
            program,
            lattice: index_vec![LatticeValue::Unknown; num_values],
            reachable,
            cfg_worklist,
            values_worklist: Vec::new(),
            predecessors,
            uses,
            unreachable_blocks: DenseIndexSet::new(),
        }
    }

    pub fn analysis(&mut self) {
        while let Some(bb_id) = self.cfg_worklist.pop() {
            self.process_block(bb_id);
        }
        for i in 0..self.program.basic_blocks.len() {
            let bb_id = BasicBlockId::new(i as u32);
            if !self.reachable[bb_id] {
                self.unreachable_blocks.add(bb_id);
            }
        }
    }

    pub fn apply(&mut self) {
        for i in 0..self.program.basic_blocks.len() {
            let bb_id = BasicBlockId::new(i as u32);
            if self.reachable[bb_id] {
                self.rewrite_constants(bb_id);
                self.simplify_control(bb_id);
            }
        }
    }

    pub fn get_unreachable_blocks(&self) -> &DenseIndexSet<BasicBlockIdMarker> {
        &self.unreachable_blocks
    }

    fn rewrite_constants(&mut self, bb_id: X32<BasicBlockIdMarker>) {
        let ops = self.program.basic_blocks[bb_id].operations;
        for op_idx in ops.iter() {
            let outputs = self.program.operations[op_idx].outputs(self.program);
            for out in outputs {
                if let LatticeValue::Const(cv) = &self.lattice[out] {
                    let new_op = match cv {
                        ConstValue::SmallConst(v) => {
                            Operation::SetSmallConst(SetSmallConstData { sets: out, value: *v })
                        }
                        ConstValue::LargeConst(v) => {
                            let id = self.program.large_consts.push(*v);
                            Operation::SetLargeConst(SetLargeConstData { sets: out, value: id })
                        }
                    };
                    self.program.operations[op_idx] = new_op;
                }
            }
        }
    }

    fn simplify_control(&mut self, bb_id: X32<BasicBlockIdMarker>) {
        match &self.program.basic_blocks[bb_id].control {
            Control::Branches(branch) => {
                if let Some(cv) = self.const_value(branch.condition) {
                    let target =
                        if cv.is_zero() { branch.zero_target } else { branch.non_zero_target };
                    self.program.basic_blocks[bb_id].control = Control::ContinuesTo(target);
                }
            }
            Control::Switch(switch) => {
                if let Some(val) = self.const_u256(switch.condition) {
                    let target = self.program.cases[switch.cases]
                        .iter(&self.program)
                        .find(|(case_val, _)| val == *case_val)
                        .map(|(_, t)| t)
                        .or(switch.fallback);

                    if let Some(t) = target {
                        self.program.basic_blocks[bb_id].control = Control::ContinuesTo(t);
                    }
                }
            }
            _ => {}
        }
    }

    fn process_inputs(&mut self, bb_id: X32<BasicBlockIdMarker>) {
        let bb = &self.program.basic_blocks[bb_id];
        for pred_id in &self.predecessors[bb_id] {
            if !self.reachable[*pred_id] {
                continue;
            }
            let pred_bb = &self.program.basic_blocks[*pred_id];
            for (i, &pred_output) in self.program.locals[pred_bb.outputs].iter().enumerate() {
                let pred_value = self.lattice[pred_output].clone();
                let input_local = self.program.locals[bb.inputs][i];
                if self.lattice[input_local].meet(pred_value) {
                    self.values_worklist.push(input_local);
                }
            }
        }
    }

    fn process_operations(&mut self, bb_id: X32<BasicBlockIdMarker>) {
        let bb = &self.program.basic_blocks[bb_id];
        for op in &self.program.operations[bb.operations] {
            constant(op, &self.program.large_consts, |local, value| {
                if self.lattice[local].meet(value) {
                    self.values_worklist.push(local);
                }
            });

            if let Some((out, result)) = self.evaluate(op) {
                let value = if let Ok(small) = u32::try_from(result) {
                    ConstValue::SmallConst(small)
                } else {
                    ConstValue::LargeConst(result)
                };
                if self.lattice[out].meet(LatticeValue::Const(value)) {
                    self.values_worklist.push(out);
                }
            }
        }
    }

    fn process_control(&mut self, bb_id: X32<BasicBlockIdMarker>) {
        match &self.program.basic_blocks[bb_id].control {
            Control::ContinuesTo(target) => {
                self.mark_reachable(bb_id, *target);
            }
            Control::Branches(branch) => {
                let (zero, non_zero, cond) =
                    (branch.zero_target, branch.non_zero_target, branch.condition);
                match self.const_value(cond) {
                    Some(cv) => {
                        let target = if cv.is_zero() { zero } else { non_zero };
                        self.mark_reachable(bb_id, target);
                    }
                    None => {
                        self.mark_reachable(bb_id, zero);
                        self.mark_reachable(bb_id, non_zero);
                    }
                }
            }
            Control::Switch(switch) => {
                let cases_ids = switch.cases;

                match self.const_u256(switch.condition) {
                    Some(val) => {
                        let target = self.program.cases[cases_ids]
                            .iter(&self.program)
                            .find(|(case_val, _)| val == *case_val)
                            .map(|(_, target)| target)
                            .or(switch.fallback);

                        if let Some(t) = target {
                            self.mark_reachable(bb_id, t);
                        }
                    }
                    None => {
                        if let Some(fb) = switch.fallback {
                            self.mark_reachable(bb_id, fb);
                        }
                        let targets: Vec<_> = self.program.cases[cases_ids]
                            .iter(&self.program)
                            .map(|(_, t)| t)
                            .collect();

                        for t in targets {
                            self.mark_reachable(bb_id, t);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn process_values(&mut self) {
        while let Some(value) = self.values_worklist.pop() {
            for UseLocation { block_id, op_id } in &self.uses[value] {
                if !self.reachable[*block_id] {
                    continue;
                }

                // TODO: (maybe?) there is an optimization to skip if the output is already overdefined
                // since we have no outputs() yet and I'm not very sure inputs() has the right approach, I didn't add it
                // there is also the alternative to exit evaluate early but there too we have the multiple tipes of operations (i.e., binary, unary, and ternary)
                // so it might complicate the code a bit to add that check. but technically, adding it there could benefit the processing of the operation

                // we ended up adding outputs for rewriting
                let outputs = self.program.operations[*op_id].outputs(self.program);
                if outputs.iter().all(|o| matches!(self.lattice[*o], LatticeValue::Overdefined)) {
                    continue;
                }

                if let Some((out, result)) = self.evaluate(&self.program.operations[*op_id]) {
                    let value = if let Ok(small) = u32::try_from(result) {
                        ConstValue::SmallConst(small)
                    } else {
                        ConstValue::LargeConst(result)
                    };
                    if self.lattice[out].meet(LatticeValue::Const(value)) {
                        self.values_worklist.push(out);
                    }
                } else {
                    for out in outputs {
                        if self.lattice[out].meet(LatticeValue::Overdefined) {
                            self.values_worklist.push(out);
                        }
                    }
                }
            }
        }
    }

    fn process_block(&mut self, bb_id: X32<BasicBlockIdMarker>) {
        self.process_inputs(bb_id);
        self.process_operations(bb_id);
        self.process_control(bb_id);
        self.process_values();
    }

    fn mark_reachable(&mut self, from: BasicBlockId, to: BasicBlockId) {
        if !self.reachable[to] {
            self.reachable[to] = true;
            self.cfg_worklist.push(to);
        }
        self.flow_outputs_to(from, to);
    }

    fn flow_outputs_to(&mut self, from: BasicBlockId, to: BasicBlockId) {
        let from_outputs = self.program.basic_blocks[from].outputs;
        let to_inputs = self.program.basic_blocks[to].inputs;
        for (i, &output) in self.program.locals[from_outputs].iter().enumerate() {
            let value = self.lattice[output].clone();
            let input = self.program.locals[to_inputs][i];
            if self.lattice[input].meet(value) {
                self.values_worklist.push(input);
            }
        }
    }

    // TODO: (worth?) A minor optimization is to skip the evaluation if output is Overdefined
    fn evaluate(&self, op: &Operation) -> Option<(LocalId, U256)> {
        macro_rules! eval_binary {
            ($a:expr, $b:expr, $out:expr, $f:expr) => {
                if let Some((va, vb)) = self.binary_const_u256(*$a, *$b) {
                    return Some((*$out, $f(va, vb)));
                }
            };
        }

        match op {
            Operation::Add(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, U256::wrapping_add)
            }
            Operation::Mul(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, U256::wrapping_mul)
            }
            Operation::Sub(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, U256::wrapping_sub)
            }
            Operation::Div(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| va.checked_div(vb).unwrap_or(U256::ZERO))
            }
            Operation::SDiv(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb: U256| {
                    let sa = va.to::<I256>();
                    let sb = vb.to::<I256>();
                    sa.checked_div(sb).unwrap_or(I256::ZERO).to::<U256>()
                })
            }
            Operation::Mod(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| va.checked_rem(vb).unwrap_or(U256::ZERO))
            }
            Operation::SMod(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb: U256| {
                    let sa = va.to::<I256>();
                    let sb = vb.to::<I256>();
                    sa.checked_rem(sb).unwrap_or(I256::ZERO).to::<U256>()
                })
            }
            Operation::AddMod(AllocatedIns { ins_start, outs: [out] }) => {
                let a = self.program.locals[*ins_start];
                let b = self.program.locals[*ins_start + 1];
                let n = self.program.locals[*ins_start + 2];

                if let (Some(va), Some(vb), Some(vn)) =
                    (self.const_u256(a), self.const_u256(b), self.const_u256(n))
                {
                    let result = if vn.is_zero() {
                        U256::ZERO
                    } else {
                        let sum = U512::from(va) + U512::from(vb);
                        U256::from(sum % U512::from(vn))
                    };
                    return Some((*out, result));
                }
            }
            Operation::MulMod(AllocatedIns { ins_start, outs: [out] }) => {
                let a = self.program.locals[*ins_start];
                let b = self.program.locals[*ins_start + 1];
                let n = self.program.locals[*ins_start + 2];

                if let (Some(va), Some(vb), Some(vn)) =
                    (self.const_u256(a), self.const_u256(b), self.const_u256(n))
                {
                    let result = if vn.is_zero() {
                        U256::ZERO
                    } else {
                        let prod = U512::from(va) * U512::from(vb);
                        U256::from(prod % U512::from(vn))
                    };
                    return Some((*out, result));
                }
            }
            Operation::Exp(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| va.pow(vb))
            }
            Operation::SignExtend(InlineOperands { ins: [b, x], outs: [out] }) => {
                eval_binary!(b, x, out, |vb: U256, vx| {
                    if vb >= U256::from(31) {
                        vx
                    } else {
                        let sign_bit_pos = (vb.to::<usize>() + 1) * 8 - 1;
                        let sign_bit_mask = U256::from(1) << sign_bit_pos;

                        if (vx & sign_bit_mask) != U256::ZERO {
                            vx | (U256::MAX << (sign_bit_pos + 1))
                        } else {
                            vx & ((U256::from(1) << (sign_bit_pos + 1)) - U256::from(1))
                        }
                    }
                })
            }
            Operation::Lt(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| if va < vb {
                    U256::from(1)
                } else {
                    U256::ZERO
                })
            }
            Operation::Gt(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| if va > vb {
                    U256::from(1)
                } else {
                    U256::ZERO
                })
            }
            Operation::SLt(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb: U256| {
                    if va.to::<I256>() < vb.to::<I256>() { U256::from(1) } else { U256::ZERO }
                })
            }
            Operation::SGt(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb: U256| {
                    if va.to::<I256>() > vb.to::<I256>() { U256::from(1) } else { U256::ZERO }
                })
            }
            Operation::Eq(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| if va == vb {
                    U256::from(1)
                } else {
                    U256::ZERO
                })
            }
            Operation::And(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| va & vb)
            }
            Operation::Or(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| va | vb)
            }
            Operation::Xor(InlineOperands { ins: [a, b], outs: [out] }) => {
                eval_binary!(a, b, out, |va: U256, vb| va ^ vb)
            }
            Operation::Byte(InlineOperands { ins: [i, x], outs: [out] }) => {
                eval_binary!(i, x, out, |vi: U256, vx: U256| {
                    if vi >= U256::from(32) {
                        U256::ZERO
                    } else {
                        U256::from(vx.byte(31 - vi.to::<usize>()))
                    }
                })
            }
            Operation::Shl(InlineOperands { ins: [shift, value], outs: [out] }) => {
                eval_binary!(shift, value, out, |vshift: U256, vvalue| vvalue << vshift)
            }
            Operation::Shr(InlineOperands { ins: [shift, value], outs: [out] }) => {
                eval_binary!(shift, value, out, |vshift: U256, vvalue| vvalue >> vshift)
            }
            Operation::Sar(InlineOperands { ins: [shift, value], outs: [out] }) => {
                eval_binary!(shift, value, out, |vshift: U256, vvalue: U256| {
                    vvalue.to::<I256>().asr(vshift.to::<usize>()).to::<U256>()
                })
            }
            Operation::Not(InlineOperands { ins: [a], outs: [out] }) => {
                if let Some(va) = self.const_u256(*a) {
                    return Some((*out, !va));
                }
            }
            Operation::IsZero(InlineOperands { ins: [a], outs: [out] }) => {
                if let Some(va) = self.const_u256(*a) {
                    return Some((*out, U256::from(va.is_zero())));
                }
            }
            _ => {}
        }
        None
    }

    fn const_u256(&self, local: LocalId) -> Option<U256> {
        match self.const_value(local)? {
            ConstValue::SmallConst(v) => Some(U256::from(*v)),
            ConstValue::LargeConst(v) => Some(*v),
        }
    }

    fn const_value(&self, local: LocalId) -> Option<&ConstValue> {
        match &self.lattice[local] {
            LatticeValue::Const(cv) => Some(cv),
            _ => None,
        }
    }

    fn binary_const_u256(&self, a: LocalId, b: LocalId) -> Option<(U256, U256)> {
        Some((self.const_u256(a)?, self.const_u256(b)?))
    }
}

#[derive(Clone, PartialEq)]
enum LatticeValue {
    Unknown,
    Const(ConstValue),
    EvmConst(EvmConstKind),
    Overdefined,
}

impl LatticeValue {
    fn meet(&mut self, other: Self) -> bool {
        match (&*self, &other) {
            (LatticeValue::Overdefined, _) => {}
            (_, LatticeValue::Overdefined) => {
                *self = LatticeValue::Overdefined;
                return true;
            }
            (_, LatticeValue::Unknown) => {}
            (LatticeValue::Unknown, _) => {
                *self = other;
                return true;
            }
            (LatticeValue::EvmConst(a), LatticeValue::EvmConst(b)) => {
                if a != b {
                    *self = LatticeValue::Overdefined;
                    return true;
                }
            }
            (LatticeValue::Const(a), LatticeValue::Const(b)) => {
                if a != b {
                    *self = LatticeValue::Overdefined;
                    return true;
                }
            }
            (LatticeValue::Const(_), LatticeValue::EvmConst(_))
            | (LatticeValue::EvmConst(_), LatticeValue::Const(_)) => {
                *self = LatticeValue::Overdefined;
                return true;
            }
        }
        false
    }
}

#[derive(PartialEq, Clone, Eq, Hash)]
enum ConstValue {
    SmallConst(u32),
    LargeConst(U256),
}

impl ConstValue {
    fn is_zero(&self) -> bool {
        match self {
            ConstValue::SmallConst(v) => *v == 0,
            ConstValue::LargeConst(v) => v.is_zero(),
        }
    }
}

macro_rules! define_consts {
    ($($name:ident),* $(,)?) => {
        #[derive(PartialEq, Clone, Eq, Hash, Copy)]
        enum EvmConstKind {
            $($name),*
        }

        fn constant(op: &Operation, large_consts: &IndexVec<LargeConstIdMarker, U256>, mut set: impl FnMut(LocalId, LatticeValue)) {
            match op {
                $(
                    Operation::$name(InlineOperands { ins: [], outs: [out] }) => {
                        set(*out, LatticeValue::EvmConst(EvmConstKind::$name));
                    }
                )*
                Operation::SetSmallConst(SetSmallConstData { sets, value }) => {
                    set(*sets, LatticeValue::Const(ConstValue::SmallConst(*value)));
                }
                Operation::SetLargeConst(SetLargeConstData { sets, value }) => {
                    set(*sets, LatticeValue::Const(ConstValue::LargeConst(large_consts[*value])));
                }
                _ => {}
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

    fn run_const_prop(source: &str) -> String {
        let mut ir = parse_or_panic(source, EmitConfig::init_only());
        run(&mut ir);
        sir_data::display_program(&ir)
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

        let actual = run_const_prop(input);
        assert_trim_strings_eq_with_diff(
            &actual,
            expected,
            "block inputs propagate only when predecessors agree",
        );
    }

    #[test]
    fn test_complex_constant_folding() {
        let input = r#"
            fn init:
                entry {
                    zero = const 0
                    seven = const 7
                    five = const 5
                    _0x80 = const 0x80
                    _32 = const 32

                    sign_ext = signextend zero _0x80
                    byte_oob = byte _32 _0x80
                    sar_noop = sar zero _0x80
                    addmod_wrap = addmod seven seven five
                    sdiv_zero = sdiv seven zero

                    stop
                }
        "#;

        // $0-$4: constants (zero, seven, five, _0x80, _32)
        // $5: signextend(0, 0x80) → 0xFF..FF80 (sign extend fills upper bits)
        // $6: byte(32, 0x80) → 0 (index out of bounds)
        // $7: sar(0, 0x80) → 0x80 (shift by 0 is no-op)
        // $8: addmod(7, 7, 5) → 4 ((7+7) % 5)
        // $9: sdiv(7, 0) → 0 (division by zero)
        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x0
        $1 = const 0x7
        $2 = const 0x5
        $3 = const 0x80
        $4 = const 0x20
        $5 = large_const 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80
        $6 = const 0x0
        $7 = const 0x80
        $8 = const 0x4
        $9 = const 0x0
        stop
    }
        "#;

        let actual = run_const_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "complex constant folding");
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

        let actual = run_const_prop(input);
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

        let actual = run_const_prop(input);
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

        let actual = run_const_prop(input);
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

        let actual = run_const_prop(input);
        assert_trim_strings_eq_with_diff(&actual, expected, "switch no match takes default");
    }
}
