use std::collections::HashMap;

use alloy_primitives::{I256, U256, U512};
use sir_analyses::compute_predecessors;
use sir_data::{
    BasicBlockId, BasicBlockIdMarker, EthIRProgram, IndexVec, LargeConstId, LargeConstIdMarker,
    LocalId, LocalIdMarker, LocalIndexMarker, Operation, RelSliceMut, Span, X32,
    operation::{
        AllocatedIns, InlineOperands, InternalCallData, MemoryLoadData, MemoryStoreData,
        OpVisitorMut, SetDataOffsetData, SetLargeConstData, SetSmallConstData, StaticAllocData,
    },
};

macro_rules! define_track_constant {
    ($($name:ident),* $(,)?) => {
        #[derive(PartialEq, Clone, Eq, Hash)]
        enum ConstValue {
            SmallConst(u32),
            LargeConst(LargeConstId),
            $($name),*
        }

        fn track_constant(
            op: &Operation,
            mut track: impl FnMut(LocalId, ConstValue),
        ) {
            match op {
                $(
                    Operation::$name(InlineOperands { ins: [], outs: [out] }) => {
                        track(*out, ConstValue::$name);
                    }
                )*
                Operation::SetSmallConst(SetSmallConstData { sets, value }) => {
                    track(*sets, ConstValue::SmallConst(*value));
                }
                Operation::SetLargeConst(SetLargeConstData { sets, value }) => {
                    track(*sets, ConstValue::LargeConst(*value));
                }
                _ => {}
            }
        }
    };
}

define_track_constant!(
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

pub struct ConstPropAnalysis<'a> {
    program: &'a mut EthIRProgram,
    constant_map: HashMap<LocalId, ConstValue>,
    first_occurrence: HashMap<ConstValue, LocalId>,
}

impl<'a> ConstPropAnalysis<'a> {
    pub fn new(program: &'a mut EthIRProgram) -> Self {
        let mut analysis =
            Self { program, constant_map: HashMap::new(), first_occurrence: HashMap::new() };
        analysis.init();
        analysis
    }

    fn init(&mut self) {
        let predecessors = compute_predecessors(self.program);

        for bb in self.program.basic_blocks.iter() {
            for op in &self.program.operations[bb.operations] {
                track_constant(op, |local, value| {
                    self.constant_map.insert(local, value.clone());
                    self.first_occurrence.entry(value).or_insert(local);
                });
            }
        }

        self.track_block_inputs(&predecessors);
    }

    fn track_block_inputs(
        &mut self,
        predecessors: &IndexVec<BasicBlockIdMarker, Vec<BasicBlockId>>,
    ) {
        for (bb_id, pred_ids) in predecessors.enumerate_idx() {
            let bb = &self.program.basic_blocks[bb_id];
            let inputs = &self.program.locals[bb.inputs];

            for (i, input) in inputs.iter().enumerate() {
                let mut const_value: Option<ConstValue> = None;
                let mut is_unknown = false;

                for pred_id in pred_ids {
                    let pred_bb = &self.program.basic_blocks[*pred_id];
                    let pred_output = &self.program.locals[pred_bb.outputs][i];

                    match self.constant_map.get(pred_output) {
                        None => {
                            is_unknown = true;
                            break;
                        }
                        Some(c) => match &const_value {
                            None => const_value = Some(c.clone()),
                            Some(existing) => {
                                if existing != c {
                                    is_unknown = true;
                                    break;
                                }
                            }
                        },
                    }
                }

                if !is_unknown && let Some(c) = const_value {
                    self.constant_map.insert(*input, c);
                }
            }
        }
    }

    pub fn apply(&mut self) {
        let locals = self.program.locals.as_rel_slice_mut();
        let mut replacer = ConstantReplacer {
            constant_map: &self.constant_map,
            first_occurrence: &self.first_occurrence,
            locals,
        };
        for bb in self.program.basic_blocks.iter_mut() {
            for op in &mut self.program.operations[bb.operations] {
                op.visit_data_mut(&mut replacer);
                try_fold(
                    op,
                    &self.constant_map,
                    &mut self.program.large_consts,
                    &self.program.locals,
                );
            }

            match &mut bb.control {
                sir_data::Control::Branches(branch) => {
                    dedupe_const(&mut branch.condition, &self.constant_map, &self.first_occurrence);
                }
                sir_data::Control::Switch(switch) => {
                    dedupe_const(&mut switch.condition, &self.constant_map, &self.first_occurrence);
                }
                _ => {}
            }
        }
    }
}

pub fn run(program: &mut EthIRProgram) {
    let mut analysis = ConstPropAnalysis::new(program);
    analysis.apply();
}

fn get_const_value(
    local: &LocalId,
    constant_map: &HashMap<LocalId, ConstValue>,
    large_consts: &IndexVec<LargeConstIdMarker, U256>,
) -> Option<U256> {
    match constant_map.get(local)? {
        ConstValue::SmallConst(v) => Some(U256::from(*v)),
        ConstValue::LargeConst(id) => Some(large_consts[*id]),
        _ => None,
    }
}

fn get_binary_const_values(
    a: &LocalId,
    b: &LocalId,
    constant_map: &HashMap<LocalId, ConstValue>,
    large_consts: &IndexVec<LargeConstIdMarker, U256>,
) -> Option<(U256, U256)> {
    let va = get_const_value(a, constant_map, large_consts)?;
    let vb = get_const_value(b, constant_map, large_consts)?;
    Some((va, vb))
}

fn fold_to_const(
    result: U256,
    out: LocalId,
    large_consts: &mut IndexVec<LargeConstIdMarker, U256>,
) -> Operation {
    if let Ok(small) = u32::try_from(result) {
        Operation::SetSmallConst(SetSmallConstData { sets: out, value: small })
    } else {
        let id = large_consts.push(result);
        Operation::SetLargeConst(SetLargeConstData { sets: out, value: id })
    }
}

fn try_fold(
    op: &mut Operation,
    constant_map: &HashMap<LocalId, ConstValue>,
    large_consts: &mut IndexVec<LargeConstIdMarker, U256>,
    locals: &[LocalId],
) {
    macro_rules! fold_binary {
        ($a:expr, $b:expr, $out:expr, $f:expr) => {
            if let Some((va, vb)) = get_binary_const_values($a, $b, constant_map, large_consts) {
                *op = fold_to_const($f(va, vb), *$out, large_consts);
            }
        };
    }

    match op {
        Operation::Add(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, U256::wrapping_add)
        }
        Operation::Mul(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, U256::wrapping_mul)
        }
        Operation::Sub(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, U256::wrapping_sub)
        }
        Operation::Div(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb| va.checked_div(vb).unwrap_or(U256::ZERO))
        }
        Operation::SDiv(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb: U256| {
                let sa = va.to::<I256>();
                let sb = vb.to::<I256>();
                sa.checked_div(sb).unwrap_or(I256::ZERO).to::<U256>()
            })
        }
        Operation::Mod(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb| va.checked_rem(vb).unwrap_or(U256::ZERO))
        }
        Operation::SMod(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb: U256| {
                let sa = va.to::<I256>();
                let sb = vb.to::<I256>();
                sa.checked_rem(sb).unwrap_or(I256::ZERO).to::<U256>()
            })
        }
        Operation::AddMod(AllocatedIns { ins_start, outs: [out] }) => {
            let idx = ins_start.get() as usize;
            let a = locals[idx];
            let b = locals[idx + 1];
            let n = locals[idx + 2];

            if let (Some(va), Some(vb), Some(vn)) = (
                get_const_value(&a, constant_map, large_consts),
                get_const_value(&b, constant_map, large_consts),
                get_const_value(&n, constant_map, large_consts),
            ) {
                let result = if vn.is_zero() {
                    U256::ZERO
                } else {
                    let sum = U512::from(va) + U512::from(vb);
                    U256::from(sum % U512::from(vn))
                };
                *op = fold_to_const(result, *out, large_consts);
            }
        }
        Operation::MulMod(AllocatedIns { ins_start, outs: [out] }) => {
            let idx = ins_start.get() as usize;
            let a = locals[idx];
            let b = locals[idx + 1];
            let n = locals[idx + 2];

            if let (Some(va), Some(vb), Some(vn)) = (
                get_const_value(&a, constant_map, large_consts),
                get_const_value(&b, constant_map, large_consts),
                get_const_value(&n, constant_map, large_consts),
            ) {
                let result = if vn.is_zero() {
                    U256::ZERO
                } else {
                    let prod = U512::from(va) * U512::from(vb);
                    U256::from(prod % U512::from(vn))
                };
                *op = fold_to_const(result, *out, large_consts);
            }
        }
        Operation::Exp(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb| va.pow(vb))
        }
        Operation::SignExtend(InlineOperands { ins: [b, x], outs: [out] }) => {
            fold_binary!(b, x, out, |vb: U256, vx| {
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
            fold_binary!(a, b, out, |va: U256, vb| if va < vb { U256::from(1) } else { U256::ZERO })
        }
        Operation::Gt(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb| if va > vb { U256::from(1) } else { U256::ZERO })
        }
        Operation::SLt(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb: U256| {
                if va.to::<I256>() < vb.to::<I256>() { U256::from(1) } else { U256::ZERO }
            })
        }
        Operation::SGt(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb: U256| {
                if va.to::<I256>() > vb.to::<I256>() { U256::from(1) } else { U256::ZERO }
            })
        }
        Operation::Eq(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb| if va == vb {
                U256::from(1)
            } else {
                U256::ZERO
            })
        }
        Operation::And(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb| va & vb)
        }
        Operation::Or(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb| va | vb)
        }
        Operation::Xor(InlineOperands { ins: [a, b], outs: [out] }) => {
            fold_binary!(a, b, out, |va: U256, vb| va ^ vb)
        }
        Operation::Byte(InlineOperands { ins: [i, x], outs: [out] }) => {
            fold_binary!(i, x, out, |vi: U256, vx: U256| {
                if vi >= U256::from(32) {
                    U256::ZERO
                } else {
                    U256::from(vx.byte(31 - vi.to::<usize>()))
                }
            })
        }
        Operation::Shl(InlineOperands { ins: [shift, value], outs: [out] }) => {
            fold_binary!(shift, value, out, |vshift: U256, vvalue| vvalue << vshift)
        }
        Operation::Shr(InlineOperands { ins: [shift, value], outs: [out] }) => {
            fold_binary!(shift, value, out, |vshift: U256, vvalue| vvalue >> vshift)
        }
        Operation::Sar(InlineOperands { ins: [shift, value], outs: [out] }) => {
            fold_binary!(shift, value, out, |vshift: U256, vvalue: U256| {
                vvalue.to::<I256>().asr(vshift.to::<usize>()).to::<U256>()
            })
        }
        Operation::Not(InlineOperands { ins: [a], outs: [out] }) => {
            if let Some(va) = get_const_value(a, constant_map, large_consts) {
                *op = fold_to_const(!va, *out, large_consts);
            }
        }
        Operation::IsZero(InlineOperands { ins: [a], outs: [out] }) => {
            if let Some(va) = get_const_value(a, constant_map, large_consts) {
                *op = fold_to_const(U256::from(va.is_zero()), *out, large_consts);
            }
        }
        _ => {}
    }
}

fn dedupe_const(
    input: &mut X32<LocalIdMarker>,
    constant_map: &HashMap<LocalId, ConstValue>,
    first_occurrence: &HashMap<ConstValue, LocalId>,
) {
    if let Some(replacement) = constant_map.get(input) {
        // Safe: every value in constant_map has a corresponding entry in first_occurrence
        *input = first_occurrence[replacement];
    }
}

struct ConstantReplacer<'a> {
    constant_map: &'a HashMap<LocalId, ConstValue>,
    first_occurrence: &'a HashMap<ConstValue, LocalId>,
    locals: RelSliceMut<'a, LocalIndexMarker, LocalId>,
}

impl OpVisitorMut<()> for ConstantReplacer<'_> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut InlineOperands<INS, OUTS>,
    ) {
        for input in &mut data.ins {
            dedupe_const(input, self.constant_map, self.first_occurrence);
        }
    }

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &mut AllocatedIns<INS, OUTS>,
    ) {
        for idx in Span::new(data.ins_start, data.ins_start + INS as u32).iter() {
            dedupe_const(&mut self.locals[idx], self.constant_map, self.first_occurrence);
        }
    }

    fn visit_static_alloc_mut(&mut self, _data: &mut StaticAllocData) {}

    fn visit_memory_load_mut(&mut self, data: &mut MemoryLoadData) {
        dedupe_const(&mut data.ptr, self.constant_map, self.first_occurrence);
    }

    fn visit_memory_store_mut(&mut self, data: &mut MemoryStoreData) {
        dedupe_const(&mut data.ptr, self.constant_map, self.first_occurrence);
        dedupe_const(&mut data.value, self.constant_map, self.first_occurrence);
    }

    fn visit_set_small_const_mut(&mut self, _data: &mut SetSmallConstData) {}

    fn visit_set_large_const_mut(&mut self, _data: &mut SetLargeConstData) {}

    fn visit_set_data_offset_mut(&mut self, _data: &mut SetDataOffsetData) {}

    fn visit_icall_mut(&mut self, data: &mut InternalCallData) {
        for idx in Span::new(data.ins_start, data.outs_start).iter() {
            dedupe_const(&mut self.locals[idx], self.constant_map, self.first_occurrence);
        }
    }

    fn visit_void_mut(&mut self) {}
}

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
    fn test_duplicate_small_constants_deduplicated() {
        let input = r#"
            fn init:
                entry {
                    a = const 42
                    b = const 42
                    c = add b b
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x2a
        $1 = const 0x2a
        $2 = add $0 $0
        stop
    }
        "#;

        let actual = run_const_prop(input);
        assert_trim_strings_eq_with_diff(
            &actual,
            expected,
            "duplicate small constants deduplicated",
        );
    }

    #[test]
    fn test_evm_constant_in_branch_and_operations() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry {
                    a = caller
                    b = caller
                    c = eq a b
                    => b ? @nonzero : @zero
                }
                nonzero {
                    stop
                }
                zero {
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

    @1 {
        $0 = caller
        $1 = caller
        $2 = eq $0 $0
        => $0 ? @2 : @3
    }

    @2 {
        stop
    }

    @3 {
        stop
    }
        "#;

        let actual = run_const_prop(input);
        assert_trim_strings_eq_with_diff(
            &actual,
            expected,
            "evm constant in branch and operations",
        );
    }

    #[test]
    fn test_switch_dedupes_constant_from_block_input() {
        let input = r#"
            fn init:
                entry {
                    stop
                }
            fn test:
                entry x {
                    => x ? @block_a : @block_b
                }
                block_a -> val_a {
                    val_a = chainid
                    => @merge
                }
                block_b -> val_b {
                    val_b = chainid
                    => @merge
                }
                merge val {
                    first_chainid = chainid
                    switch val {
                        1 => @case_one
                        default => @case_default
                    }
                }
                case_one {
                    stop
                }
                case_default {
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

    @2 -> $1 {
        $1 = chainid
        => @4
    }

    @3 -> $2 {
        $2 = chainid
        => @4
    }

    @4 $3 {
        $4 = chainid
        switch $1 {
            1 => @5,
            else => @6
        }

    }

    @5 {
        stop
    }

    @6 {
        stop
    }
        "#;

        let actual = run_const_prop(input);
        assert_trim_strings_eq_with_diff(
            &actual,
            expected,
            "switch dedupes constant from block input",
        );
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
                    result = add input_same input_diff
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
        $7 = add $1 $6
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
    fn test_large_constants_not_deduplicated_by_value() {
        // Large constants are compared by LargeConstId, not by value.
        let input = r#"
            fn init:
                entry {
                    a = large_const 0x1234567890abcdef1234567890abcdef
                    b = large_const 0x1234567890abcdef1234567890abcdef
                    c = add a b
                    stop
                }
        "#;

        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = large_const 0x1234567890abcdef1234567890abcdef
        $1 = large_const 0x1234567890abcdef1234567890abcdef
        $2 = add $0 $1
        stop
    }
        "#;

        let actual = run_const_prop(input);
        assert_trim_strings_eq_with_diff(
            &actual,
            expected,
            "large constants not deduplicated by value",
        );
    }
}
