use std::collections::HashMap;

use sir_data::{
    BasicBlockId, EthIRProgram, LargeConstId, LocalId, LocalIdMarker, LocalIndexMarker, Operation,
    RelSliceMut, Span, X32,
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
    ChainId,
    BaseFee,
    BlobBaseFee,
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
        let mut predecessors: HashMap<BasicBlockId, Vec<BasicBlockId>> = HashMap::new();

        for (id, bb) in self.program.basic_blocks.enumerate_idx() {
            for successor in bb.control.iter_outgoing(self.program) {
                predecessors.entry(successor).or_default().push(id);
            }
            for op in &self.program.operations[bb.operations] {
                track_constant(op, |local, value| {
                    self.constant_map.insert(local, value.clone());
                    self.first_occurrence.entry(value).or_insert(local);
                });
            }
        }

        self.track_block_inputs(&predecessors);
    }

    fn track_block_inputs(&mut self, predecessors: &HashMap<BasicBlockId, Vec<BasicBlockId>>) {
        for (bb_id, pred_ids) in predecessors {
            let bb = &self.program.basic_blocks[*bb_id];
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
}
