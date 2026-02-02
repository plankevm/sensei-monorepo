use std::collections::HashMap;

use sir_data::{
    BasicBlockId, EthIRProgram, LargeConstId, LocalId, LocalIdMarker, LocalIndexMarker, Operation,
    RelSliceMut, Span, X32,
    operation::{
        AllocatedIns, InlineOperands, InternalCallData, MemoryLoadData, MemoryStoreData,
        OpVisitorMut, SetDataOffsetData, SetLargeConstData, SetSmallConstData, StaticAllocData,
    },
};

#[derive(PartialEq, Clone, Eq, Hash)]
enum ConstValue {
    SmallConst(u32),
    LargeConst(LargeConstId),
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
}

fn track_constant(
    constant_map: &mut HashMap<LocalId, ConstValue>,
    first_occurrence: &mut HashMap<ConstValue, LocalId>,
    local: LocalId,
    value: ConstValue,
) {
    constant_map.insert(local, value.clone());
    first_occurrence.entry(value).or_insert(local);
}

type AnalysisResult = (
    HashMap<LocalId, ConstValue>,
    HashMap<ConstValue, LocalId>,
    HashMap<BasicBlockId, Vec<BasicBlockId>>,
);

fn analyze_program(program: &EthIRProgram) -> AnalysisResult {
    let mut constant_map: HashMap<LocalId, ConstValue> = HashMap::new();
    let mut first_occurrence: HashMap<ConstValue, LocalId> = HashMap::new();
    let mut predecessors: HashMap<BasicBlockId, Vec<BasicBlockId>> = HashMap::new();

    for (id, bb) in program.basic_blocks.enumerate_idx() {
        for successor in bb.control.iter_outgoing(program) {
            predecessors.entry(successor).or_default().push(id);
        }
        for op in &program.operations[bb.operations] {
            match op {
                Operation::Address(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::Address,
                    );
                }
                Operation::Origin(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::Origin,
                    );
                }
                Operation::Caller(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::Caller,
                    );
                }
                Operation::CallValue(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::CallValue,
                    );
                }
                Operation::CallDataSize(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::CallDataSize,
                    );
                }
                Operation::CodeSize(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::CodeSize,
                    );
                }
                Operation::GasPrice(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::GasPrice,
                    );
                }
                Operation::Coinbase(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::Coinbase,
                    );
                }
                Operation::Timestamp(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::Timestamp,
                    );
                }
                Operation::Number(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::Number,
                    );
                }
                Operation::ChainId(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::ChainId,
                    );
                }
                Operation::BaseFee(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::BaseFee,
                    );
                }
                Operation::BlobBaseFee(InlineOperands { ins: [], outs: [out] }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *out,
                        ConstValue::BlobBaseFee,
                    );
                }
                Operation::SetSmallConst(SetSmallConstData { sets, value }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *sets,
                        ConstValue::SmallConst(*value),
                    );
                }
                Operation::SetLargeConst(SetLargeConstData { sets, value }) => {
                    track_constant(
                        &mut constant_map,
                        &mut first_occurrence,
                        *sets,
                        ConstValue::LargeConst(*value),
                    );
                }
                _ => {}
            }
        }
    }

    (constant_map, first_occurrence, predecessors)
}

fn resolve_block_inputs(
    program: &EthIRProgram,
    predecessors: &HashMap<BasicBlockId, Vec<BasicBlockId>>,
    constant_map: &mut HashMap<LocalId, ConstValue>,
) {
    for (bb_id, pred_ids) in predecessors {
        let bb = &program.basic_blocks[*bb_id];
        let inputs = &program.locals[bb.inputs];

        for (i, input) in inputs.iter().enumerate() {
            let mut const_value: Option<ConstValue> = None;
            let mut is_unknown = false;

            for pred_id in pred_ids {
                let pred_bb = &program.basic_blocks[*pred_id];
                let pred_output = &program.locals[pred_bb.outputs][i];

                match constant_map.get(pred_output) {
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
                constant_map.insert(*input, c);
            }
        }
    }
}

pub fn run(program: &mut EthIRProgram) {
    let (mut constant_map, first_occurrence, predecessors) = analyze_program(program);
    resolve_block_inputs(program, &predecessors, &mut constant_map);

    let locals = program.locals.as_rel_slice_mut();
    let mut replacer = ConstantReplacer {
        constant_map: &constant_map,
        first_occurrence: &first_occurrence,
        locals,
    };
    for bb in program.basic_blocks.iter() {
        for op in &mut program.operations[bb.operations] {
            op.visit_data_mut(&mut replacer);
        }
    }
}

fn dedupe_const(
    input: &mut X32<LocalIdMarker>,
    constant_map: &HashMap<LocalId, ConstValue>,
    first_occurrence: &HashMap<ConstValue, LocalId>,
) {
    if let Some(replacement) = constant_map.get(input) {
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
