use crate::{EthIRProgram, builder::EthIRBuilder, index::*};
use alloy_primitives::{U256, ruint::FromUintError};
use sensei_core::span::Span;

pub(crate) trait VoidOpData {
    fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O;
    fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(&'d mut self, visitor: &mut V) -> O;
}

impl VoidOpData for () {
    fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_void()
    }

    fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(&'d mut self, visitor: &mut V) -> O {
        visitor.visit_void_mut()
    }
}

impl FromOpData for () {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        _builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        if extra != OpExtraData::Empty {
            return Err(OpBuildError::UnexpectedExtraData { received: extra, expected: "Empty" });
        }
        check_ins_count(ins, 0)?;
        check_outs_count(outs, 0)?;

        Ok(())
    }
}

pub trait OpVisitor<'d, VisitOut> {
    fn visit_inline_operands<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'d InlineOperands<INS, OUTS>,
    ) -> VisitOut;

    fn visit_allocated_ins<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'d AllocatedIns<INS, OUTS>,
    ) -> VisitOut;

    fn visit_static_alloc(&mut self, data: &'d StaticAllocData) -> VisitOut;
    fn visit_memory_load(&mut self, data: &'d MemoryLoadData) -> VisitOut;
    fn visit_memory_store(&mut self, data: &'d MemoryStoreData) -> VisitOut;
    fn visit_set_small_const(&mut self, data: &'d SetSmallConstData) -> VisitOut;
    fn visit_set_large_const(&mut self, data: &'d SetLargeConstData) -> VisitOut;
    fn visit_set_data_offset(&mut self, data: &'d SetDataOffsetData) -> VisitOut;
    fn visit_icall(&mut self, data: &'d InternalCallData) -> VisitOut;
    fn visit_void(&mut self) -> VisitOut;
}

pub trait OpVisitorMut<'d, VisitOut> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'d mut InlineOperands<INS, OUTS>,
    ) -> VisitOut;

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'d mut AllocatedIns<INS, OUTS>,
    ) -> VisitOut;

    fn visit_static_alloc_mut(&mut self, data: &'d mut StaticAllocData) -> VisitOut;
    fn visit_memory_load_mut(&mut self, data: &'d mut MemoryLoadData) -> VisitOut;
    fn visit_memory_store_mut(&mut self, data: &'d mut MemoryStoreData) -> VisitOut;
    fn visit_set_small_const_mut(&mut self, data: &'d mut SetSmallConstData) -> VisitOut;
    fn visit_set_large_const_mut(&mut self, data: &'d mut SetLargeConstData) -> VisitOut;
    fn visit_set_data_offset_mut(&mut self, data: &'d mut SetDataOffsetData) -> VisitOut;
    fn visit_icall_mut(&mut self, data: &'d mut InternalCallData) -> VisitOut;
    fn visit_void_mut(&mut self) -> VisitOut;
}

pub(crate) struct InputsGetter<'a> {
    pub(crate) ir: &'a EthIRProgram,
}

impl<'a> OpVisitor<'a, &'a [LocalId]> for InputsGetter<'a> {
    fn visit_inline_operands<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a InlineOperands<INS, OUTS>,
    ) -> &'a [LocalId] {
        &data.ins
    }

    fn visit_allocated_ins<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a AllocatedIns<INS, OUTS>,
    ) -> &'a [LocalId] {
        data.get_inputs(self.ir)
    }

    fn visit_static_alloc(&mut self, _data: &'a StaticAllocData) -> &'a [LocalId] {
        &[]
    }
    fn visit_memory_load(&mut self, data: &'a MemoryLoadData) -> &'a [LocalId] {
        std::slice::from_ref(&data.ptr)
    }
    fn visit_memory_store(&mut self, data: &'a MemoryStoreData) -> &'a [LocalId] {
        &data.ins
    }
    fn visit_set_small_const(&mut self, _data: &'a SetSmallConstData) -> &'a [LocalId] {
        &[]
    }
    fn visit_set_large_const(&mut self, _data: &'a SetLargeConstData) -> &'a [LocalId] {
        &[]
    }
    fn visit_set_data_offset(&mut self, _data: &'a SetDataOffsetData) -> &'a [LocalId] {
        &[]
    }
    fn visit_icall(&mut self, data: &'a InternalCallData) -> &'a [LocalId] {
        data.get_inputs(self.ir)
    }
    fn visit_void(&mut self) -> &'a [LocalId] {
        &[]
    }
}

pub(crate) struct OutputsGetter<'a> {
    pub(crate) ir: &'a EthIRProgram,
}

impl<'a> OpVisitor<'a, &'a [LocalId]> for OutputsGetter<'a> {
    fn visit_inline_operands<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a InlineOperands<INS, OUTS>,
    ) -> &'a [LocalId] {
        &data.outs
    }

    fn visit_allocated_ins<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a AllocatedIns<INS, OUTS>,
    ) -> &'a [LocalId] {
        &data.outs
    }

    fn visit_static_alloc(&mut self, data: &'a StaticAllocData) -> &'a [LocalId] {
        std::slice::from_ref(&data.ptr_out)
    }
    fn visit_memory_load(&mut self, data: &'a MemoryLoadData) -> &'a [LocalId] {
        std::slice::from_ref(&data.out)
    }
    fn visit_memory_store(&mut self, _data: &'a MemoryStoreData) -> &'a [LocalId] {
        &[]
    }
    fn visit_set_small_const(&mut self, data: &'a SetSmallConstData) -> &'a [LocalId] {
        std::slice::from_ref(&data.sets)
    }
    fn visit_set_large_const(&mut self, data: &'a SetLargeConstData) -> &'a [LocalId] {
        std::slice::from_ref(&data.sets)
    }
    fn visit_set_data_offset(&mut self, data: &'a SetDataOffsetData) -> &'a [LocalId] {
        std::slice::from_ref(&data.sets)
    }
    fn visit_icall(&mut self, data: &'a InternalCallData) -> &'a [LocalId] {
        data.get_outputs(self.ir)
    }
    fn visit_void(&mut self) -> &'a [LocalId] {
        &[]
    }
}

#[derive(Debug)]
pub struct AllocatedSpans {
    pub input: Option<Span<LocalIdx>>,
    pub output: Option<Span<LocalIdx>>,
}

impl AllocatedSpans {
    pub const NONE: Self = Self { input: None, output: None };
}

pub(crate) struct AllocatedSpansGetter<'a> {
    pub(crate) ir: &'a EthIRProgram,
}

impl<'a> OpVisitor<'a, AllocatedSpans> for AllocatedSpansGetter<'a> {
    fn visit_inline_operands<const INS: usize, const OUTS: usize>(
        &mut self,
        _data: &'a InlineOperands<INS, OUTS>,
    ) -> AllocatedSpans {
        AllocatedSpans::NONE
    }

    fn visit_allocated_ins<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a AllocatedIns<INS, OUTS>,
    ) -> AllocatedSpans {
        AllocatedSpans {
            input: Some(Span::new(data.ins_start, data.ins_start + INS as u32)),
            output: None,
        }
    }

    fn visit_static_alloc(&mut self, _data: &'a StaticAllocData) -> AllocatedSpans {
        AllocatedSpans::NONE
    }
    fn visit_memory_load(&mut self, _data: &'a MemoryLoadData) -> AllocatedSpans {
        AllocatedSpans::NONE
    }
    fn visit_memory_store(&mut self, _data: &'a MemoryStoreData) -> AllocatedSpans {
        AllocatedSpans::NONE
    }
    fn visit_set_small_const(&mut self, _data: &'a SetSmallConstData) -> AllocatedSpans {
        AllocatedSpans::NONE
    }
    fn visit_set_large_const(&mut self, _data: &'a SetLargeConstData) -> AllocatedSpans {
        AllocatedSpans::NONE
    }
    fn visit_set_data_offset(&mut self, _data: &'a SetDataOffsetData) -> AllocatedSpans {
        AllocatedSpans::NONE
    }
    fn visit_icall(&mut self, data: &'a InternalCallData) -> AllocatedSpans {
        let fn_outputs = self.ir.functions[data.function].outputs;
        AllocatedSpans {
            input: Some(Span::new(data.ins_start, data.outs_start)),
            output: Some(Span::new(data.outs_start, data.outs_start + fn_outputs)),
        }
    }
    fn visit_void(&mut self) -> AllocatedSpans {
        AllocatedSpans::NONE
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpExtraData {
    DataId(DataId),
    FuncId(FunctionId),
    Num(U256),
    Empty,
}

#[derive(Debug, Clone)]
pub struct InlineOperands<const INS: usize, const OUTS: usize> {
    pub ins: [LocalId; INS],
    pub outs: [LocalId; OUTS],
}

impl<const INS: usize, const OUTS: usize> InlineOperands<INS, OUTS> {
    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_inline_operands(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_inline_operands_mut(self)
    }
}

impl Default for InlineOperands<0, 0> {
    fn default() -> Self {
        Self { ins: [], outs: [] }
    }
}

/// Operation data where inputs are allocated in the IR but outputs are stored inline.
#[derive(Debug, Clone)]
pub struct AllocatedIns<const INS: usize, const OUTS: usize> {
    pub ins_start: LocalIdx,
    pub outs: [LocalId; OUTS],
}

impl<const INS: usize, const OUTS: usize> AllocatedIns<INS, OUTS> {
    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_allocated_ins(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_allocated_ins_mut(self)
    }

    pub fn get_inputs<'ir>(&self, ir: &'ir EthIRProgram) -> &'ir [LocalId] {
        let ins_start = self.ins_start.idx();
        &ir.locals.as_raw_slice()[ins_start..ins_start + INS]
    }
}

#[derive(Debug, Clone)]
pub struct StaticAllocData {
    pub size: u32,
    pub ptr_out: LocalId,
    pub alloc_id: StaticAllocId,
}

impl StaticAllocData {
    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_static_alloc(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_static_alloc_mut(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum IRMemoryIOByteSize {
    B1 = 1,
    B2 = 2,
    B3 = 3,
    B4 = 4,
    B5 = 5,
    B6 = 6,
    B7 = 7,
    B8 = 8,
    B9 = 9,
    B10 = 10,
    B11 = 11,
    B12 = 12,
    B13 = 13,
    B14 = 14,
    B15 = 15,
    B16 = 16,
    B17 = 17,
    B18 = 18,
    B19 = 19,
    B20 = 20,
    B21 = 21,
    B22 = 22,
    B23 = 23,
    B24 = 24,
    B25 = 25,
    B26 = 26,
    B27 = 27,
    B28 = 28,
    B29 = 29,
    B30 = 30,
    B31 = 31,
    B32 = 32,
}

impl IRMemoryIOByteSize {
    const MIN: Self = Self::B1;
    const MAX: Self = Self::B32;

    pub fn try_from_u8(x: u8) -> Option<Self> {
        match x {
            1 => Some(Self::B1),
            2 => Some(Self::B2),
            3 => Some(Self::B3),
            4 => Some(Self::B4),
            5 => Some(Self::B5),
            6 => Some(Self::B6),
            7 => Some(Self::B7),
            8 => Some(Self::B8),
            9 => Some(Self::B9),
            10 => Some(Self::B10),
            11 => Some(Self::B11),
            12 => Some(Self::B12),
            13 => Some(Self::B13),
            14 => Some(Self::B14),
            15 => Some(Self::B15),
            16 => Some(Self::B16),
            17 => Some(Self::B17),
            18 => Some(Self::B18),
            19 => Some(Self::B19),
            20 => Some(Self::B20),
            21 => Some(Self::B21),
            22 => Some(Self::B22),
            23 => Some(Self::B23),
            24 => Some(Self::B24),
            25 => Some(Self::B25),
            26 => Some(Self::B26),
            27 => Some(Self::B27),
            28 => Some(Self::B28),
            29 => Some(Self::B29),
            30 => Some(Self::B30),
            31 => Some(Self::B31),
            32 => Some(Self::B32),
            _ => None,
        }
    }

    pub fn bits(&self) -> u16 {
        (*self as u16) * 8
    }
}

#[derive(Debug, Clone)]
pub struct MemoryLoadData {
    pub out: LocalId,
    pub ptr: LocalId,
    pub size: IRMemoryIOByteSize,
}

impl MemoryLoadData {
    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_memory_load(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_memory_load_mut(self)
    }
}

#[derive(Debug, Clone)]
pub struct MemoryStoreData {
    pub ins: [LocalId; 2],
    pub size: IRMemoryIOByteSize,
}

impl MemoryStoreData {
    pub fn ptr(&self) -> LocalId {
        self.ins[0]
    }

    pub fn value(&self) -> LocalId {
        self.ins[1]
    }

    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_memory_store(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_memory_store_mut(self)
    }
}

#[derive(Debug, Clone)]
pub struct SetSmallConstData {
    pub sets: LocalId,
    pub value: u32,
}

impl SetSmallConstData {
    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_set_small_const(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_set_small_const_mut(self)
    }
}

#[derive(Debug, Clone)]
pub struct SetLargeConstData {
    pub sets: LocalId,
    pub value: LargeConstId,
}

impl SetLargeConstData {
    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_set_large_const(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_set_large_const_mut(self)
    }
}

#[derive(Debug, Clone)]
pub struct SetDataOffsetData {
    pub sets: LocalId,
    pub segment_id: DataId,
}

impl SetDataOffsetData {
    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_set_data_offset(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_set_data_offset_mut(self)
    }
}

/// Expects args and outputs to be stored contiguously in the IR arena:
/// - Arguments: `ins_start..outs_start`
/// - Outputs: `outs_start..outs_start + functions[function].outputs`
#[derive(Debug, Clone)]
pub struct InternalCallData {
    pub function: FunctionId,
    pub ins_start: LocalIdx,
    pub outs_start: LocalIdx,
}

impl InternalCallData {
    pub(crate) fn get_visited<'d, O, V: OpVisitor<'d, O>>(&'d self, visitor: &mut V) -> O {
        visitor.visit_icall(self)
    }

    pub(crate) fn get_visited_mut<'d, O, V: OpVisitorMut<'d, O>>(
        &'d mut self,
        visitor: &mut V,
    ) -> O {
        visitor.visit_icall_mut(self)
    }

    pub fn get_inputs<'ir>(&self, ir: &'ir EthIRProgram) -> &'ir [LocalId] {
        &ir.locals[self.ins_start..self.outs_start]
    }

    pub fn get_outputs<'ir>(&self, ir: &'ir EthIRProgram) -> &'ir [LocalId] {
        let fn_output_count = ir.functions[self.function].outputs;
        &ir.locals[self.outs_start..self.outs_start + fn_output_count]
    }
}

#[derive(Debug, thiserror::Error)]
pub enum OpBuildError {
    #[error("Wrong input count: got {received}, expected {expected}")]
    WrongInputCount { expected: usize, received: usize },
    #[error("Wrong output count: got {received}, expected {expected}")]
    WrongOutputCount { expected: usize, received: usize },
    #[error("Unexpected extra data: got {received:?}, expected {expected}")]
    UnexpectedExtraData { received: OpExtraData, expected: &'static str },
    #[error("Undefined function @{0}")]
    UndefinedFunction(FunctionId),
    #[error(
        "Provided number {too_large} too large, expected value in range [{valid_lower}; {valid_upper}]"
    )]
    NumTooLarge { too_large: U256, valid_lower: u32, valid_upper: u32 },
}

pub trait FromOpData: Sized {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError>;
}

fn check_ins_count(ins: &[LocalId], expected: usize) -> Result<(), OpBuildError> {
    if ins.len() != expected {
        return Err(OpBuildError::WrongInputCount { expected, received: ins.len() });
    }
    Ok(())
}

fn check_outs_count(outs: &[LocalId], expected: usize) -> Result<(), OpBuildError> {
    if outs.len() != expected {
        return Err(OpBuildError::WrongOutputCount { expected, received: outs.len() });
    }
    Ok(())
}

impl<const INS: usize, const OUTS: usize> FromOpData for InlineOperands<INS, OUTS> {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        _builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let outs = outs
            .try_into()
            .map_err(|_| OpBuildError::WrongOutputCount { expected: OUTS, received: outs.len() })?;
        let ins = ins
            .try_into()
            .map_err(|_| OpBuildError::WrongInputCount { expected: INS, received: ins.len() })?;
        if extra != OpExtraData::Empty {
            return Err(OpBuildError::UnexpectedExtraData { received: extra, expected: "Empty" });
        }
        Ok(Self { ins, outs })
    }
}

impl<const INS: usize, const OUTS: usize> FromOpData for AllocatedIns<INS, OUTS> {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let outs = outs
            .try_into()
            .map_err(|_| OpBuildError::WrongOutputCount { expected: OUTS, received: outs.len() })?;
        check_ins_count(ins, INS)?;
        let ins_span = builder.alloc_locals(ins);
        assert_eq!(ins_span.end - ins_span.start, INS as u32);
        if extra != OpExtraData::Empty {
            return Err(OpBuildError::UnexpectedExtraData { received: extra, expected: "Empty" });
        }
        Ok(Self { ins_start: ins_span.start, outs })
    }
}

impl FromOpData for InternalCallData {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let OpExtraData::FuncId(func_id) = extra else {
            return Err(OpBuildError::UnexpectedExtraData {
                received: extra,
                expected: "FunctionId",
            });
        };
        let func = *builder.get_func(func_id).ok_or(OpBuildError::UndefinedFunction(func_id))?;
        let inputs = func.get_inputs(&builder.basic_blocks) as usize;
        let outputs = func.get_outputs() as usize;

        check_ins_count(ins, inputs)?;
        check_outs_count(outs, outputs)?;

        let ins_span = builder.alloc_locals(ins);
        let outs_span = builder.alloc_locals(outs);
        assert_eq!(
            ins_span.end, outs_span.start,
            "Expecting icall locals to be stored contiguously"
        );

        Ok(InternalCallData {
            function: func_id,
            ins_start: ins_span.start,
            outs_start: outs_span.start,
        })
    }
}

impl FromOpData for SetLargeConstData {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let OpExtraData::Num(num) = extra else {
            return Err(OpBuildError::UnexpectedExtraData {
                received: extra,
                expected: "Num(u256)",
            });
        };

        check_ins_count(ins, 0)?;
        check_outs_count(outs, 1)?;

        let cid = builder.alloc_u256(num);

        Ok(SetLargeConstData { sets: outs[0], value: cid })
    }
}

fn uint256_to_u32(x: U256) -> Result<u32, OpBuildError> {
    x.try_into().map_err(|err| match err {
        FromUintError::Overflow(_, _, _) => {
            OpBuildError::NumTooLarge { too_large: x, valid_lower: 0, valid_upper: u32::MAX }
        }
    })
}

impl FromOpData for SetSmallConstData {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        _builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let OpExtraData::Num(value) = extra else {
            return Err(OpBuildError::UnexpectedExtraData {
                received: extra,
                expected: "Num(u32)",
            });
        };

        let value = uint256_to_u32(value)?;

        check_ins_count(ins, 0)?;
        check_outs_count(outs, 1)?;

        Ok(SetSmallConstData { sets: outs[0], value })
    }
}

impl FromOpData for StaticAllocData {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let OpExtraData::Num(size) = extra else {
            return Err(OpBuildError::UnexpectedExtraData {
                received: extra,
                expected: "Num(u32)",
            });
        };

        let size = uint256_to_u32(size)?;

        check_ins_count(ins, 0)?;
        check_outs_count(outs, 1)?;
        let alloc_id = builder.new_static_alloc();

        Ok(StaticAllocData { size, ptr_out: outs[0], alloc_id })
    }
}

impl FromOpData for MemoryLoadData {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        _builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let OpExtraData::Num(size) = extra else {
            return Err(OpBuildError::UnexpectedExtraData {
                received: extra,
                expected: "Num(u32)",
            });
        };
        let Some(size) = size.try_into().ok().and_then(IRMemoryIOByteSize::try_from_u8) else {
            return Err(OpBuildError::NumTooLarge {
                too_large: size,
                valid_lower: IRMemoryIOByteSize::B1 as u32,
                valid_upper: IRMemoryIOByteSize::B32 as u32,
            });
        };
        check_ins_count(ins, 1)?;
        check_outs_count(outs, 1)?;

        Ok(MemoryLoadData { out: outs[0], ptr: ins[0], size })
    }
}

impl FromOpData for MemoryStoreData {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        _builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let OpExtraData::Num(size) = extra else {
            return Err(OpBuildError::UnexpectedExtraData {
                received: extra,
                expected: "Num(1..=32)",
            });
        };
        let Some(size) = size.try_into().ok().and_then(IRMemoryIOByteSize::try_from_u8) else {
            return Err(OpBuildError::NumTooLarge {
                too_large: size,
                valid_lower: IRMemoryIOByteSize::MIN as u32,
                valid_upper: IRMemoryIOByteSize::MAX as u32,
            });
        };
        check_ins_count(ins, 2)?;
        check_outs_count(outs, 0)?;

        Ok(MemoryStoreData { ins: [ins[0], ins[1]], size })
    }
}

impl FromOpData for SetDataOffsetData {
    fn try_build_op(
        ins: &[LocalId],
        outs: &[LocalId],
        extra: OpExtraData,
        _builder: &mut EthIRBuilder,
    ) -> Result<Self, OpBuildError> {
        let OpExtraData::DataId(segment_id) = extra else {
            return Err(OpBuildError::UnexpectedExtraData { received: extra, expected: "DataId" });
        };

        check_ins_count(ins, 0)?;
        check_outs_count(outs, 1)?;

        Ok(SetDataOffsetData { sets: outs[0], segment_id })
    }
}
