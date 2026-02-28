use crate::{EthIRProgram, index::*};
use sensei_core::span::Span;

use super::op_data::*;

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

pub(crate) struct InputsMutGetter<'a> {
    pub(crate) locals: Option<&'a mut IndexVec<LocalIdx, LocalId>>,
}

impl<'a> OpVisitorMut<'a, &'a mut [LocalId]> for InputsMutGetter<'a> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a mut InlineOperands<INS, OUTS>,
    ) -> &'a mut [LocalId] {
        &mut data.ins
    }

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a mut AllocatedIns<INS, OUTS>,
    ) -> &'a mut [LocalId] {
        let locals = self.locals.take().unwrap();
        let start = data.ins_start.idx();
        &mut locals.as_raw_slice_mut()[start..start + INS]
    }

    fn visit_static_alloc_mut(&mut self, _data: &'a mut StaticAllocData) -> &'a mut [LocalId] {
        &mut []
    }

    fn visit_memory_load_mut(&mut self, data: &'a mut MemoryLoadData) -> &'a mut [LocalId] {
        std::slice::from_mut(&mut data.ptr)
    }

    fn visit_memory_store_mut(&mut self, data: &'a mut MemoryStoreData) -> &'a mut [LocalId] {
        &mut data.ins
    }

    fn visit_set_small_const_mut(&mut self, _data: &'a mut SetSmallConstData) -> &'a mut [LocalId] {
        &mut []
    }

    fn visit_set_large_const_mut(&mut self, _data: &'a mut SetLargeConstData) -> &'a mut [LocalId] {
        &mut []
    }

    fn visit_set_data_offset_mut(&mut self, _data: &'a mut SetDataOffsetData) -> &'a mut [LocalId] {
        &mut []
    }

    fn visit_icall_mut(&mut self, data: &'a mut InternalCallData) -> &'a mut [LocalId] {
        let locals = self.locals.take().unwrap();
        let start = data.ins_start.idx();
        let end = data.outs_start.idx();
        &mut locals.as_raw_slice_mut()[start..end]
    }

    fn visit_void_mut(&mut self) -> &'a mut [LocalId] {
        &mut []
    }
}

pub(crate) struct OutputsMutGetter<'a> {
    pub(crate) locals: Option<&'a mut IndexVec<LocalIdx, LocalId>>,
    pub(crate) functions: &'a IndexVec<FunctionId, crate::Function>,
}

impl<'a> OpVisitorMut<'a, &'a mut [LocalId]> for OutputsMutGetter<'a> {
    fn visit_inline_operands_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a mut InlineOperands<INS, OUTS>,
    ) -> &'a mut [LocalId] {
        &mut data.outs
    }

    fn visit_allocated_ins_mut<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'a mut AllocatedIns<INS, OUTS>,
    ) -> &'a mut [LocalId] {
        &mut data.outs
    }

    fn visit_static_alloc_mut(&mut self, data: &'a mut StaticAllocData) -> &'a mut [LocalId] {
        std::slice::from_mut(&mut data.ptr_out)
    }

    fn visit_memory_load_mut(&mut self, data: &'a mut MemoryLoadData) -> &'a mut [LocalId] {
        std::slice::from_mut(&mut data.out)
    }

    fn visit_memory_store_mut(&mut self, _data: &'a mut MemoryStoreData) -> &'a mut [LocalId] {
        &mut []
    }

    fn visit_set_small_const_mut(&mut self, data: &'a mut SetSmallConstData) -> &'a mut [LocalId] {
        std::slice::from_mut(&mut data.sets)
    }

    fn visit_set_large_const_mut(&mut self, data: &'a mut SetLargeConstData) -> &'a mut [LocalId] {
        std::slice::from_mut(&mut data.sets)
    }

    fn visit_set_data_offset_mut(&mut self, data: &'a mut SetDataOffsetData) -> &'a mut [LocalId] {
        std::slice::from_mut(&mut data.sets)
    }

    fn visit_icall_mut(&mut self, data: &'a mut InternalCallData) -> &'a mut [LocalId] {
        let fn_output_count = self.functions[data.function].outputs as usize;
        let locals = self.locals.take().unwrap();
        let start = data.outs_start.idx();
        &mut locals.as_raw_slice_mut()[start..start + fn_output_count]
    }

    fn visit_void_mut(&mut self) -> &'a mut [LocalId] {
        &mut []
    }
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
