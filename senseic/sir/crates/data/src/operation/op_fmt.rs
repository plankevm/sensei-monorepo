use super::op_data::*;
use crate::{EthIRProgram, index::*, operation::OpVisitor};
use std::fmt;

pub(crate) struct OpFormatter<'fmt, 'ir, W: fmt::Write> {
    pub(crate) ir: &'ir EthIRProgram,
    pub(crate) write: &'fmt mut W,
    pub(crate) mnemonic: &'static str,
}

fn fmt_locals(f: &mut impl fmt::Write, mut locals: impl Iterator<Item = LocalId>) -> fmt::Result {
    let Some(first) = locals.next() else {
        return Ok(());
    };
    write!(f, "${}", first)?;
    for local in locals {
        write!(f, " ${}", local)?;
    }
    Ok(())
}

impl<'d, 'fmt, 'ir, W: fmt::Write> OpVisitor<'d, fmt::Result> for OpFormatter<'fmt, 'ir, W> {
    fn visit_inline_operands<const INS: usize, const OUTS: usize>(
        &mut self,
        operands: &'d InlineOperands<INS, OUTS>,
    ) -> fmt::Result {
        fmt_locals(self.write, operands.outs.iter().copied())?;
        if operands.outs.is_empty() {
            write!(self.write, "{}", self.mnemonic)?;
        } else {
            write!(self.write, " = {}", self.mnemonic)?;
        }
        if !operands.ins.is_empty() {
            write!(self.write, " ")?;
        }
        fmt_locals(self.write, operands.ins.iter().copied())
    }

    fn visit_allocated_ins<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'d AllocatedIns<INS, OUTS>,
    ) -> fmt::Result {
        fmt_locals(self.write, data.outs.iter().copied())?;
        if data.outs.is_empty() {
            write!(self.write, "{}", self.mnemonic)?;
        } else {
            write!(self.write, " = {}", self.mnemonic)?;
        }
        let ins = &self.ir.locals[data.ins_start..data.ins_start + INS as u32];
        if INS > 0 {
            write!(self.write, " ")?;
        }
        fmt_locals(self.write, ins.iter().copied())
    }

    fn visit_static_alloc(&mut self, data: &'d StaticAllocData) -> fmt::Result {
        write!(self.write, "${} = {} {} #{}", data.ptr_out, self.mnemonic, data.size, data.alloc_id)
    }

    fn visit_memory_load(&mut self, data: &'d MemoryLoadData) -> fmt::Result {
        write!(self.write, "${} = {}{} ${}", data.out, self.mnemonic, data.size.bits(), data.ptr)
    }

    fn visit_memory_store(&mut self, data: &'d MemoryStoreData) -> fmt::Result {
        write!(
            self.write,
            "{}{} ${} ${}",
            self.mnemonic,
            data.size.bits(),
            data.ptr(),
            data.value()
        )
    }

    fn visit_set_small_const(&mut self, data: &'d SetSmallConstData) -> fmt::Result {
        write!(self.write, "${} = {} {:#x}", data.sets, self.mnemonic, data.value)
    }

    fn visit_set_large_const(&mut self, data: &'d SetLargeConstData) -> fmt::Result {
        write!(
            self.write,
            "${} = {} {:#x}",
            data.sets, self.mnemonic, self.ir.large_consts[data.value]
        )
    }

    fn visit_set_data_offset(&mut self, data: &'d SetDataOffsetData) -> fmt::Result {
        write!(self.write, "${} = {} .{}", data.sets, self.mnemonic, data.segment_id)
    }

    fn visit_icall(&mut self, data: &'d InternalCallData) -> fmt::Result {
        let ins = &self.ir.locals[data.ins_start..data.outs_start];
        let outs = &self.ir.locals
            [data.outs_start..data.outs_start + self.ir.functions[data.function].get_outputs()];
        fmt_locals(self.write, outs.iter().copied())?;
        if !outs.is_empty() {
            write!(self.write, " = {} @{}", self.mnemonic, data.function)?;
        } else {
            write!(self.write, "{} @{}", self.mnemonic, data.function)?;
        }
        if !ins.is_empty() {
            write!(self.write, " ")?;
        }
        fmt_locals(self.write, ins.iter().copied())
    }

    fn visit_void(&mut self) -> fmt::Result {
        write!(self.write, "{}", self.mnemonic)
    }
}
