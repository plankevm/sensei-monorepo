use sensei_core::{DenseIndexSet, Idx, IncIterable};
use sir_assembler::{AsmReference, Assembler, MarkId, MarkReference, op};
use sir_data::{BasicBlockId, Control, DataId, EthIRProgram, FunctionId, LocalId, Span};

use crate::static_memory_layout::StaticMemoryLayout;

mod operations;
mod static_memory_layout;

const ASM_BYTES_CAPACITY: usize = 20_000;
const ASM_SECTIONS_CAPACITY: usize = 512;

pub(crate) struct MarkMap {
    init_basic_block_marks_start: MarkId,
    run_basic_block_marks_start: MarkId,
    data_marks_start: MarkId,
    runtime_start: MarkId,
    initcode_end: MarkId,
    next_mark_id: MarkId,
}

impl MarkMap {
    fn new(ir: &EthIRProgram) -> Self {
        let mut next_mark_id = MarkId::ZERO;

        let init_basic_block_marks_start = next_mark_id;
        next_mark_id += ir.basic_blocks.len() as u32;

        let run_basic_block_marks_start = next_mark_id;
        next_mark_id += ir.basic_blocks.len() as u32;

        let data_marks_start = next_mark_id;
        next_mark_id += ir.data_segments_start.len() as u32;

        let runtime_start = next_mark_id.get_and_inc();
        let bytecode_end = next_mark_id.get_and_inc();

        Self {
            init_basic_block_marks_start,
            run_basic_block_marks_start,
            data_marks_start,
            runtime_start,
            initcode_end: bytecode_end,
            next_mark_id,
        }
    }

    pub fn allocate_mark(&mut self) -> MarkId {
        self.next_mark_id.get_and_inc()
    }

    pub fn get_init_bb_mark(&self, bb_id: BasicBlockId) -> MarkId {
        self.init_basic_block_marks_start + bb_id.get()
    }

    pub fn get_run_bb_mark(&self, bb_id: BasicBlockId) -> MarkId {
        self.run_basic_block_marks_start + bb_id.get()
    }

    pub fn get_data_mark(&self, data_id: DataId) -> MarkId {
        self.data_marks_start + data_id.get()
    }
}

pub(crate) struct Translator<'ir> {
    pub ir: &'ir EthIRProgram,
    pub memory_layout: StaticMemoryLayout,
    pub mark_map: MarkMap,
    pub translated_bbs: DenseIndexSet<BasicBlockId>,
    pub bbs_to_be_translated: Vec<(FunctionId, BasicBlockId)>,
    pub translating_init_code: bool,
    pub asm: Assembler,
}

impl<'ir> Translator<'ir> {
    pub(crate) fn emit_free_ptr_load(&mut self) {
        self.asm.push_minimal_u32(self.memory_layout.free_pointer);
        self.asm.push_op_byte(op::MLOAD);
    }

    pub(crate) fn emit_local_load(&mut self, local: LocalId) {
        self.asm.push_minimal_u32(self.memory_layout.get_local_addr(local));
        self.asm.push_op_byte(op::MLOAD);
    }

    pub(crate) fn emit_local_store(&mut self, local: LocalId) {
        self.asm.push_minimal_u32(self.memory_layout.get_local_addr(local));
        self.asm.push_op_byte(op::MSTORE);
    }

    pub(crate) fn emit_code_offset_push(&mut self, offset_mark: MarkId) {
        let mark_ref = if self.translating_init_code {
            MarkReference::Direct(offset_mark)
        } else {
            MarkReference::Delta(Span::new(self.mark_map.runtime_start, offset_mark))
        };
        self.asm.push_reference(AsmReference { mark_ref, set_size: None, pushed: true });
    }

    fn new(ir: &'ir EthIRProgram) -> Self {
        let memory_layout = StaticMemoryLayout::new(ir);
        let asm = Assembler::with_capacity(ASM_BYTES_CAPACITY, ASM_SECTIONS_CAPACITY);
        let translated_bbs = DenseIndexSet::with_capacity_in_bits(ir.basic_blocks.len());
        let bbs_to_be_translated = Vec::with_capacity(8);
        let mark_map = MarkMap::new(ir);
        Self {
            ir,
            memory_layout,
            asm,
            bbs_to_be_translated,
            mark_map,
            translated_bbs,
            translating_init_code: true,
        }
    }

    fn get_bb_mark(&self, bb_id: BasicBlockId) -> MarkId {
        if self.translating_init_code {
            self.mark_map.get_init_bb_mark(bb_id)
        } else {
            self.mark_map.get_run_bb_mark(bb_id)
        }
    }

    fn emit_undefined_behavior_error(&mut self) {
        self.asm.push_minimal_u32(0xbadbad);
        self.asm.push_op_byte(op::PUSH0);
        self.asm.push_op_byte(op::MSTORE);
        self.asm.push_minimal_u32(3);
        self.asm.push_minimal_u32(32 - 3);
        self.asm.push_op_byte(op::REVERT);
    }

    fn translate_basic_blocks_from_entry_point(&mut self, entry_point: FunctionId) {
        let entry_basic_block = self.ir.functions[entry_point].entry();
        self.bbs_to_be_translated.push((entry_point, entry_basic_block));

        while let Some((func, bb_id)) = self.bbs_to_be_translated.pop() {
            if !self.translated_bbs.add(bb_id) {
                continue;
            }

            self.asm.push_mark(self.get_bb_mark(bb_id));
            self.asm.push_op_byte(op::JUMPDEST);

            let basic_block = self.ir.basic_blocks[bb_id].clone();
            self.memory_layout.emit_transfer_basic_block_outputs(
                &mut self.asm,
                &self.ir.locals[basic_block.inputs],
            );
            for op in &self.ir.operations[basic_block.operations] {
                operations::translate_operation(self, op.clone());
            }
            self.memory_layout.emit_copy_for_basic_block_inputs(
                &mut self.asm,
                &self.ir.locals[basic_block.outputs],
            );

            self.bbs_to_be_translated
                .extend(basic_block.control.iter_outgoing(self.ir).map(|bb| (func, bb)));

            match basic_block.control {
                Control::LastOpTerminates => {}
                Control::InternalReturn => {
                    let return_dest_loc = self.memory_layout.get_return_dest_store(func);
                    self.asm.push_minimal_u32(return_dest_loc);
                    self.asm.push_op_byte(op::MLOAD);
                    self.asm.push_op_byte(op::JUMP);
                }
                Control::ContinuesTo(to) => {
                    self.emit_code_offset_push(self.get_bb_mark(to));
                    self.asm.push_op_byte(op::JUMP);
                }
                Control::Branches(branch) => {
                    self.emit_local_load(branch.condition);
                    self.emit_code_offset_push(self.get_bb_mark(branch.non_zero_target));
                    self.asm.push_op_byte(op::JUMPI);
                    self.emit_code_offset_push(self.get_bb_mark(branch.zero_target));
                    self.asm.push_op_byte(op::JUMP);
                }
                Control::Switch(switch) => {
                    self.emit_local_load(switch.condition);
                    self.asm.push_minimal_u32(self.memory_layout.switch_store);
                    self.asm.push_op_byte(op::MSTORE);

                    let cases = &self.ir.cases[switch.cases];
                    for (&value, &bb) in
                        cases.get_values(self.ir).iter().zip(cases.get_bb_ids(self.ir))
                    {
                        self.asm.push_minimal_u32(self.memory_layout.switch_store);
                        self.asm.push_op_byte(op::MLOAD);
                        self.asm.push_minimal_u256(value);
                        self.asm.push_op_byte(op::EQ);
                        self.emit_code_offset_push(self.get_bb_mark(bb));
                        self.asm.push_op_byte(op::JUMPI);
                    }

                    if let Some(fallback) = switch.fallback {
                        self.emit_code_offset_push(self.get_bb_mark(fallback));
                        self.asm.push_op_byte(op::JUMP);
                    } else {
                        self.emit_undefined_behavior_error();
                    };
                }
            }
        }
    }
}

pub fn ir_to_bytecode(ir: &EthIRProgram, result: &mut Vec<u8>) {
    let mut translator = Translator::new(ir);

    translator.translating_init_code = true;
    translator.memory_layout.emit_init_free_pointer(&mut translator.asm);
    translator.translate_basic_blocks_from_entry_point(ir.init_entry);

    translator.translating_init_code = false;
    translator.asm.push_mark(translator.mark_map.runtime_start);
    if let Some(main_entry) = ir.main_entry {
        translator.translate_basic_blocks_from_entry_point(main_entry);
    }

    for data_id in sensei_core::Span::new(DataId::ZERO, ir.data_segments_start.len_idx()).iter() {
        let bytes = &ir.data_bytes[ir.get_segment_span(data_id)];
        let mark = translator.mark_map.get_data_mark(data_id);
        translator.asm.push_mark(mark);
        translator.asm.push_data(bytes);
    }

    translator.asm.push_mark(translator.mark_map.initcode_end);

    let _mark_to_offset = translator
        .asm
        .assemble(result, Some(translator.mark_map.next_mark_id.get() as usize))
        .expect("debug backend produces valid assembly");
}
