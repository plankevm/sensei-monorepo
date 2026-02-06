use crate::Translator;
use sir_assembler::{AsmReference, op};
use sir_data::{LocalId, operation::*};

fn op_kind_to_direct_op(kind: OperationKind) -> Option<u8> {
    let evm_op = match kind {
        OperationKind::DynamicAllocZeroed
        | OperationKind::DynamicAllocAnyBytes
        | OperationKind::AcquireFreePointer
        | OperationKind::StaticAllocZeroed
        | OperationKind::StaticAllocAnyBytes
        | OperationKind::MemoryLoad
        | OperationKind::MemoryStore
        | OperationKind::SetCopy
        | OperationKind::SetSmallConst
        | OperationKind::SetLargeConst
        | OperationKind::SetDataOffset
        | OperationKind::Noop
        | OperationKind::InternalCall
        | OperationKind::RuntimeStartOffset
        | OperationKind::InitEndOffset
        | OperationKind::RuntimeLength => return None,

        // ========== EVM Arithmetic ==========
        OperationKind::Add => op::ADD,
        OperationKind::Mul => op::MUL,
        OperationKind::Sub => op::SUB,
        OperationKind::Div => op::DIV,
        OperationKind::SDiv => op::SDIV,
        OperationKind::Mod => op::MOD,
        OperationKind::SMod => op::SMOD,
        OperationKind::AddMod => op::ADDMOD,
        OperationKind::MulMod => op::MULMOD,
        OperationKind::Exp => op::EXP,
        OperationKind::SignExtend => op::SIGNEXTEND,

        // ========== EVM Comparison & Bitwise Logic ==========
        OperationKind::Lt => op::LT,
        OperationKind::Gt => op::GT,
        OperationKind::SLt => op::SLT,
        OperationKind::SGt => op::SGT,
        OperationKind::Eq => op::EQ,
        OperationKind::IsZero => op::ISZERO,
        OperationKind::And => op::AND,
        OperationKind::Or => op::OR,
        OperationKind::Xor => op::XOR,
        OperationKind::Not => op::NOT,
        OperationKind::Byte => op::BYTE,
        OperationKind::Shl => op::SHL,
        OperationKind::Shr => op::SHR,
        OperationKind::Sar => op::SAR,

        // ========== EVM Keccak-256 ==========
        OperationKind::Keccak256 => op::KECCAK256,

        // ========== EVM Environment Information ==========
        OperationKind::Address => op::ADDRESS,
        OperationKind::Balance => op::BALANCE,
        OperationKind::Origin => op::ORIGIN,
        OperationKind::Caller => op::CALLER,
        OperationKind::CallValue => op::CALLVALUE,
        OperationKind::CallDataLoad => op::CALLDATALOAD,
        OperationKind::CallDataSize => op::CALLDATASIZE,
        OperationKind::CallDataCopy => op::CALLDATACOPY,
        OperationKind::CodeSize => op::CODESIZE,
        OperationKind::CodeCopy => op::CODECOPY,
        OperationKind::GasPrice => op::GASPRICE,
        OperationKind::ExtCodeSize => op::EXTCODESIZE,
        OperationKind::ExtCodeCopy => op::EXTCODECOPY,
        OperationKind::ReturnDataSize => op::RETURNDATASIZE,
        OperationKind::ReturnDataCopy => op::RETURNDATACOPY,
        OperationKind::ExtCodeHash => op::EXTCODEHASH,
        OperationKind::Gas => op::GAS,

        // ========== EVM Block Information ==========
        OperationKind::BlockHash => op::BLOCKHASH,
        OperationKind::Coinbase => op::COINBASE,
        OperationKind::Timestamp => op::TIMESTAMP,
        OperationKind::Number => op::NUMBER,
        OperationKind::Difficulty => op::PREVRANDAO,
        OperationKind::GasLimit => op::GASLIMIT,
        OperationKind::ChainId => op::CHAINID,
        OperationKind::SelfBalance => op::SELFBALANCE,
        OperationKind::BaseFee => op::BASEFEE,
        OperationKind::BlobHash => op::BLOBHASH,
        OperationKind::BlobBaseFee => op::BLOBBASEFEE,

        // ========== EVM State Manipulation ==========
        OperationKind::SLoad => op::SLOAD,
        OperationKind::SStore => op::SSTORE,
        OperationKind::TLoad => op::TLOAD,
        OperationKind::TStore => op::TSTORE,

        // ========== Memory Manipulation ==========
        OperationKind::MemoryCopy => op::MCOPY,

        // ========== EVM Logging Operations ==========
        OperationKind::Log0 => op::LOG0,
        OperationKind::Log1 => op::LOG1,
        OperationKind::Log2 => op::LOG2,
        OperationKind::Log3 => op::LOG3,
        OperationKind::Log4 => op::LOG4,

        // ========== EVM System Calls ==========
        OperationKind::Create => op::CREATE,
        OperationKind::Create2 => op::CREATE2,
        OperationKind::Call => op::CALL,
        OperationKind::CallCode => op::CALLCODE,
        OperationKind::DelegateCall => op::DELEGATECALL,
        OperationKind::StaticCall => op::STATICCALL,
        OperationKind::Return => op::RETURN,
        OperationKind::Stop => op::STOP,
        OperationKind::Revert => op::REVERT,
        OperationKind::Invalid => op::INVALID,
        OperationKind::SelfDestruct => op::SELFDESTRUCT,
    };
    Some(evm_op)
}

struct OpcodeTranslator<'t, 'ir> {
    translator: &'t mut Translator<'ir>,
    op_kind: OperationKind,
    evm_op: Option<u8>,
}

impl<'t, 'ir> OpcodeTranslator<'t, 'ir> {
    fn emit_simple_operation(&mut self, evm_op: u8, inputs: &[LocalId], outputs: &[LocalId]) {
        for &input in inputs.iter().rev() {
            self.translator.emit_local_load(input);
        }
        self.translator.asm.push_op_byte(evm_op);
        for &output in outputs.iter() {
            self.translator.emit_local_store(output);
        }
    }

    fn emit_dynamic_memory_alloc(&mut self, size_local: LocalId, ptr_out_local: LocalId) {
        self.translator.emit_free_ptr_load(); // [free_ptr]
        self.translator.asm.push_op_byte(op::DUP1); // [free_ptr, free_ptr]
        self.translator.emit_local_load(size_local); // [size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::DUP1); // [size, size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::CALLDATASIZE); // [cdz, size, size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::DUP4); // [free_ptr, cdz, size, size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::CALLDATACOPY); // [size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::ADD); // [free_ptr', free_ptr]
        self.translator.asm.push_minimal_u32(self.translator.memory_layout.free_pointer);
        // [free_ptr_loc, free_ptr', free_ptr]
        self.translator.asm.push_op_byte(op::MSTORE); // [free_ptr]
        self.translator.emit_local_store(ptr_out_local);
    }

    fn emit_static_memory_alloc(&mut self, size: u32, ptr_out_local: LocalId) {
        self.translator.emit_free_ptr_load(); // [free_ptr]
        self.translator.asm.push_op_byte(op::DUP1); // [free_ptr, free_ptr]
        self.translator.asm.push_minimal_u32(size); // [size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::DUP1); // [size, size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::CALLDATASIZE); // [cdz, size, size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::DUP4); // [free_ptr, cdz, size, size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::CALLDATACOPY); // [size, free_ptr, free_ptr]
        self.translator.asm.push_op_byte(op::ADD); // [free_ptr', free_ptr]
        self.translator.asm.push_minimal_u32(self.translator.memory_layout.free_pointer);
        // [free_ptr_loc, free_ptr', free_ptr]
        self.translator.asm.push_op_byte(op::MSTORE); // [free_ptr]
        self.translator.emit_local_store(ptr_out_local);
    }
}

impl<'d, 't, 'ir> OpVisitor<'d, ()> for OpcodeTranslator<'t, 'ir> {
    fn visit_inline_operands<const INS: usize, const OUTS: usize>(
        &mut self,
        operands: &'d InlineOperands<INS, OUTS>,
    ) {
        match self.op_kind {
            OperationKind::DynamicAllocZeroed | OperationKind::DynamicAllocAnyBytes => {
                self.emit_dynamic_memory_alloc(operands.ins[0], operands.outs[0])
            }
            OperationKind::AcquireFreePointer => {
                self.translator.emit_free_ptr_load();
                self.translator.emit_local_store(operands.outs[0]);
            }
            OperationKind::SetCopy => {
                self.translator.emit_local_load(operands.ins[0]);
                self.translator.emit_local_store(operands.outs[0]);
            }
            OperationKind::RuntimeStartOffset => {
                debug_assert!(
                    self.translator.translating_init_code,
                    "unexpected runtime_start_offset in run code"
                );
                self.translator.asm.push_reference(AsmReference::new_direct(
                    self.translator.mark_map.runtime_start,
                ));
                self.translator.emit_local_store(operands.outs[0]);
            }
            OperationKind::InitEndOffset => {
                debug_assert!(
                    self.translator.translating_init_code,
                    "unexpected init_end_offset in run code"
                );
                self.translator.asm.push_reference(AsmReference::new_direct(
                    self.translator.mark_map.initcode_end,
                ));
                self.translator.emit_local_store(operands.outs[0]);
            }
            OperationKind::RuntimeLength => {
                self.translator.asm.push_reference(AsmReference::new_delta(
                    self.translator.mark_map.runtime_start,
                    self.translator.mark_map.initcode_end,
                ));
                self.translator.emit_local_store(operands.outs[0])
            }
            _ => {
                let evm_op = self
                    .evm_op
                    .unwrap_or_else(|| panic!("Expected {:?} to be EVM op", self.op_kind));
                self.emit_simple_operation(evm_op, &operands.ins, &operands.outs);
            }
        }
    }

    fn visit_allocated_ins<const INS: usize, const OUTS: usize>(
        &mut self,
        data: &'d AllocatedIns<INS, OUTS>,
    ) {
        let evm_op = self.evm_op.expect("all allocated input operand ops to be EVM");
        self.emit_simple_operation(evm_op, data.get_inputs(self.translator.ir), &data.outs);
    }

    fn visit_void(&mut self) {
        if let Some(evm_op) = self.evm_op {
            self.translator.asm.push_op_byte(evm_op);
        } else {
            debug_assert_eq!(self.op_kind, OperationKind::Noop, "expected only noop to have void");
        };
    }

    fn visit_static_alloc(&mut self, data: &'d StaticAllocData) {
        self.emit_static_memory_alloc(data.size, data.ptr_out);
    }

    fn visit_memory_load(&mut self, data: &'d MemoryLoadData) {
        let load_size = data.size as u32;
        self.translator.emit_local_load(data.ptr);
        self.translator.asm.push_op_byte(op::MLOAD);
        self.translator.asm.push_minimal_u32(256 - load_size * 8);
        self.translator.asm.push_op_byte(op::SHR);
        self.translator.emit_local_store(data.out);
    }

    fn visit_memory_store(&mut self, data: &'d MemoryStoreData) {
        let load_size = data.size as u32;
        let shift_to_clean_word = load_size * 8;
        self.translator.emit_local_load(data.ptr()); // [ptr]
        self.translator.asm.push_op_byte(op::DUP1); // [ptr, ptr]
        self.translator.asm.push_op_byte(op::MLOAD); // [current_word, ptr]
        self.translator.asm.push_minimal_u32(shift_to_clean_word); // [shift, current_word, ptr]
        self.translator.asm.push_op_byte(op::SHL); // [current_word << shift, ptr]
        self.translator.asm.push_minimal_u32(shift_to_clean_word); // [shift, current_word << shift, ptr]
        self.translator.asm.push_op_byte(op::SHR); // [cleaned_word, ptr]
        self.translator.emit_local_load(data.value()); // [value, cleaned_word, ptr]
        self.translator.asm.push_minimal_u32(256 - load_size * 8); // [value_shift, value, cleaned_word, ptr]
        self.translator.asm.push_op_byte(op::SHL); // [shifted_value, cleaned_word, ptr]
        self.translator.asm.push_op_byte(op::OR); // [updated_word, ptr]
        self.translator.asm.push_op_byte(op::SWAP1); // [ptr, updated_word]
        self.translator.asm.push_op_byte(op::MSTORE); // []
    }

    fn visit_set_small_const(&mut self, data: &'d SetSmallConstData) {
        self.translator.asm.push_minimal_u32(data.value);
        self.translator.emit_local_store(data.sets);
    }

    fn visit_set_large_const(&mut self, data: &'d SetLargeConstData) {
        self.translator.asm.push_minimal_u256(self.translator.ir.large_consts[data.value]);
        self.translator.emit_local_store(data.sets);
    }

    fn visit_set_data_offset(&mut self, data: &'d SetDataOffsetData) {
        let data_offset_mark = self.translator.mark_map.get_data_mark(data.segment_id);
        self.translator.emit_code_offset_push(data_offset_mark);
        self.translator.emit_local_store(data.sets);
    }

    fn visit_icall(&mut self, data: &'d InternalCallData) {
        self.translator.memory_layout.emit_copy_for_basic_block_inputs(
            &mut self.translator.asm,
            data.get_inputs(self.translator.ir),
        );

        let return_mark = self.translator.mark_map.allocate_mark();
        let return_store_loc = self.translator.memory_layout.get_return_dest_store(data.function);
        self.translator.emit_code_offset_push(return_mark);
        self.translator.asm.push_minimal_u32(return_store_loc);
        self.translator.asm.push_op_byte(op::MSTORE);
        let func_entry_bb = self.translator.ir.functions[data.function].entry();
        let func_entry_bb_mark = self.translator.get_bb_mark(func_entry_bb);
        self.translator.emit_code_offset_push(func_entry_bb_mark);
        self.translator.asm.push_op_byte(op::JUMP);
        self.translator.asm.push_mark(return_mark);
        self.translator.asm.push_op_byte(op::JUMPDEST);

        self.translator.memory_layout.emit_transfer_basic_block_outputs(
            &mut self.translator.asm,
            data.get_outputs(self.translator.ir),
        );

        self.translator.bbs_to_be_translated.push((data.function, func_entry_bb));
    }
}

pub(crate) fn translate_operation(translator: &mut Translator, op: Operation) {
    let evm_op = op_kind_to_direct_op(op.kind());
    let mut opcode_translator = OpcodeTranslator { translator, op_kind: op.kind(), evm_op };
    op.visit_data(&mut opcode_translator);
}
