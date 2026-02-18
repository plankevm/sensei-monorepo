use sensei_core::Idx;
use sir_assembler::{Assembler, op};
use sir_data::{EthIRProgram, FunctionId, LocalId};

const EVM_WORD_IN_BYTES: u32 = 0x20;

type EvmMemAddr = u32;

trait StaticMemoryAllocator {
    fn alloc_bytes(&mut self, bytes: u32) -> EvmMemAddr;
}

impl StaticMemoryAllocator for EvmMemAddr {
    fn alloc_bytes(&mut self, bytes: u32) -> EvmMemAddr {
        let addr = *self;
        *self += bytes;
        addr
    }
}

pub struct StaticMemoryLayout {
    pub switch_store: EvmMemAddr,
    pub free_pointer: EvmMemAddr,
    pub basic_block_locals_transfer: EvmMemAddr,
    pub locals_start: EvmMemAddr,
    pub function_return_destinations: EvmMemAddr,
    pub next_free: EvmMemAddr,
}

impl StaticMemoryLayout {
    pub fn new(ir: &EthIRProgram) -> Self {
        let mut next_free = 0;
        let switch_store = next_free.alloc_bytes(EVM_WORD_IN_BYTES);
        let free_pointer = next_free.alloc_bytes(EVM_WORD_IN_BYTES);

        let max_locals_transfer =
            ir.blocks().map(|b| b.outputs().len() as u32).max().expect("at least 1 bb in valid IR");
        let basic_block_locals_transfer =
            next_free.alloc_bytes(max_locals_transfer * EVM_WORD_IN_BYTES);

        let total_locals = ir.next_free_local_id.get();
        let locals_start = next_free.alloc_bytes(total_locals * EVM_WORD_IN_BYTES);
        let function_return_destinations =
            next_free.alloc_bytes(ir.functions.len() as u32 * EVM_WORD_IN_BYTES);

        Self {
            switch_store,
            free_pointer,
            basic_block_locals_transfer,
            locals_start,
            function_return_destinations,
            next_free,
        }
    }

    pub fn get_return_dest_store(&self, function: FunctionId) -> EvmMemAddr {
        self.function_return_destinations + function.get() * EVM_WORD_IN_BYTES
    }

    pub fn emit_transfer_basic_block_outputs(&self, asm: &mut Assembler, input_locals: &[LocalId]) {
        for (transfer_slot, &local) in input_locals.iter().enumerate() {
            let transfer_addr =
                self.basic_block_locals_transfer + transfer_slot as u32 * EVM_WORD_IN_BYTES;
            let local_addr = self.get_local_addr(local);

            asm.push_minimal_u32(transfer_addr);
            asm.push_op_byte(op::MLOAD);
            asm.push_minimal_u32(local_addr);
            asm.push_op_byte(op::MSTORE);
        }
    }

    pub fn get_local_addr(&self, local: LocalId) -> u32 {
        self.locals_start + local.get() * EVM_WORD_IN_BYTES
    }

    pub fn emit_copy_for_basic_block_inputs(&self, asm: &mut Assembler, output_locals: &[LocalId]) {
        for (transfer_slot, &local) in output_locals.iter().enumerate() {
            let transfer_addr =
                self.basic_block_locals_transfer + transfer_slot as u32 * EVM_WORD_IN_BYTES;
            let local_addr = self.get_local_addr(local);

            asm.push_minimal_u32(local_addr);
            asm.push_op_byte(op::MLOAD);
            asm.push_minimal_u32(transfer_addr);
            asm.push_op_byte(op::MSTORE);
        }
    }

    pub fn emit_init_free_pointer(&self, asm: &mut Assembler) {
        asm.push_minimal_u32(self.next_free);
        asm.push_minimal_u32(self.free_pointer);
        asm.push_op_byte(op::MSTORE);
    }
}
