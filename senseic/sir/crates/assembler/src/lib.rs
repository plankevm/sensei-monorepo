use alloy_primitives::U256;
use sensei_core::{IndexVec, Span, X32, index_vec};
pub mod op;

const ASSUMED_MARK_COUNT_WITHOUT_HINT: usize = 128;
const MAX_ASSEMBLER_CONVERGENCE_ITERS: usize = 1024;

pub struct MarkIdMarker;
pub type MarkId = X32<MarkIdMarker>;

pub struct AsmBytesIndex;
pub type AsmBytesIdx = X32<AsmBytesIndex>;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RefSize {
    S1 = 1,
    S2 = 2,
    S3 = 3,
    S4 = 4,
}

#[derive(Debug, Clone, Copy)]
struct DirectMarkRef {
    id: MarkId,
    set_size: Option<RefSize>,
    pushed: bool,
}

#[derive(Debug, Clone, Copy)]
enum StoredAsmSection {
    Mark(MarkId),
    Ops(Span<AsmBytesIdx>),
    Data(Span<AsmBytesIdx>),
    DirectMarkRef(DirectMarkRef),
    UnsizedPushedDeltaRef(Span<MarkId>),
    Size1PushedDeltaRef(Span<MarkId>),
    Size2PushedDeltaRef(Span<MarkId>),
    Size3PushedDeltaRef(Span<MarkId>),
    Size4PushedDeltaRef(Span<MarkId>),
    UnsizedRawDeltaRef(Span<MarkId>),
    Size1RawDeltaRef(Span<MarkId>),
    Size2RawDeltaRef(Span<MarkId>),
    Size3RawDeltaRef(Span<MarkId>),
    Size4RawDeltaRef(Span<MarkId>),
}

fn bytes_to_hold(offset: u32) -> RefSize {
    match offset {
        0x00..=0xff => RefSize::S1,
        0x100..=0xffff => RefSize::S2,
        0x10000..=0xffffff => RefSize::S3,
        0x1000000..=0xffffffff => RefSize::S4,
    }
}

impl From<StoredAsmSection> for AsmSection {
    fn from(value: StoredAsmSection) -> Self {
        match value {
            StoredAsmSection::Mark(id) => AsmSection::Mark(id),
            StoredAsmSection::Ops(span) => AsmSection::Ops(span),
            StoredAsmSection::Data(span) => AsmSection::Data(span),

            StoredAsmSection::DirectMarkRef(mark_ref) => AsmSection::MarkRef(AsmReference {
                mark_ref: MarkReference::Direct(mark_ref.id),
                set_size: mark_ref.set_size,
                pushed: mark_ref.pushed,
            }),
            StoredAsmSection::UnsizedPushedDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, true, None)
            }
            StoredAsmSection::Size1PushedDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, true, Some(RefSize::S1))
            }
            StoredAsmSection::Size2PushedDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, true, Some(RefSize::S2))
            }
            StoredAsmSection::Size3PushedDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, true, Some(RefSize::S3))
            }
            StoredAsmSection::Size4PushedDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, true, Some(RefSize::S4))
            }
            StoredAsmSection::UnsizedRawDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, false, None)
            }
            StoredAsmSection::Size1RawDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, false, Some(RefSize::S1))
            }
            StoredAsmSection::Size2RawDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, false, Some(RefSize::S2))
            }
            StoredAsmSection::Size3RawDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, false, Some(RefSize::S3))
            }
            StoredAsmSection::Size4RawDeltaRef(delta_span) => {
                AsmSection::delta_ref(delta_span, false, Some(RefSize::S4))
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum AsmSection {
    Mark(MarkId),
    Ops(Span<AsmBytesIdx>),
    Data(Span<AsmBytesIdx>),
    MarkRef(AsmReference),
}

impl AsmSection {
    fn delta_ref(delta_span: Span<MarkId>, pushed: bool, set_size: Option<RefSize>) -> Self {
        Self::MarkRef(AsmReference { mark_ref: MarkReference::Delta(delta_span), set_size, pushed })
    }

    fn min_compiled_size(&self) -> u32 {
        match self {
            AsmSection::Mark(_) => 0,
            AsmSection::Ops(bytes_span) | AsmSection::Data(bytes_span) => {
                bytes_span.end - bytes_span.start
            }
            AsmSection::MarkRef(mark_ref) => match (mark_ref.set_size, mark_ref.pushed) {
                (Some(set_size), true) => set_size as u32 + 1,
                (Some(set_size), false) => set_size as u32,
                (None, _) => 1,
            },
        }
    }

    fn compiled_size(&self, mark_map: &IndexVec<MarkIdMarker, u32>) -> Option<u32> {
        match self {
            AsmSection::Mark(_) => Some(0),
            AsmSection::Ops(bytes_span) | AsmSection::Data(bytes_span) => {
                Some(bytes_span.end - bytes_span.start)
            }
            AsmSection::MarkRef(mark_ref) => {
                let value = match mark_ref.mark_ref {
                    MarkReference::Direct(id) => mark_map[id],
                    MarkReference::Delta(span) => mark_map[span.end] - mark_map[span.start],
                };
                let ref_size = bytes_to_hold(value);
                match (mark_ref.set_size, mark_ref.pushed) {
                    (Some(set_size), _) if set_size < ref_size => None,
                    (Some(set_size), true) => Some(set_size as u32 + 1),
                    (Some(set_size), false) => Some(set_size as u32),
                    (None, true) if value == 0 => Some(1),
                    (None, true) => Some(1 + ref_size as u32),
                    (None, false) => Some(ref_size as u32),
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum MarkReference {
    Direct(MarkId),
    Delta(Span<MarkId>),
}

#[derive(Debug, Clone, Copy)]
pub struct AsmReference {
    pub mark_ref: MarkReference,
    pub set_size: Option<RefSize>,
    pub pushed: bool,
}

impl AsmReference {
    pub fn new_direct(id: MarkId) -> Self {
        Self { mark_ref: MarkReference::Direct(id), set_size: None, pushed: true }
    }

    pub fn new_delta(start: MarkId, end: MarkId) -> Self {
        Self { mark_ref: MarkReference::Delta(Span { start, end }), set_size: None, pushed: true }
    }
}

const _ASSERT_STORED_ASM_SECTION_MEM_SIZE: () = const {
    assert!(std::mem::size_of::<StoredAsmSection>() == 12);
    assert!(std::mem::align_of::<StoredAsmSection>() == 4);
};

#[derive(Debug, Clone)]
pub struct Assembler {
    bytes: IndexVec<AsmBytesIndex, u8>,
    sections: Vec<StoredAsmSection>,
}

#[derive(Debug, Clone)]
pub enum AssembleError {
    RefHasTooSmallSetSize(usize),
}

impl Assembler {
    pub fn with_capacity(bytes_capacity: usize, sections_capacity: usize) -> Self {
        Self {
            bytes: IndexVec::with_capacity(bytes_capacity),
            sections: Vec::with_capacity(sections_capacity),
        }
    }

    fn iter_sections(&self) -> impl Iterator<Item = AsmSection> {
        self.sections.iter().map(|&section| section.into())
    }

    pub fn push_mark(&mut self, mark: MarkId) {
        self.sections.push(StoredAsmSection::Mark(mark))
    }

    pub fn push_op_byte(&mut self, byte: u8) {
        match self.sections.last_mut() {
            Some(StoredAsmSection::Ops(bytes_span)) => {
                debug_assert!(bytes_span.end == self.bytes.len_idx(), "span out of sync");
                self.bytes.push(byte);
                bytes_span.end = self.bytes.len_idx();
            }
            _ => {
                let start = self.bytes.len_idx();
                self.bytes.push(byte);
                let end = self.bytes.len_idx();
                self.sections.push(StoredAsmSection::Ops(Span { start, end }));
            }
        }
    }

    pub fn push_minimal_u256(&mut self, value: U256) {
        let push_size = 32 - value.leading_zeros() / 8;
        debug_assert!(push_size <= u8::MAX as usize);
        let push_op = op::PUSH1 + push_size as u8 - 1;
        debug_assert!(
            (value == U256::ZERO) == (push_size == 0) && (push_size == 0) == (push_op == op::PUSH0),
            "push0 handled incorrectly"
        );
        self.push_op_byte(push_op);
        let bytes = value.to_le_bytes::<32>();
        for i in (0..push_size).rev() {
            self.push_op_byte(bytes[i]);
        }
    }

    pub fn push_minimal_u64(&mut self, value: u64) {
        let push_size = 8 - value.leading_zeros() as u8 / 8;
        let push_op = op::PUSH1 + push_size - 1;
        debug_assert!(
            (value == 0) == (push_size == 0) && (push_size == 0) == (push_op == op::PUSH0),
            "push0 handled incorrectly"
        );
        self.push_op_byte(push_op);
        let bytes = value.to_le_bytes();
        for i in (0..push_size).rev() {
            self.push_op_byte(bytes[i as usize]);
        }
    }

    pub fn push_minimal_u32(&mut self, value: u32) {
        let push_size = 4 - value.leading_zeros() as u8 / 8;
        let push_op = op::PUSH1 + push_size - 1;
        debug_assert!(
            (value == 0) == (push_size == 0) && (push_size == 0) == (push_op == op::PUSH0),
            "push0 handled incorrectly"
        );
        self.push_op_byte(push_op);
        let bytes = value.to_le_bytes();
        for i in (0..push_size).rev() {
            self.push_op_byte(bytes[i as usize]);
        }
    }

    pub fn push_data(&mut self, data: &[u8]) {
        match self.sections.last_mut() {
            Some(StoredAsmSection::Data(bytes_span)) => {
                debug_assert!(bytes_span.end == self.bytes.len_idx(), "span out of sync");
                self.bytes.extend_from_slice(data);
                bytes_span.end = self.bytes.len_idx();
            }
            _ => {
                let start = self.bytes.len_idx();
                self.bytes.extend_from_slice(data);
                let end = self.bytes.len_idx();
                self.sections.push(StoredAsmSection::Data(Span { start, end }));
            }
        }
    }

    pub fn push_reference(&mut self, asm_ref: AsmReference) {
        let delta_span = match asm_ref.mark_ref {
            MarkReference::Direct(id) => {
                self.sections.push(StoredAsmSection::DirectMarkRef(DirectMarkRef {
                    id,
                    set_size: asm_ref.set_size,
                    pushed: asm_ref.pushed,
                }));
                return;
            }
            MarkReference::Delta(span) => span,
        };
        let section = if asm_ref.pushed {
            match asm_ref.set_size {
                None => StoredAsmSection::UnsizedPushedDeltaRef(delta_span),
                Some(RefSize::S1) => StoredAsmSection::Size1PushedDeltaRef(delta_span),
                Some(RefSize::S2) => StoredAsmSection::Size2PushedDeltaRef(delta_span),
                Some(RefSize::S3) => StoredAsmSection::Size3PushedDeltaRef(delta_span),
                Some(RefSize::S4) => StoredAsmSection::Size4PushedDeltaRef(delta_span),
            }
        } else {
            match asm_ref.set_size {
                None => StoredAsmSection::UnsizedRawDeltaRef(delta_span),
                Some(RefSize::S1) => StoredAsmSection::Size1RawDeltaRef(delta_span),
                Some(RefSize::S2) => StoredAsmSection::Size2RawDeltaRef(delta_span),
                Some(RefSize::S3) => StoredAsmSection::Size3RawDeltaRef(delta_span),
                Some(RefSize::S4) => StoredAsmSection::Size4RawDeltaRef(delta_span),
            }
        };
        self.sections.push(section);
    }

    fn converge_mark_offsets(
        &self,
        mark_to_offset: &mut IndexVec<MarkIdMarker, u32>,
    ) -> Result<(), AssembleError> {
        let mut min_size = 0;
        for section in self.iter_sections() {
            if let AsmSection::Mark(id) = section {
                let size_for_id = id.get() as usize + 1;
                // Maintain `length == capacity`.
                let additional_to_reserve = size_for_id.saturating_sub(mark_to_offset.len());
                mark_to_offset.reserve(additional_to_reserve);
                let cap = mark_to_offset.capacity();
                mark_to_offset.resize(cap, 0);
                mark_to_offset[id] = min_size;
            }
            min_size += section.min_compiled_size();
        }

        for _ in 0..MAX_ASSEMBLER_CONVERGENCE_ITERS {
            let mut converged = true;
            let mut current_code_offset = 0;
            for (i, section) in self.iter_sections().enumerate() {
                if let AsmSection::Mark(id) = section {
                    let prev_offset = mark_to_offset[id];
                    if prev_offset != current_code_offset {
                        converged = false;
                        mark_to_offset[id] = current_code_offset;
                    }
                }

                current_code_offset += section
                    .compiled_size(mark_to_offset)
                    .ok_or(AssembleError::RefHasTooSmallSetSize(i))?;
            }

            if converged {
                return Ok(());
            }
        }

        unreachable!("assembly didn't converge")
    }

    pub fn assemble(
        &self,
        result: &mut Vec<u8>,
        mark_id_count_hint: Option<usize>,
    ) -> Result<IndexVec<MarkIdMarker, u32>, AssembleError> {
        let mut mark_to_offset: IndexVec<MarkIdMarker, u32> =
            index_vec![0; mark_id_count_hint.unwrap_or(ASSUMED_MARK_COUNT_WITHOUT_HINT)];

        self.converge_mark_offsets(&mut mark_to_offset)?;

        for stored_section in self.iter_sections() {
            match stored_section {
                AsmSection::Mark(_) => { /* Marks are sizeless */ }
                AsmSection::Ops(bytes) | AsmSection::Data(bytes) => {
                    result.extend_from_slice(&self.bytes[bytes.start..bytes.end]);
                }
                AsmSection::MarkRef(mark_ref) => {
                    let value = match mark_ref.mark_ref {
                        MarkReference::Direct(id) => mark_to_offset[id],
                        MarkReference::Delta(span) => {
                            mark_to_offset[span.end] - mark_to_offset[span.start]
                        }
                    };
                    if value == 0 && mark_ref.set_size.is_none() && mark_ref.pushed {
                        result.push(op::PUSH0);
                    } else {
                        let ref_size = bytes_to_hold(value);
                        assert!(
                            mark_ref.set_size.is_none_or(|set_size| set_size >= ref_size),
                            "reached code emission with invalid ref size"
                        );
                        let ref_size = mark_ref.set_size.unwrap_or(ref_size);
                        let value_bytes = value.to_le_bytes();
                        if mark_ref.pushed {
                            result.push(op::PUSH1 + ref_size as u8 - 1);
                        }
                        for i in (0..ref_size as usize).rev() {
                            result.push(value_bytes[i]);
                        }
                    }
                }
            }
        }

        Ok(mark_to_offset)
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::hex;
    use sensei_core::IncIterable;

    use super::*;

    #[test]
    fn test_basic_assembly() {
        let mut next_mark_id = MarkId::ZERO;

        let main = next_mark_id.get_and_inc();
        let mut asm = Assembler::with_capacity(256, 16);

        asm.push_reference(AsmReference::new_direct(main));
        asm.push_data(&[0x11; 253]);
        asm.push_mark(main);
        asm.push_op_byte(op::STOP);
        asm.push_op_byte(op::STOP);

        let mut result = Vec::with_capacity(300);
        asm.assemble(&mut result, Some(2)).unwrap();

        assert_eq!(
            hex::encode(result),
            "60ff111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110000"
        );
    }

    #[test]
    fn test_pushes() {
        let mut asm = Assembler::with_capacity(256, 16);

        asm.push_minimal_u64(0);
        asm.push_minimal_u64(1);
        asm.push_minimal_u64(0xff);
        asm.push_minimal_u64(0x100);
        asm.push_minimal_u64(0x3103);
        asm.push_minimal_u64(0x10000);
        asm.push_minimal_u64(0x310ee);
        asm.push_minimal_u64(0xffffff);
        asm.push_minimal_u64(0x1000000);
        asm.push_minimal_u64(0x100000000000000);
        asm.push_minimal_u64(0xff0000000ccccccc);

        let mut result = Vec::with_capacity(300);
        asm.assemble(&mut result, Some(2)).unwrap();

        assert_eq!(
            hex::encode(result),
            "5f600160ff61010061310362010000620310ee62ffffff630100000067010000000000000067ff0000000ccccccc"
        );
    }
}
