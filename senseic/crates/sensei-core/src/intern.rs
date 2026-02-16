use crate::{Idx, IndexVec};
use hashbrown::{DefaultHashBuilder, HashTable, hash_table::Entry};
use std::hash::BuildHasher;

pub struct BytesInterner<I: Idx> {
    owned_bytes: Vec<u8>,
    source_ends: IndexVec<I, u32>,
    bytes_to_idx: HashTable<I>,
    hasher: DefaultHashBuilder,
}

impl<I: Idx> BytesInterner<I> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(entries: usize, bytes: usize) -> Self {
        Self {
            owned_bytes: Vec::with_capacity(bytes),
            source_ends: IndexVec::with_capacity(entries),
            bytes_to_idx: HashTable::with_capacity(entries),
            hasher: DefaultHashBuilder::default(),
        }
    }

    fn get_inner<'a>(
        owned_bytes: &'a [u8],
        source_ends: &'a IndexVec<I, u32>,
        index: I,
    ) -> &'a [u8] {
        let start = if index == I::ZERO { 0 } else { source_ends[index - 1u32] as usize };
        let end = source_ends[index] as usize;
        &owned_bytes[start..end]
    }

    pub fn get(&self, index: I) -> &[u8] {
        Self::get_inner(&self.owned_bytes, &self.source_ends, index)
    }

    pub fn intern(&mut self, bytes: &[u8]) -> I {
        let entry = self.bytes_to_idx.entry(
            self.hasher.hash_one(bytes),
            |&i| Self::get_inner(&self.owned_bytes, &self.source_ends, i) == bytes,
            |&i| self.hasher.hash_one(Self::get_inner(&self.owned_bytes, &self.source_ends, i)),
        );
        match entry {
            Entry::Occupied(i) => *i.get(),
            Entry::Vacant(vacant) => {
                assert!(
                    self.owned_bytes
                        .len()
                        .checked_add(bytes.len())
                        .is_some_and(|new_len| new_len <= u32::MAX as usize),
                    "attempting to have interner hold more than 2^32-1 bytes"
                );
                self.owned_bytes.extend_from_slice(bytes);
                let new_end = self.owned_bytes.len() as u32;
                let new_index = self.source_ends.push(new_end);
                vacant.insert(new_index);
                new_index
            }
        }
    }
}

impl<I: Idx> Default for BytesInterner<I> {
    fn default() -> Self {
        Self {
            owned_bytes: Vec::new(),
            source_ends: IndexVec::new(),
            bytes_to_idx: HashTable::new(),
            hasher: DefaultHashBuilder::default(),
        }
    }
}

pub struct StringInterner<I: Idx>(BytesInterner<I>);

impl<I: Idx> StringInterner<I> {
    pub fn new() -> Self {
        Self(BytesInterner::new())
    }

    pub fn with_capacity(entries: usize, bytes: usize) -> Self {
        Self(BytesInterner::with_capacity(entries, bytes))
    }

    pub fn intern(&mut self, string: &str) -> I {
        self.0.intern(string.as_bytes())
    }

    pub fn get(&self, index: I) -> &str {
        // Safety: BytesInterner guarantees we receive the same bytes we interned.
        unsafe { std::str::from_utf8_unchecked(self.0.get(index)) }
    }
}
