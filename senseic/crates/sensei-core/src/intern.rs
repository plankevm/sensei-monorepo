use crate::{Idx, list_of_lists::ListOfLists};
use hashbrown::{DefaultHashBuilder, HashTable, hash_table::Entry};
use std::hash::BuildHasher;

pub struct BytesInterner<I: Idx> {
    bytes: ListOfLists<I, u8>,
    bytes_to_idx: HashTable<I>,
    hasher: DefaultHashBuilder,
}

impl<I: Idx> BytesInterner<I> {
    pub fn new() -> Self {
        Self {
            bytes: ListOfLists::new(),
            bytes_to_idx: HashTable::new(),
            hasher: DefaultHashBuilder::default(),
        }
    }

    pub fn with_capacity(entries: usize, bytes: usize) -> Self {
        Self {
            bytes: ListOfLists::with_capacities(entries, bytes),
            bytes_to_idx: HashTable::with_capacity(entries),
            hasher: DefaultHashBuilder::default(),
        }
    }

    pub fn get(&self, index: I) -> &[u8] {
        &self.bytes[index]
    }

    pub fn intern(&mut self, bytes: &[u8]) -> I {
        let entry = self.bytes_to_idx.entry(
            self.hasher.hash_one(bytes),
            |&i| &self.bytes[i] == bytes,
            |&i| self.hasher.hash_one(&self.bytes[i]),
        );
        match entry {
            Entry::Occupied(i) => *i.get(),
            Entry::Vacant(vacant) => {
                let new_index = self.bytes.push_copy_slice(bytes);
                vacant.insert(new_index);
                new_index
            }
        }
    }
}

impl<I: Idx> Default for BytesInterner<I> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct StringInterner<I: Idx>(BytesInterner<I>);

impl<I: Idx> Default for StringInterner<I> {
    fn default() -> Self {
        Self::new()
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::newtype_index;

    newtype_index! {
        struct TestIdx;
    }

    #[test]
    fn basic_interning_and_retrieval() {
        let mut interner = BytesInterner::<TestIdx>::new();

        let id1 = interner.intern(b"hello");
        let id2 = interner.intern(b"world");
        let id3 = interner.intern(b"");

        assert_eq!(interner.get(id1), b"hello");
        assert_eq!(interner.get(id2), b"world");
        assert_eq!(interner.get(id3), b"");
    }

    #[test]
    fn duplicate_contents_return_same_id() {
        let mut interner = BytesInterner::<TestIdx>::new();

        let id1 = interner.intern(b"duplicate");
        let id2 = interner.intern(b"other");
        let id3 = interner.intern(b"duplicate");

        assert_eq!(id1, id3);
        assert_ne!(id1, id2);
        assert_eq!(interner.get(id1), interner.get(id3));
    }
}
