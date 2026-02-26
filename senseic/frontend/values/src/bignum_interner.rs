use alloy_primitives::U256;
use hashbrown::{DefaultHashBuilder, HashTable, hash_table::Entry};
use sensei_core::{IndexVec, newtype_index};
use std::hash::BuildHasher;

newtype_index! {
    /// Unique ID for numbers.
    pub struct BigNumId;
}

#[derive(Debug, Clone)]
pub struct BigNumInterner {
    values: IndexVec<BigNumId, U256>,
    dedup: HashTable<BigNumId>,
    hasher: DefaultHashBuilder,
}

impl Default for BigNumInterner {
    fn default() -> Self {
        Self::new()
    }
}

impl BigNumInterner {
    pub fn new() -> Self {
        Self {
            values: IndexVec::new(),
            dedup: HashTable::new(),
            hasher: DefaultHashBuilder::default(),
        }
    }

    pub fn intern(&mut self, value: U256) -> BigNumId {
        let hash = self.hasher.hash_one(value);
        let entry = self.dedup.entry(
            hash,
            |&id| self.values[id] == value,
            |&id| self.hasher.hash_one(self.values[id]),
        );
        match entry {
            Entry::Occupied(occupied) => *occupied.get(),
            Entry::Vacant(vacant) => {
                let id = self.values.push(value);
                vacant.insert(id);
                id
            }
        }
    }

    pub fn lookup(&self, id: BigNumId) -> U256 {
        self.values[id]
    }
}

impl std::ops::Index<BigNumId> for BigNumInterner {
    type Output = U256;

    fn index(&self, id: BigNumId) -> &U256 {
        &self.values[id]
    }
}
