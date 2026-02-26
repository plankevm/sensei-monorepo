use alloy_primitives::U256;
use hashbrown::{DefaultHashBuilder, HashTable};
use sensei_core::{IndexVec, list_of_lists::ListOfLists, newtype_index};
use sensei_hir::FnDefId;
use sensei_types::{TypeId, ValueId};
use std::hash::BuildHasher;

newtype_index! {
    struct CompoundIdx;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StoredValue {
    Void,
    Bool(bool),
    BigNum(U256),
    Type(TypeId),
    Closure { fn_def: FnDefId, children: CompoundIdx },
    StructVal { ty: TypeId, children: CompoundIdx },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Value<'a> {
    Void,
    Bool(bool),
    BigNum(U256),
    Type(TypeId),
    Closure { fn_def: FnDefId, captures: &'a [ValueId] },
    StructVal { ty: TypeId, fields: &'a [ValueId] },
}

pub(crate) struct ValueInterner {
    values: IndexVec<ValueId, StoredValue>,
    dedup: HashTable<ValueId>,
    hasher: DefaultHashBuilder,
    children: ListOfLists<CompoundIdx, ValueId>,
}

fn stored_to_value<'a>(
    stored: StoredValue,
    children: &'a ListOfLists<CompoundIdx, ValueId>,
) -> Value<'a> {
    match stored {
        StoredValue::Void => Value::Void,
        StoredValue::Bool(b) => Value::Bool(b),
        StoredValue::BigNum(n) => Value::BigNum(n),
        StoredValue::Type(t) => Value::Type(t),
        StoredValue::Closure { fn_def, children: idx } => {
            Value::Closure { fn_def, captures: &children[idx] }
        }
        StoredValue::StructVal { ty, children: idx } => {
            Value::StructVal { ty, fields: &children[idx] }
        }
    }
}

impl ValueInterner {
    pub fn new() -> Self {
        Self {
            values: IndexVec::new(),
            dedup: HashTable::new(),
            hasher: DefaultHashBuilder::default(),
            children: ListOfLists::new(),
        }
    }

    fn hash_value(&self, value: Value<'_>) -> u64 {
        self.hasher.hash_one(value)
    }

    pub fn intern(&mut self, value: Value<'_>) -> ValueId {
        let hash = self.hash_value(value);
        if let Some(&existing) =
            self.dedup.find(hash, |&id| stored_to_value(self.values[id], &self.children) == value)
        {
            return existing;
        }
        let stored = match value {
            Value::Void => StoredValue::Void,
            Value::Bool(b) => StoredValue::Bool(b),
            Value::BigNum(n) => StoredValue::BigNum(n),
            Value::Type(t) => StoredValue::Type(t),
            Value::Closure { fn_def, captures } => {
                StoredValue::Closure { fn_def, children: self.children.push_copy_slice(captures) }
            }
            Value::StructVal { ty, fields } => {
                StoredValue::StructVal { ty, children: self.children.push_copy_slice(fields) }
            }
        };
        let id = self.values.push(stored);
        self.dedup.insert_unique(hash, id, |&id| {
            self.hasher.hash_one(stored_to_value(self.values[id], &self.children))
        });
        id
    }

    pub fn lookup(&self, id: ValueId) -> Value<'_> {
        stored_to_value(self.values[id], &self.children)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_primitives_dedup() {
        let mut interner = ValueInterner::new();
        let v1 = interner.intern(Value::Void);
        let v2 = interner.intern(Value::Void);
        assert_eq!(v1, v2);

        let b1 = interner.intern(Value::Bool(true));
        let b2 = interner.intern(Value::Bool(true));
        let b3 = interner.intern(Value::Bool(false));
        assert_eq!(b1, b2);
        assert_ne!(b1, b3);
    }

    #[test]
    fn intern_compound_dedup() {
        let mut interner = ValueInterner::new();
        let v1 = interner.intern(Value::Void);
        let ty = interner.intern(Value::Type(TypeId::new(1)));

        let s1 = interner.intern(Value::StructVal { ty: TypeId::new(1), fields: &[v1, ty] });
        let s2 = interner.intern(Value::StructVal { ty: TypeId::new(1), fields: &[v1, ty] });
        assert_eq!(s1, s2);

        let s3 = interner.intern(Value::StructVal { ty: TypeId::new(2), fields: &[v1, ty] });
        assert_ne!(s1, s3);
    }

    #[test]
    fn lookup_roundtrip() {
        let mut interner = ValueInterner::new();
        let v = interner.intern(Value::BigNum(U256::from(42)));
        assert_eq!(interner.lookup(v), Value::BigNum(U256::from(42)));
    }
}
