use crate::values::ValueIdx;
use hashbrown::{DefaultHashBuilder, HashTable, hash_table::Entry};
use sensei_core::{Idx, IndexVec, list_of_lists::ListOfLists, newtype_index};
use sensei_parser::cst;
use std::{hash::BuildHasher, num::NonZero};

newtype_index! {
    pub struct TypeId;
    struct StructIdx;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructExtraInfo {
    pub source: cst::NodeIdx,
    pub type_index: ValueIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructInfo<'fields> {
    pub source: cst::NodeIdx,
    pub type_index: ValueIdx,
    pub fields: &'fields [TypeId],
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type<'fields> {
    Void,
    Int,
    Bool,
    MemoryPointer,
    Type,
    Function,
    Struct(StructInfo<'fields>),
}

#[derive(Debug)]
pub struct TypeInterner {
    info_to_struct: HashTable<StructIdx>,
    /// Separate struct that holds struct lookup information for ownership reason.
    storage: StructStorage,
}

#[derive(Debug)]
struct StructStorage {
    struct_fields: ListOfLists<StructIdx, TypeId>,
    index_to_struct: IndexVec<StructIdx, StructExtraInfo>,
    hasher: DefaultHashBuilder,
}

impl TypeId {
    const VOID: TypeId = TypeId::new(0);
    const INT: TypeId = TypeId::new(1);
    const BOOL: TypeId = TypeId::new(2);
    const MEMORY_POINTER: TypeId = TypeId::new(3);
    const TYPE: TypeId = TypeId::new(4);
    const FUNCTION: TypeId = TypeId::new(5);

    const LAST_FIXED_ID: TypeId = Self::FUNCTION;
    const STRUCT_IDS_OFFSET: u32 = Self::LAST_FIXED_ID.const_get() + 1;

    fn get_primitive_id(ty: Type<'_>) -> Result<TypeId, StructInfo<'_>> {
        match ty {
            Type::Void => Ok(Self::VOID),
            Type::Int => Ok(Self::INT),
            Type::Bool => Ok(Self::BOOL),
            Type::MemoryPointer => Ok(Self::MEMORY_POINTER),
            Type::Type => Ok(Self::TYPE),
            Type::Function => Ok(Self::FUNCTION),
            Type::Struct(r#struct) => Err(r#struct),
        }
    }

    const fn as_type(self) -> Result<Type<'static>, StructIdx> {
        match self {
            Self::VOID => Ok(Type::Void),
            Self::INT => Ok(Type::Int),
            Self::BOOL => Ok(Type::Bool),
            Self::MEMORY_POINTER => Ok(Type::MemoryPointer),
            Self::TYPE => Ok(Type::Type),
            Self::FUNCTION => Ok(Type::Function),
            _ => Err(StructIdx::new(self.const_get() - Self::STRUCT_IDS_OFFSET)),
        }
    }

    pub fn is_struct(self) -> bool {
        self.0.get() > Self::LAST_FIXED_ID.0.get()
    }
}

impl From<StructIdx> for TypeId {
    fn from(value: StructIdx) -> Self {
        Self(
            NonZero::new(value.get().wrapping_add(Self::STRUCT_IDS_OFFSET))
                .expect("32-bit overflow"),
        )
    }
}

impl Default for TypeInterner {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeInterner {
    pub fn new() -> Self {
        Self {
            storage: StructStorage {
                struct_fields: Default::default(),
                index_to_struct: Default::default(),
                hasher: Default::default(),
            },
            info_to_struct: Default::default(),
        }
    }

    pub fn with_capacity(structs: usize, fields: usize) -> Self {
        Self {
            storage: StructStorage {
                struct_fields: ListOfLists::with_capacities(structs, fields),
                index_to_struct: IndexVec::with_capacity(structs),
                hasher: Default::default(),
            },
            info_to_struct: HashTable::with_capacity(structs),
        }
    }

    pub fn intern(&mut self, ty: Type<'_>) -> TypeId {
        let r#struct = match TypeId::get_primitive_id(ty) {
            Ok(ty) => return ty,
            Err(type_info) => type_info,
        };
        let entry = self.info_to_struct.entry(
            self.storage.hash_struct_info(r#struct),
            |&idx| self.storage.get_info(idx) == r#struct,
            |&idx| self.storage.hash_struct_id(idx),
        );
        match entry {
            Entry::Occupied(occupied) => (*occupied.get()).into(),
            Entry::Vacant(vacant) => {
                let field_struct_idx = self.storage.struct_fields.push_copy_slice(r#struct.fields);
                let new_struct_idx = self.storage.index_to_struct.push(StructExtraInfo {
                    source: r#struct.source,
                    type_index: r#struct.type_index,
                });
                debug_assert_eq!(new_struct_idx, field_struct_idx);
                vacant.insert(new_struct_idx);
                new_struct_idx.into()
            }
        }
    }

    pub fn lookup(&self, type_id: TypeId) -> Type<'_> {
        let struct_idx = match type_id.as_type() {
            Ok(ty) => return ty,
            Err(struct_idx) => struct_idx,
        };
        let stored = &self.storage.index_to_struct[struct_idx];
        Type::Struct(StructInfo {
            source: stored.source,
            type_index: stored.type_index,
            fields: &self.storage.struct_fields[struct_idx],
        })
    }
}

impl StructStorage {
    fn get_info(&self, idx: StructIdx) -> StructInfo<'_> {
        let source = self.index_to_struct[idx].source;
        let type_index = self.index_to_struct[idx].type_index;
        let fields = &self.struct_fields[idx];
        StructInfo { source, type_index, fields }
    }

    fn hash_struct_id(&self, idx: StructIdx) -> u64 {
        self.hash_struct_info(self.get_info(idx))
    }

    fn hash_struct_info(&self, r#struct: StructInfo) -> u64 {
        self.hasher.hash_one(r#struct)
    }
}
