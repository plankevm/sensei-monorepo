use crate::ast;

type AllocationId = u32;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct StructType {
    pub def_uuid: ast::StructDefUniqueId,
    pub fields: Vec<(Box<str>, Type)>,
    pub defs: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Void,
    Num,
    Bool,
    MemoryPointer,
    Type,
    Function,
    Struct(StructType),
}

impl From<Type> for Value {
    fn from(value: Type) -> Self {
        Self::Type(Box::new(value))
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct ScopeId(pub usize);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Closure {
    pub r#type: Type,
    pub binds: Box<str>,
    pub body: ast::Expr,
    pub captures: ScopeId,
}

pub enum PartialExpr {
    Value(Value),
    Var(Box<str>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct StructValue {
    pub r#type: Type,
    pub field_values: Vec<Value>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct VirtualMemoryPointer {
    pub allocation: AllocationId,
    pub offset: i32,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Value {
    Void,
    Num(i32),
    Bool(bool),
    Struct(Box<StructValue>),
    MemoryPointer(VirtualMemoryPointer),
    Type(Box<Type>),
    Closure(Box<Closure>),
}
