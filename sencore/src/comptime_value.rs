use crate::ast;

type AllocationId = u32;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct StructType {
    pub def_uuid: ast::StructDefUniqueId,
    pub fields: Vec<(Box<str>, Type)>,
    pub capture: Value,
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

impl Type {
    pub const fn is_struct(&self) -> bool {
        matches!(self, Self::Struct(_))
    }
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
    pub is_comptime: bool,
    pub recursive_name: Option<Box<str>>,
    pub binds: Box<str>,
    pub body: ast::Expr,
    pub captures: ScopeId,
}

impl From<Closure> for Value {
    fn from(value: Closure) -> Self {
        Self::Closure(Box::new(value))
    }
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Builtin {
    GetStructField,
    GetTotalStructFields,
    IsStruct,
    Error,

    Add,
    Eq,

    Malloc,
    MemWrite,
    MemRead,

    InputSize,
    InputCopy,
    ReturnExit,
}

impl Builtin {
    pub fn comptime_only(&self) -> bool {
        matches!(
            self,
            Self::GetStructField | Self::GetTotalStructFields | Self::IsStruct | Self::Error
        )
    }

    pub fn runtime_only(&self) -> bool {
        matches!(self, Self::InputSize | Self::InputCopy | Self::ReturnExit)
    }

    pub const fn arg_count(&self) -> usize {
        match self {
            Self::GetStructField => 2,
            Self::GetTotalStructFields => 1,
            Self::IsStruct => 1,
            Self::Error => 1,

            Self::Add => 2,
            Self::Eq => 2,

            Self::Malloc => 1,
            Self::MemWrite => 2,
            Self::MemRead => 1,

            Self::InputSize => 1,
            Self::InputCopy => 3,
            Self::ReturnExit => 2,
        }
    }
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

impl Value {
    pub fn get_type(&self) -> Type {
        match self {
            Value::Void => Type::Void,
            Value::Num(_) => Type::Num,
            Value::Bool(_) => Type::Bool,
            Value::Struct(s) => s.r#type.clone(),
            Value::MemoryPointer(_) => Type::MemoryPointer,
            Value::Type(_) => Type::Type,
            Value::Closure(_) => Type::Function,
        }
    }
}
