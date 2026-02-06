use std::collections::HashMap;

use inturn::Interner;
use sensei_core::{IndexVec, Span, X32};
use sensei_parser::cst;

// ---------------------------------------------------------------------------
// Index marker types (empty enums, matching SIR pattern)
// ---------------------------------------------------------------------------

pub struct NodeIndex;
pub type NodeIdx = X32<NodeIndex>;

pub struct NodeRefIndex;
pub type NodeRefIdx = X32<NodeRefIndex>;

pub struct FuncDefIndex;
pub type FuncDefIdx = X32<FuncDefIndex>;

pub struct ParamIndex;
pub type ParamIdx = X32<ParamIndex>;

pub struct StructDefIndex;
pub type StructDefIdx = X32<StructDefIndex>;

pub struct FieldDefIndex;
pub type FieldDefIdx = X32<FieldDefIndex>;

pub struct InitFieldIndex;
pub type InitFieldIdx = X32<InitFieldIndex>;

pub struct LetIndex;
pub type LetIdx = X32<LetIndex>;

pub struct ConstIndex;
pub type ConstIdx = X32<ConstIndex>;

pub struct TypeIndex;
pub type TypeIdx = X32<TypeIndex>;

pub struct LimbIndex;
pub type LimbIdx = X32<LimbIndex>;

pub struct StringId;
pub type StrId = X32<StringId>;

// ---------------------------------------------------------------------------
// Builtin
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Builtin {
    // Struct reflection (comptime)
    GetStructField,
    GetTotalStructFields,
    IsStruct,
    Error,

    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    // Wrapping arithmetic
    AddWrap,
    SubWrap,
    MulWrap,
    // Rounding division
    DivCeil,
    DivFloor,
    DivTrunc,
    DivRound,

    // Comparison
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,

    // Bitwise
    BitOr,
    BitXor,
    BitAnd,
    Shl,
    Shr,

    // Logical
    Or,
    And,

    // Unary
    Neg,
    Not,
    BitNot,

    // Memory
    Malloc,
    MemWrite,
    MemRead,

    // I/O (runtime)
    InputSize,
    InputCopy,
    ReturnExit,
}

#[derive(Debug, Clone, Copy)]
pub struct BigInt {
    pub is_positive: bool,
    pub limbs: Span<LimbIdx>,
}

// ---------------------------------------------------------------------------
// NodeKind (target: 16 bytes, align 4)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
pub enum NodeKind {
    Var(StrId),
    LitVoid,
    LitInt(BigInt),
    LitBool(bool),
    LitType(TypeIdx),
    LitBuiltin(Builtin),

    Call { func: NodeIdx, args: Span<NodeRefIdx> },

    FuncDef(FuncDefIdx),

    IfThenElse { cond: NodeIdx, then_body: NodeIdx, else_body: NodeIdx },

    StructDef(StructDefIdx),
    StructInit { type_expr: NodeIdx, fields: Span<InitFieldIdx> },
    MemberAccess { object: NodeIdx, member: StrId },

    Block { lets: Span<LetIdx>, tail: NodeIdx },
}

// ---------------------------------------------------------------------------
// Type interning
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Void,
    Num,
    Bool,
    MemoryPointer,
    Type,
    Function,
    Struct(StructDefIdx),
}

#[derive(Debug)]
pub struct TypeInterner {
    types: IndexVec<TypeIndex, Type>,
    map: HashMap<Type, TypeIdx>,
}

impl TypeInterner {
    pub fn new() -> Self {
        Self { types: IndexVec::new(), map: HashMap::new() }
    }

    pub fn intern(&mut self, ty: Type) -> TypeIdx {
        if let Some(&idx) = self.map.get(&ty) {
            return idx;
        }
        let idx = self.types.push(ty.clone());
        self.map.insert(ty, idx);
        idx
    }

    pub fn resolve(&self, idx: TypeIdx) -> &Type {
        &self.types[idx]
    }
}

impl Default for TypeInterner {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Auxiliary structures
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
pub struct FuncDef {
    pub name: Option<StrId>,
    pub params: Span<ParamIdx>,
    pub body: NodeIdx,
}

#[derive(Debug, Clone, Copy)]
pub struct Param {
    pub source: cst::NodeIdx,
    pub name: StrId,
    pub is_comptime: bool,
    pub type_expr: NodeIdx,
}

#[derive(Debug, Clone, Copy)]
pub struct StructDef {
    pub fields: Span<FieldDefIdx>,
}

#[derive(Debug, Clone, Copy)]
pub struct FieldDef {
    pub source: cst::NodeIdx,
    pub name: StrId,
    pub type_expr: NodeIdx,
}

#[derive(Debug, Clone, Copy)]
pub struct InitField {
    pub source: cst::NodeIdx,
    pub name: StrId,
    pub value: NodeIdx,
}

#[derive(Debug, Clone, Copy)]
pub struct LetBinding {
    pub source: cst::NodeIdx,
    pub name: StrId,
    pub type_expr: Option<NodeIdx>,
    pub value: NodeIdx,
}

#[derive(Debug, Clone, Copy)]
pub struct TopLevelConst {
    pub source: cst::NodeIdx,
    pub name: StrId,
    pub type_expr: Option<NodeIdx>,
    pub value: NodeIdx,
}

// ---------------------------------------------------------------------------
// Top-level HIR
// ---------------------------------------------------------------------------

pub struct Hir {
    pub node_kinds: IndexVec<NodeIndex, NodeKind>,
    pub node_sources: IndexVec<NodeIndex, cst::NodeIdx>,

    pub node_refs: IndexVec<NodeRefIndex, NodeIdx>,

    pub func_defs: IndexVec<FuncDefIndex, FuncDef>,
    pub params: IndexVec<ParamIndex, Param>,

    pub struct_defs: IndexVec<StructDefIndex, StructDef>,
    pub field_defs: IndexVec<FieldDefIndex, FieldDef>,

    pub init_fields: IndexVec<InitFieldIndex, InitField>,

    pub lets: IndexVec<LetIndex, LetBinding>,

    pub strings: Interner<StrId>,
    pub types: TypeInterner,
    pub limbs: IndexVec<LimbIndex, u32>,

    pub consts: IndexVec<ConstIndex, TopLevelConst>,

    pub root: NodeIdx,
}

impl std::fmt::Debug for Hir {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Hir")
            .field("node_kinds", &self.node_kinds)
            .field("node_sources", &self.node_sources)
            .field("node_refs", &self.node_refs)
            .field("func_defs", &self.func_defs)
            .field("params", &self.params)
            .field("struct_defs", &self.struct_defs)
            .field("field_defs", &self.field_defs)
            .field("init_fields", &self.init_fields)
            .field("lets", &self.lets)
            .field("strings", &"<Interner>")
            .field("types", &self.types)
            .field("limbs", &self.limbs)
            .field("consts", &self.consts)
            .field("root", &self.root)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Layout assertions
// ---------------------------------------------------------------------------

const _NODE_KIND_LAYOUT: () = const {
    assert!(std::mem::size_of::<NodeKind>() == 16);
    assert!(std::mem::align_of::<NodeKind>() == 4);
};
const _FUNC_DEF_SIZE: () = const { assert!(std::mem::size_of::<FuncDef>() == 16) };
const _PARAM_SIZE: () = const { assert!(std::mem::size_of::<Param>() == 16) };
const _STRUCT_DEF_SIZE: () = const { assert!(std::mem::size_of::<StructDef>() == 8) };
const _FIELD_DEF_SIZE: () = const { assert!(std::mem::size_of::<FieldDef>() == 12) };
const _INIT_FIELD_SIZE: () = const { assert!(std::mem::size_of::<InitField>() == 12) };
const _LET_BINDING_SIZE: () = const { assert!(std::mem::size_of::<LetBinding>() == 16) };
const _TOP_LEVEL_CONST_SIZE: () = const { assert!(std::mem::size_of::<TopLevelConst>() == 16) };
