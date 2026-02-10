use std::collections::HashMap;

use inturn::Interner;
use sensei_core::{IndexVec, Span, newtype_index};
use sensei_parser::cst;

// ---------------------------------------------------------------------------
// Index types
// ---------------------------------------------------------------------------

newtype_index! {
    pub struct NodeIdx;
    pub struct NodeRefIdx;
    pub struct FuncDefIdx;
    pub struct ParamIdx;
    pub struct StructDefIdx;
    pub struct FieldDefIdx;
    pub struct InitFieldIdx;
    pub struct LetIdx;
    pub struct ConstIdx;
    pub struct TypeIdx;
    pub struct LimbIdx;
    pub struct StrId;
}

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
    types: IndexVec<TypeIdx, Type>,
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
    pub node_kinds: IndexVec<NodeIdx, NodeKind>,
    pub node_sources: IndexVec<NodeIdx, cst::NodeIdx>,

    pub node_refs: IndexVec<NodeRefIdx, NodeIdx>,

    pub func_defs: IndexVec<FuncDefIdx, FuncDef>,
    pub params: IndexVec<ParamIdx, Param>,

    pub struct_defs: IndexVec<StructDefIdx, StructDef>,
    pub field_defs: IndexVec<FieldDefIdx, FieldDef>,

    pub init_fields: IndexVec<InitFieldIdx, InitField>,

    pub lets: IndexVec<LetIdx, LetBinding>,

    pub strings: Interner<StrId>,
    pub types: TypeInterner,
    pub limbs: IndexVec<LimbIdx, u32>,

    pub consts: IndexVec<ConstIdx, TopLevelConst>,

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
