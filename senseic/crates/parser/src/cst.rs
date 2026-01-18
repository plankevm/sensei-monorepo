use crate::const_print::const_assert_eq;
use allocator_api2::vec::Vec;
use bumpalo::Bump;
use neosen_data::{Span, X32};

pub struct TokenIndex;
pub type TokenIdx = X32<TokenIndex>;

pub struct NodeIndex;
pub type NodeIdx = X32<NodeIndex>;

#[derive(Debug, Clone)]
pub struct Node {
    pub kind: NodeKind,
    pub tokens: Span<TokenIdx>,
    pub next_sibling: Option<NodeIdx>,
    pub first_child: Option<NodeIdx>,
}

const _ASSERT_NODE_SIZE: () = const_assert_eq(std::mem::size_of::<Node>(), 20);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeKind {
    // Declarations
    ConstDecl,
    InitBlock,
    RunBlock,

    // Statements
    Block,
    LetStmt,
    ReturnStmt,
    AssignStmt,
    ExprStmt,
    WhileStmt,
    CondStmt,

    // Expressions
    CondExpr,
    ComptimeExpr,
    BinaryExpr,
    UnaryExpr,
    ParenExpr,
    CallExpr,
    MemberExpr,
    FnDef,
    StructDef,
    StructLit,

    // Atoms
    Literal,
    Ident,
    NamePath,

    // Misc
    ParamDef,
    FieldDef,
    ArgList,
    ParamList,
    FieldList,
    ElseBranch,

    // Errors
    Error,
}

#[derive(Debug, Clone)]
pub struct ConcreteSyntaxTree<'ast> {
    pub nodes: Vec<Node, &'ast Bump>,
}
