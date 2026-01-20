use crate::const_print::const_assert_eq;
use bumpalo::Bump;
use neosen_data::{IndexVec, Span, X32};

pub mod display;

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
pub enum BinaryKind {
    // Logical
    Or,
    And,
    // Comparison
    DoubleEquals,
    NotEquals,
    LessThan,
    GreaterThan,
    LessEquals,
    GreaterEquals,
    // Bitwise
    Pipe,
    Caret,
    Ampersand,
    ShiftLeft,
    ShiftRight,
    // Arithmetic (additive)
    Plus,
    Minus,
    PlusPercent,
    MinusPercent,
    // Arithmetic (multiplicative)
    Star,
    Slash,
    Percent,
    StarPercent,
    SlashPlus,
    SlashNeg,
    SlashLess,
    SlashGreater,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryKind {
    Minus,
    Not,
    Tilde,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeKind {
    File,

    // Declarations
    ConstDecl,
    TypedConstDecl,
    InitBlock,
    RunBlock,

    // Statements
    ComptimeBlock,
    Block,
    LetStmt,
    ReturnStmt,
    AssignStmt,
    ExprStmt,
    WhileStmt,
    CondStmt,

    // Expressions
    CondExpr,
    BinaryExpr(BinaryKind),
    UnaryExpr(UnaryKind),
    ParenExpr,
    CallExpr,
    MemberExpr,
    FnDef,
    StructDef,
    StructLit,

    // Atoms
    Operator,
    LiteralExpr,
    Identifier,

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
    pub nodes: IndexVec<NodeIndex, Node, &'ast Bump>,
}

impl<'ast> ConcreteSyntaxTree<'ast> {
    pub const FILE_IDX: NodeIdx = NodeIdx::ZERO;

    pub fn iter_children(&self, node: NodeIdx) -> impl Iterator<Item = NodeIdx> {
        let mut next_child = self.nodes[node].first_child;
        std::iter::from_fn(move || {
            let child = next_child?;
            next_child = self.nodes[child].next_sibling;
            Some(child)
        })
    }
}
