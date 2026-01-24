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
pub enum BinaryOp {
    // Logical
    Or,
    And,
    // Comparison
    DoubleEquals,
    BangEquals,
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
pub enum UnaryOp {
    Minus,
    Bang,
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

    // Expressions
    BinaryExpr(BinaryOp),
    UnaryExpr(UnaryOp),
    ParenExpr,
    CallExpr,
    MemberExpr,
    FnDef,
    StructDef,
    StructLit,

    // Conditional
    If,
    ElseIfBranchList,
    ElseIfBranch,

    // Atoms
    LiteralExpr,
    Identifier,

    // Misc
    ParamDef,
    FieldDef,
    ArgList,
    ParamList,
    FieldList,
    StatementsList,

    // Errors
    Error,
}

impl NodeKind {
    pub fn expr_requires_semi_as_stmt(&self) -> Option<bool> {
        match self {
            Self::ComptimeBlock | Self::Block | Self::If | Self::Error => Some(false),
            Self::BinaryExpr(_)
            | Self::UnaryExpr(_)
            | Self::ParenExpr
            | Self::CallExpr
            | Self::MemberExpr
            | Self::FnDef
            | Self::StructDef
            | Self::StructLit
            | Self::LiteralExpr
            | Self::Identifier => Some(true),
            _ => None,
        }
    }
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

    pub fn assert_no_intersecting_token_spans_node(&self, parent: NodeIdx) {
        let parent_span = self.nodes[parent].tokens;
        let mut children = self.iter_children(parent).inspect(|&child| {
            self.assert_no_intersecting_token_spans_node(child);
        });
        if let Some(first_child) = children.next() {
            let first_child_span = self.nodes[first_child].tokens;
            let mut last = (first_child, first_child_span);
            assert!(
                parent_span.start <= last.1.start,
                "first child #{} span {} intersects parent #{} {}",
                first_child.get(),
                last.1,
                parent.get(),
                parent_span
            );

            for child in children {
                let (last_child, last_span) = last;
                let child_span = self.nodes[child].tokens;
                assert!(
                    last_span.end <= child_span.start,
                    "child #{} span {} intersects with previous sibling #{} {}",
                    child.get(),
                    child_span,
                    last_child.get(),
                    last_span
                );
                last = (child, child_span);
            }

            let (last_child, last_span) = last;

            assert!(
                last_span.end <= parent_span.end,
                "last child #{} span {} intersects with parent #{} span {}",
                last_child.get(),
                last_span,
                parent.get(),
                parent_span
            );
        }
    }

    pub fn assert_no_intersecting_token_spans(&self) {
        self.assert_no_intersecting_token_spans_node(Self::FILE_IDX);
    }
}
