use crate::{StrId, const_print::const_assert_eq, lexer::TokenIdx};
use sensei_core::{Idx, IndexVec, Span, newtype_index};

pub mod display;

newtype_index! {
    pub struct NodeIdx;
}

#[derive(Debug, Clone, Copy)]
pub struct Node {
    pub kind: NodeKind,
    pub tokens: Span<TokenIdx>,
    pub next_sibling: Option<NodeIdx>,
    pub first_child: Option<NodeIdx>,
}

const _ASSERT_NODE_SIZE: () = const_assert_eq(std::mem::size_of::<Node>(), 24);

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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NodeKind {
    File,

    // Declarations
    ConstDecl { typed: bool },
    ImportDecl { glob: bool },
    ImportAsDecl,
    InitBlock,
    RunBlock,

    // Statements
    ComptimeBlock,
    Block,
    LetStmt { mutable: bool, typed: bool },
    ReturnStmt,
    AssignStmt,
    WhileStmt,
    InlineWhileStmt,

    // Expressions
    BinaryExpr(BinaryOp),
    UnaryExpr(UnaryOp),
    ParenExpr,
    CallExpr,
    MemberExpr,
    StructDef,
    StructLit,

    // Conditional
    If,
    ElseIfBranchList,
    ElseIfBranch,

    // Atoms
    LiteralExpr,
    Identifier { ident: StrId },

    // Function Definition
    FnDef,
    ParamList,
    Parameter,
    ComptimeParameter,

    // Misc
    StatementsList,
    ImportPath,
    FieldDef,
    FieldAssign,

    // Errors
    Error,
}

impl std::fmt::Debug for NodeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::File => write!(f, "File"),
            Self::ConstDecl { typed } => f.debug_struct("ConstDecl").field("typed", typed).finish(),
            Self::ImportDecl { glob } => f.debug_struct("ImportDecl").field("glob", glob).finish(),
            Self::ImportAsDecl => write!(f, "ImportAsDecl"),
            Self::InitBlock => write!(f, "InitBlock"),
            Self::RunBlock => write!(f, "RunBlock"),
            Self::ComptimeBlock => write!(f, "ComptimeBlock"),
            Self::Block => write!(f, "Block"),
            Self::LetStmt { mutable, typed } => {
                f.debug_struct("LetStmt").field("mutable", mutable).field("typed", typed).finish()
            }
            Self::ReturnStmt => write!(f, "ReturnStmt"),
            Self::AssignStmt => write!(f, "AssignStmt"),
            Self::WhileStmt => write!(f, "WhileStmt"),
            Self::InlineWhileStmt => write!(f, "InlineWhileStmt"),
            Self::BinaryExpr(op) => write!(f, "BinaryExpr({op:?})"),
            Self::UnaryExpr(op) => write!(f, "UnaryExpr({op:?})"),
            Self::ParenExpr => write!(f, "ParenExpr"),
            Self::CallExpr => write!(f, "CallExpr"),
            Self::MemberExpr => write!(f, "MemberExpr"),
            Self::StructDef => write!(f, "StructDef"),
            Self::StructLit => write!(f, "StructLit"),
            Self::If => write!(f, "If"),
            Self::ElseIfBranchList => write!(f, "ElseIfBranchList"),
            Self::ElseIfBranch => write!(f, "ElseIfBranch"),
            Self::LiteralExpr => write!(f, "LiteralExpr"),
            Self::Identifier { .. } => write!(f, "Identifier"),
            Self::FnDef => write!(f, "FnDef"),
            Self::ParamList => write!(f, "ParamList"),
            Self::Parameter => write!(f, "Parameter"),
            Self::ComptimeParameter => write!(f, "ComptimeParameter"),
            Self::StatementsList => write!(f, "StatementsList"),
            Self::ImportPath => write!(f, "ImportPath"),
            Self::FieldDef => write!(f, "FieldDef"),
            Self::FieldAssign => write!(f, "FieldAssign"),
            Self::Error => write!(f, "Error"),
        }
    }
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
            | Self::Identifier { .. } => Some(true),
            _ => None,
        }
    }

    pub fn as_ident(&self) -> Option<StrId> {
        match self {
            Self::Identifier { ident } => Some(*ident),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ConcreteSyntaxTree {
    pub nodes: IndexVec<NodeIdx, Node>,
}

#[derive(Debug, Clone, Copy)]
pub struct NodeView<'cst> {
    cst: &'cst ConcreteSyntaxTree,
    idx: NodeIdx,
}

impl<'cst> NodeView<'cst> {
    pub fn new(cst: &'cst ConcreteSyntaxTree, idx: NodeIdx) -> Self {
        assert!(idx < cst.nodes.len_idx(), "idx out of bounds");
        Self { cst, idx }
    }

    fn node(self) -> &'cst Node {
        // Safety: Constructor validates `idx`
        unsafe { self.cst.nodes.get_unchecked(self.idx.idx()) }
    }

    pub fn kind(self) -> NodeKind {
        self.node().kind
    }

    pub fn span(self) -> Span<TokenIdx> {
        self.node().tokens
    }

    pub fn single_token(self) -> Option<TokenIdx> {
        let span = self.span();
        (span.end == span.start + 1).then_some(span.start)
    }

    pub fn idx(self) -> NodeIdx {
        self.idx
    }

    pub fn children(self) -> impl Iterator<Item = NodeView<'cst>> {
        self.cst.iter_children(self.idx).map(|idx| NodeView::new(self.cst, idx))
    }

    pub fn child(self, i: u32) -> Option<NodeView<'cst>> {
        self.children().skip(i as usize).next()
    }
}

impl ConcreteSyntaxTree {
    pub const FILE_IDX: NodeIdx = NodeIdx::ZERO;

    pub fn file_view(&self) -> NodeView<'_> {
        NodeView::new(self, Self::FILE_IDX)
    }

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
