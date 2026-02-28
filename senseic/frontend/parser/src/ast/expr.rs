use crate::{
    StrId,
    cst::{BinaryOp, NodeKind, NodeView, NumLitId, UnaryOp},
};

#[derive(Debug, Clone, Copy)]
pub enum Expr<'cst> {
    Binary(BinaryExpr<'cst>),
    Unary(UnaryExpr<'cst>),
    Call(CallExpr<'cst>),
    Member(MemberExpr<'cst>),
    StructDef(StructDef<'cst>),
    StructLit(StructLit<'cst>),
    If(IfExpr<'cst>),
    FnDef(FnDef<'cst>),
    Block(BlockExpr<'cst>),
    ComptimeBlock(BlockExpr<'cst>),
    BoolLiteral(bool),
    NumLiteral { negative: bool, id: NumLitId },
    Ident(StrId),
}

impl<'cst> Expr<'cst> {
    pub fn new_unwrap(view: NodeView<'cst>) -> Self {
        Expr::new(view).expect("expected expression node")
    }

    /// Creates an Expr from a NodeView. Returns `None` for non-expression nodes.
    ///
    /// ParenExpr nodes are transparently peeled — the resulting Expr
    /// points to the innermost non-paren expression.
    pub fn new(mut view: NodeView<'cst>) -> Option<Self> {
        const MAX_PAREN_UNWRAPS: usize = 16_000;
        for _ in 0..MAX_PAREN_UNWRAPS {
            let expr = match view.kind() {
                NodeKind::ParenExpr => {
                    view = view.child(0)?;
                    continue;
                }
                NodeKind::BinaryExpr(op) => Expr::Binary(BinaryExpr { op, view }),
                NodeKind::UnaryExpr(op) => Expr::Unary(UnaryExpr { op, view }),
                NodeKind::CallExpr => Expr::Call(CallExpr { view }),
                NodeKind::MemberExpr => Expr::Member(MemberExpr::new(view).unwrap()),
                NodeKind::StructDef => Expr::StructDef(StructDef { view }),
                NodeKind::StructLit => Expr::StructLit(StructLit { view }),
                NodeKind::If => Expr::If(IfExpr { view }),
                NodeKind::FnDef => Expr::FnDef(FnDef { view }),
                NodeKind::Block => Expr::Block(BlockExpr { view }),
                NodeKind::ComptimeBlock => Expr::ComptimeBlock(BlockExpr { view }),
                NodeKind::BoolLiteral(value) => Expr::BoolLiteral(value),
                NodeKind::NumLiteral { negative, id } => Expr::NumLiteral { negative, id },
                NodeKind::Identifier { ident } => Expr::Ident(ident),
                _ => return None,
            };
            return Some(expr);
        }

        unreachable!("Nested paren over {MAX_PAREN_UNWRAPS} deep");
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BinaryExpr<'cst> {
    pub op: BinaryOp,
    view: NodeView<'cst>,
}

impl<'cst> BinaryExpr<'cst> {
    pub fn lhs(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("BinaryExpr must have lhs child");
        Expr::new_unwrap(child)
    }

    pub fn rhs(&self) -> Expr<'cst> {
        let child = self.view.child(1).expect("BinaryExpr must have rhs child");
        Expr::new_unwrap(child)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Unary expression: `op operand`
#[derive(Debug, Clone, Copy)]
pub struct UnaryExpr<'cst> {
    pub op: UnaryOp,
    view: NodeView<'cst>,
}

impl<'cst> UnaryExpr<'cst> {
    pub fn operand(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("UnaryExpr must have operand child");
        Expr::new_unwrap(child)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Call expression: `callee(arg1, arg2, ...)`
#[derive(Debug, Clone, Copy)]
pub struct CallExpr<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> CallExpr<'cst> {
    pub fn callee(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("CallExpr must have callee child");
        Expr::new_unwrap(child)
    }

    pub fn args(&self) -> impl Iterator<Item = Expr<'cst>> {
        self.view.children().skip(1).map(Expr::new_unwrap)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Member access expression: `object.member`
#[derive(Debug, Clone, Copy)]
pub struct MemberExpr<'cst> {
    pub member: StrId,
    view: NodeView<'cst>,
}

impl<'cst> MemberExpr<'cst> {
    pub fn new(view: NodeView<'cst>) -> Option<Self> {
        if view.kind() != NodeKind::MemberExpr {
            return None;
        }
        let member = view.child(1).and_then(NodeView::ident).expect("TODO: Malformed member expr");
        Some(Self { member, view })
    }

    pub fn object(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("MemberExpr must have object child");
        Expr::new_unwrap(child)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Struct definition: `struct { field1: Type1, ... }` or
/// `struct TypeIndex { field1: Type1, ... }`
#[derive(Debug, Clone, Copy)]
pub struct StructDef<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> StructDef<'cst> {
    pub fn index_expr(&self) -> Option<Expr<'cst>> {
        self.view.children().next().and_then(|child| match child.kind() {
            NodeKind::FieldDef => None,
            _ => Expr::new(child),
        })
    }

    pub fn fields(&self) -> impl Iterator<Item = FieldDef<'cst>> {
        self.view.children().filter_map(FieldDef::new)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Field definition within a struct: `name: Type`
#[derive(Debug, Clone, Copy)]
pub struct FieldDef<'cst> {
    pub name: StrId,
    view: NodeView<'cst>,
}

impl<'cst> FieldDef<'cst> {
    fn new(view: NodeView<'cst>) -> Option<Self> {
        match view.kind() {
            NodeKind::FieldDef => {
                let name = view
                    .child(0)
                    .and_then(|v| v.kind().as_ident())
                    .expect("TODO: handle malformed FieldDef");
                Some(Self { name, view })
            }
            _ => None,
        }
    }

    pub fn type_expr(&self) -> Expr<'cst> {
        let child = self.view.child(1).expect("FieldDef must have type_expr child");
        Expr::new_unwrap(child)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Struct literal: `Type { field1: value1, ... }`
#[derive(Debug, Clone, Copy)]
pub struct StructLit<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> StructLit<'cst> {
    pub fn type_expr(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("StructLit must have type_expr child");
        Expr::new_unwrap(child)
    }

    pub fn fields(&self) -> impl Iterator<Item = FieldAssign<'cst>> {
        self.view.children().skip(1).filter_map(FieldAssign::new)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Field assignment within a struct literal: `name: value`
#[derive(Debug, Clone, Copy)]
pub struct FieldAssign<'cst> {
    pub name: StrId,
    view: NodeView<'cst>,
}

impl<'cst> FieldAssign<'cst> {
    fn new(view: NodeView<'cst>) -> Option<Self> {
        match view.kind() {
            NodeKind::FieldAssign => {
                let name = view
                    .child(0)
                    .and_then(|v| v.kind().as_ident())
                    .expect("TODO: handle malformed FieldAssign");
                Some(Self { name, view })
            }
            _ => None,
        }
    }

    pub fn value(&self) -> Expr<'cst> {
        let child = self.view.child(1).expect("FieldAssign must have value child");
        Expr::new_unwrap(child)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// If expression: `if condition { body } else if ... else { ... }`
#[derive(Debug, Clone, Copy)]
pub struct IfExpr<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> IfExpr<'cst> {
    pub fn condition(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("If must have condition child");
        Expr::new_unwrap(child)
    }

    pub fn body(&self) -> BlockExpr<'cst> {
        let child = self.view.child(1).expect("If must have body child");
        BlockExpr::new(child)
    }

    /// Returns an iterator over the else-if branches.
    pub fn else_if_branches(&self) -> impl Iterator<Item = ElseIfBranch<'cst>> {
        let else_if_list = self.view.child(2);
        else_if_list.into_iter().flat_map(|list| list.children()).filter_map(ElseIfBranch::new)
    }

    /// Returns the else body if present.
    pub fn else_body(&self) -> Option<BlockExpr<'cst>> {
        self.view.child(3).map(BlockExpr::new)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// An else-if branch: `else if condition { body }`
#[derive(Debug, Clone, Copy)]
pub struct ElseIfBranch<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> ElseIfBranch<'cst> {
    fn new(view: NodeView<'cst>) -> Option<Self> {
        match view.kind() {
            NodeKind::ElseIfBranch => Some(Self { view }),
            _ => None,
        }
    }

    pub fn condition(&self) -> Expr<'cst> {
        let node = self.view.child(0).expect("ElseIfBranch must have condition child");
        Expr::new_unwrap(node)
    }

    pub fn body(&self) -> BlockExpr<'cst> {
        let node = self.view.child(1).expect("ElseIfBranch must have body child");
        BlockExpr::new(node)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Function definition: `fn(params) return_type { body }`
#[derive(Debug, Clone, Copy)]
pub struct FnDef<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> FnDef<'cst> {
    pub fn params(&self) -> impl Iterator<Item = Param<'cst>> {
        let param_list = self.view.child(0);
        param_list.into_iter().flat_map(|list| list.children()).filter_map(Param::new)
    }

    pub fn return_type(&self) -> Expr<'cst> {
        let node = self.view.child(1).expect("FnDef must have return_type child");
        Expr::new_unwrap(node)
    }

    pub fn body(&self) -> Expr<'cst> {
        let node = self.view.child(2).expect("FnDef must have body child");
        Expr::new_unwrap(node)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Function parameter: `name: Type` or `comptime name: Type`
#[derive(Debug, Clone, Copy)]
pub struct Param<'cst> {
    pub name: StrId,
    pub comptime: bool,
    view: NodeView<'cst>,
}

impl<'cst> Param<'cst> {
    fn new(view: NodeView<'cst>) -> Option<Self> {
        let comptime = match view.kind() {
            NodeKind::Parameter => false,
            NodeKind::ComptimeParameter => true,
            _ => return None,
        };
        let name = view
            .child(0)
            .and_then(|v| v.kind().as_ident())
            .expect("TODO: handle malformed Parameter");
        Some(Self { name, comptime, view })
    }

    pub fn type_expr(&self) -> Expr<'cst> {
        let node = self.view.child(1).expect("Parameter must have type_expr child");
        Expr::new_unwrap(node)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BlockExpr<'cst> {
    view: NodeView<'cst>,
}

#[derive(Debug, Clone, Copy)]
pub struct LetStmt<'cst> {
    pub name: StrId,
    pub mutable: bool,
    type_view: Option<NodeView<'cst>>,
    value_view: NodeView<'cst>,
}

impl<'cst> LetStmt<'cst> {
    pub fn new(view: NodeView<'cst>) -> Option<Self> {
        let NodeKind::LetStmt { mutable, typed } = view.kind() else {
            return None;
        };
        let mut children = view.children();
        let name = children.next().and_then(NodeView::ident).expect("TODO: malformed");
        let type_view = typed.then(|| children.next().expect("TODO: malformed"));
        let value_view = children.next().expect("TODO: malformed");
        Some(Self { name, mutable, type_view, value_view })
    }

    pub fn type_expr(&self) -> Option<Expr<'cst>> {
        self.type_view.map(Expr::new_unwrap)
    }

    pub fn value(&self) -> Expr<'cst> {
        Expr::new_unwrap(self.value_view)
    }
}

/// Return statement: `return expr;`
#[derive(Debug, Clone, Copy)]
pub struct ReturnStmt<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> ReturnStmt<'cst> {
    fn new(view: NodeView<'cst>) -> Option<Self> {
        match view.kind() {
            NodeKind::ReturnStmt => Some(Self { view }),
            _ => None,
        }
    }

    pub fn value(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("ReturnStmt must have value child");
        Expr::new_unwrap(child)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// Assignment statement: `target = value;`
#[derive(Debug, Clone, Copy)]
pub struct AssignStmt<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> AssignStmt<'cst> {
    fn new(view: NodeView<'cst>) -> Option<Self> {
        match view.kind() {
            NodeKind::AssignStmt => Some(Self { view }),
            _ => None,
        }
    }

    pub fn target(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("AssignStmt must have target child");
        Expr::new_unwrap(child)
    }

    pub fn value(&self) -> Expr<'cst> {
        let child = self.view.child(1).expect("AssignStmt must have value child");
        Expr::new_unwrap(child)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

/// While statement: `while condition { body }` or `inline while condition { body }`
#[derive(Debug, Clone, Copy)]
pub struct WhileStmt<'cst> {
    pub inline: bool,
    view: NodeView<'cst>,
}

impl<'cst> WhileStmt<'cst> {
    fn new(view: NodeView<'cst>) -> Option<Self> {
        let inline = match view.kind() {
            NodeKind::WhileStmt => false,
            NodeKind::InlineWhileStmt => true,
            _ => return None,
        };
        Some(Self { inline, view })
    }

    pub fn condition(&self) -> Expr<'cst> {
        let child = self.view.child(0).expect("WhileStmt must have condition child");
        Expr::new_unwrap(child)
    }

    pub fn body(&self) -> BlockExpr<'cst> {
        let child = self.view.child(1).expect("WhileStmt must have body child");
        BlockExpr::new(child)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Statement<'cst> {
    Let(LetStmt<'cst>),
    Return(ReturnStmt<'cst>),
    Assign(AssignStmt<'cst>),
    While(WhileStmt<'cst>),
    Expr(Expr<'cst>),
}

impl<'cst> Statement<'cst> {
    pub fn new(view: NodeView<'cst>) -> Option<Self> {
        if let Some(let_stmt) = LetStmt::new(view) {
            return Some(Statement::Let(let_stmt));
        }
        if let Some(return_stmt) = ReturnStmt::new(view) {
            return Some(Statement::Return(return_stmt));
        }
        if let Some(assign_stmt) = AssignStmt::new(view) {
            return Some(Statement::Assign(assign_stmt));
        }
        if let Some(while_stmt) = WhileStmt::new(view) {
            return Some(Statement::While(while_stmt));
        }
        if let Some(expr) = Expr::new(view) {
            return Some(Statement::Expr(expr));
        }
        None
    }
}

impl<'cst> BlockExpr<'cst> {
    pub(super) fn from_view(view: NodeView<'cst>) -> Self {
        assert!(
            matches!(
                view.kind(),
                NodeKind::Block
                    | NodeKind::ComptimeBlock
                    | NodeKind::InitBlock
                    | NodeKind::RunBlock
            ),
            "BlockExpr::from_view called with non-block node: {:?}",
            view.kind()
        );
        Self { view }
    }

    fn new(view: NodeView<'cst>) -> Self {
        assert!(
            matches!(view.kind(), NodeKind::Block | NodeKind::ComptimeBlock),
            "BlockExpr::new called with non-block node: {:?}",
            view.kind()
        );
        Self { view }
    }

    /// Returns an iterator over the statements in this block.
    pub fn statements(&self) -> impl Iterator<Item = Statement<'cst>> {
        let list = self.view.child(0).expect("todo: malformed block missing stmt list child");
        list.children()
            .map(|view| Statement::new(view).expect("todo: non-statement child of stmt list"))
    }

    /// Returns the trailing/end expression if present.
    pub fn end_expr(&self) -> Option<Expr<'cst>> {
        self.view.child(1).map(Expr::new_unwrap)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}
