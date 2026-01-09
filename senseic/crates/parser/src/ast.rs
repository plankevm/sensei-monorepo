use crate::{const_print::const_assert_eq, lexer::SourceSpan};
use allocator_api2::vec::Vec;
use bumpalo::Bump;
use inturn::Interner;
use neosen_data::{X32, bigint::FrozenBigUint};
use std::convert::Infallible;

pub struct InternedString;
pub type IStr = X32<InternedString>;
pub type StringInterner = Interner<IStr>;
pub type AstBox<'ast, T> = &'ast mut T;

#[derive(Debug)]
pub struct Ast<'ast> {
    pub declarations: Vec<Declaration<'ast>, &'ast Bump>,
}

#[derive(Debug)]
pub enum Declaration<'ast> {
    Init(Block<'ast>),
    Run(Block<'ast>),
    ConstDef(ConstDef<'ast>),
    PublicConstDef(ConstDef<'ast>),
    Import(Import<'ast>),
}

#[derive(Debug)]
pub struct Import<'ast> {
    pub kind: ImportKind<'ast>,
    pub path: AstBox<'ast, str>,
}

#[derive(Debug)]
pub enum ImportKind<'ast> {
    All,
    As(IStr),
    Selection(AstBox<'ast, [IStr]>),
}

#[derive(Debug)]
pub struct Block<'ast> {
    pub statements: AstBox<'ast, [Statement<'ast>]>,
    pub last_expr: Option<AstBox<'ast, Expr<'ast>>>,
}

#[derive(Debug)]
pub struct ConstDef<'ast> {
    pub ident: IStr,
    pub r#type: Option<TypeExpr<'ast>>,
    pub expr: Expr<'ast>,
}

#[derive(Debug)]
pub enum Statement<'ast> {
    Let(AstBox<'ast, LetStmt<'ast>>),
    Return(Expr<'ast>),
    Assign(AstBox<'ast, AssignStmt<'ast>>),
    Block(Block<'ast>),
    Conditional(AstBox<'ast, Conditional<'ast, ()>>),
    Expr(Expr<'ast>),
    ConstDef(AstBox<'ast, ConstDef<'ast>>),
}

#[derive(Debug)]
pub struct LetStmt<'ast> {
    pub mutable: bool,
    pub ident: IStr,
    pub r#type: Option<TypeExpr<'ast>>,
    pub value: Expr<'ast>,
}

#[derive(Debug)]
pub struct AssignStmt<'ast> {
    pub target: NamePath<'ast>,
    pub op: AssignOp,
    pub value: Expr<'ast>,
}

#[derive(Debug)]
pub enum AssignTarget<'ast> {
    Ident(IStr),
    Member(Member<'ast>),
}

#[derive(Debug)]
pub struct IntLiteral<'ast> {
    pub positive: bool,
    pub num: FrozenBigUint<'ast>,
}

#[derive(Debug)]
pub enum TypeExpr<'ast> {
    NamePath(NamePath<'ast>),
    FnDef(AstBox<'ast, FnDef<'ast>>),
    StructDef(StructDef<'ast>),
}

#[derive(Debug)]
pub struct FnDef<'ast> {
    pub params: AstBox<'ast, [ParamDef<'ast>]>,
    pub result: TypeExpr<'ast>,
    pub body: Block<'ast>,
}

#[derive(Debug)]
pub struct ParamDef<'ast> {
    pub name: IStr,
    pub r#type: TypeExpr<'ast>,
}

#[derive(Debug)]
pub struct FieldDef<'ast> {
    pub name: IStr,
    pub r#type: TypeExpr<'ast>,
}

#[derive(Debug)]
pub struct StructDef<'ast> {
    pub fields: AstBox<'ast, [FieldDef<'ast>]>,
}

#[derive(Debug)]
pub struct FieldInit<'ast> {
    pub name: IStr,
    pub value: Expr<'ast>,
}

#[derive(Debug)]
pub struct StructLiteral<'ast> {
    pub type_path: NamePath<'ast>,
    pub fields: AstBox<'ast, [FieldInit<'ast>]>,
}

#[derive(Debug)]
pub struct NamePath<'ast>(pub AstBox<'ast, [IStr]>);

const _AST_SIZE: () = const {
    const_assert_eq(std::mem::size_of::<Expr<'_>>(), 32);
    const_assert_eq(std::mem::size_of::<LetStmt<'_>>(), 64);
    const_assert_eq(std::mem::size_of::<AssignStmt<'_>>(), 48);
    const_assert_eq(std::mem::size_of::<ConstDef<'_>>(), 64);

    const_assert_eq(std::mem::size_of::<Statement<'_>>(), 40);
    const_assert_eq(std::mem::size_of::<TypeExpr<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<Block<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<IntLiteral<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<IStr>(), 4);
    const_assert_eq(std::mem::size_of::<Member<'_>>(), 16);
    const_assert_eq(std::mem::size_of::<BinaryExpr<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<FnCall<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<Conditional<'_, ()>>(), 96);
};

#[derive(Debug)]
pub struct Spanned<T> {
    pub span: SourceSpan,
    pub inner: T,
}

impl<T> Spanned<T> {
    pub fn new(span: SourceSpan, inner: T) -> Self {
        Self { span, inner }
    }
}

pub type Ident = Spanned<IStr>;

#[derive(Debug)]
pub struct Member<'ast> {
    pub expr: AstBox<'ast, Expr<'ast>>,
    pub ident: IStr,
}

#[derive(Debug)]
pub enum Expr<'ast> {
    TypeExpr(TypeExpr<'ast>),
    Block(Block<'ast>),
    Binary(BinaryExpr<'ast>),
    IntLiteral(IntLiteral<'ast>),
    BoolLiteral(bool),
    Ident(IStr),
    Member(Member<'ast>),
    FnCall(FnCall<'ast>),
    Conditional(AstBox<'ast, Conditional<'ast, Infallible>>),
    StructLiteral(AstBox<'ast, StructLiteral<'ast>>),
}

#[derive(Debug)]
pub struct BinaryExpr<'ast> {
    pub lhs: AstBox<'ast, Expr<'ast>>,
    pub rhs: AstBox<'ast, Expr<'ast>>,
    pub op: BinaryOp,
}

#[derive(Debug)]
pub struct FnCall<'ast> {
    pub fn_expr: AstBox<'ast, Expr<'ast>>,
    pub param_exprs: AstBox<'ast, [Expr<'ast>]>,
}

#[derive(Debug)]
pub enum MaybeOr<Just, Other> {
    Just(Just),
    Other(Other),
}

#[derive(Debug)]
pub struct Conditional<'ast, ElseMissing> {
    pub r#if: IfBranch<'ast>,
    pub else_ifs: AstBox<'ast, [IfBranch<'ast>]>,
    pub else_body: MaybeOr<Block<'ast>, ElseMissing>,
}

#[derive(Debug)]
pub struct IfBranch<'ast> {
    pub condition: Expr<'ast>,
    pub body: Block<'ast>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinaryOp {
    // Arithmetic
    AddWrap,
    AddChecked,
    SubWrap,
    SubChecked,
    MulWrap,
    MulChecked,
    DivToPos,
    DivToNeg,
    DivToZero,
    DivFromZero,
    Mod,
    // Comparison
    LessThan,
    LessThanEquals,
    GreaterThan,
    GreaterThanEquals,
    EqualEqual,
    NotEquals,
    // Logical
    LogicalAnd,
    LogicalOr,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
}

#[derive(Debug)]
pub enum AssignOp {
    Assign,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_op_all_variants_exist() {
        let ops = [
            // Arithmetic
            BinaryOp::AddWrap,
            BinaryOp::AddChecked,
            BinaryOp::SubWrap,
            BinaryOp::SubChecked,
            BinaryOp::MulWrap,
            BinaryOp::MulChecked,
            BinaryOp::DivToPos,
            BinaryOp::DivToNeg,
            BinaryOp::DivToZero,
            BinaryOp::DivFromZero,
            BinaryOp::Mod,
            // Comparison
            BinaryOp::LessThan,
            BinaryOp::LessThanEquals,
            BinaryOp::GreaterThan,
            BinaryOp::GreaterThanEquals,
            BinaryOp::EqualEqual,
            BinaryOp::NotEquals,
            // Logical
            BinaryOp::LogicalAnd,
            BinaryOp::LogicalOr,
            // Bitwise
            BinaryOp::BitAnd,
            BinaryOp::BitOr,
            BinaryOp::BitXor,
            BinaryOp::ShiftLeft,
            BinaryOp::ShiftRight,
        ];
        assert_eq!(ops.len(), 24);
    }

    #[test]
    fn test_binary_op_equality() {
        assert_eq!(BinaryOp::AddWrap, BinaryOp::AddWrap);
        assert_ne!(BinaryOp::AddWrap, BinaryOp::SubWrap);
        assert_eq!(BinaryOp::LogicalAnd, BinaryOp::LogicalAnd);
        assert_ne!(BinaryOp::LogicalAnd, BinaryOp::LogicalOr);
    }

    #[test]
    fn test_binary_op_copy() {
        let op = BinaryOp::BitXor;
        let op2 = op;
        assert_eq!(op, op2);
    }
}
