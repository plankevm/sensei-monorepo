use std::convert::Infallible;

use crate::const_print::const_assert_eq;
use allocator_api2::vec::Vec;
use bumpalo::Bump;
use inturn::Interner;
use neosen_data::{Span, X32, bigint::FrozenBigUint};

type HashMap<K, V, A> = hashbrown::HashMap<K, V, hashbrown::DefaultHashBuilder, A>;

pub struct InternedString;
pub type IStr = X32<InternedString>;
pub type StringInterner = Interner<IStr>;
pub type AstBox<'ast, T> = &'ast mut T;

pub struct Ast<'ast> {
    pub declarations: Vec<Declaration<'ast>, &'ast Bump>,
}

type SourceSpan = Span<u32>;

pub enum Declaration<'ast> {
    Init(Block<'ast>),
    Run(Block<'ast>),
    ConstDef(ConstDef<'ast>),
}

pub struct Block<'ast> {
    pub statements: AstBox<'ast, [Statement<'ast>]>,
    pub last_expr: Option<AstBox<'ast, Expr<'ast>>>,
}

pub struct ConstDef<'ast> {
    pub ident: IStr,
    pub r#type: Option<TypeExpr<'ast>>,
    pub expr: Expr<'ast>,
}

pub enum Statement<'ast> {
    Let(AstBox<'ast, LetStmt<'ast>>),
    Return(Expr<'ast>),
    Assign(AssignStmt<'ast>),
    Block(Block<'ast>),
    Conditional(AstBox<'ast, Conditional<'ast, ()>>),
    Expr(Expr<'ast>),
    ConstDef(AstBox<'ast, ConstDef<'ast>>),
}

pub struct LetStmt<'ast> {
    pub mutable: bool,
    pub ident: IStr,
    pub r#type: Option<TypeExpr<'ast>>,
    pub value: Expr<'ast>,
}

pub struct AssignStmt<'ast> {
    pub target: AssignTarget<'ast>,
    pub op: AssignOp,
    pub value: Expr<'ast>,
}

pub enum AssignTarget<'ast> {
    Ident(IStr),
    Member(Member<'ast>),
}

pub struct IntLiteral<'ast> {
    pub positive: bool,
    pub num: FrozenBigUint<'ast>,
}

pub enum TypeExpr<'ast> {
    NamePath(NamePath<'ast>),
    FnDef(AstBox<'ast, FnDef<'ast>>),
    StructDef(StructDef<'ast>),
}

pub struct FnDef<'ast> {
    pub params: AstBox<'ast, [ParamDef<'ast>]>,
    pub result: TypeExpr<'ast>,
    pub body: Block<'ast>,
}

pub struct ParamDef<'ast> {
    pub name: IStr,
    pub r#type: TypeExpr<'ast>,
}

pub struct FieldDef<'ast> {
    pub name: IStr,
    pub r#type: TypeExpr<'ast>,
}

pub struct StructDef<'ast> {
    pub fields: AstBox<'ast, [FieldDef<'ast>]>,
}

pub struct FieldInit<'ast> {
    pub name: IStr,
    pub value: Expr<'ast>,
}

pub struct StructLiteral<'ast> {
    pub type_path: NamePath<'ast>,
    pub fields: AstBox<'ast, [FieldInit<'ast>]>,
}

pub struct NamePath<'ast> {
    pub path_segments: AstBox<'ast, [IStr]>,
    pub final_member: IStr,
}

const _AST_SIZE: () = const {
    const_assert_eq(std::mem::size_of::<Expr<'_>>(), 32);
    const_assert_eq(std::mem::size_of::<LetStmt<'_>>(), 72);
    const_assert_eq(std::mem::size_of::<AssignStmt<'_>>(), 48);
    const_assert_eq(std::mem::size_of::<ConstDef<'_>>(), 72);

    const_assert_eq(std::mem::size_of::<Statement<'_>>(), 48);
    const_assert_eq(std::mem::size_of::<TypeExpr<'_>>(), 32);
    const_assert_eq(std::mem::size_of::<Block<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<IntLiteral<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<IStr>(), 4);
    const_assert_eq(std::mem::size_of::<Member<'_>>(), 16);
    const_assert_eq(std::mem::size_of::<BinaryExpr<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<FnCall<'_>>(), 24);
    const_assert_eq(std::mem::size_of::<Conditional<'_, ()>>(), 96);
};

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

pub struct Member<'ast> {
    pub expr: AstBox<'ast, Expr<'ast>>,
    pub ident: IStr,
}

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

pub struct BinaryExpr<'ast> {
    pub lhs: AstBox<'ast, Expr<'ast>>,
    pub rhs: AstBox<'ast, Expr<'ast>>,
    pub op: BinaryOp,
}

pub struct FnCall<'ast> {
    pub fn_expr: AstBox<'ast, Expr<'ast>>,
    pub param_exprs: AstBox<'ast, [Expr<'ast>]>,
}

pub enum MaybeOr<Just, Other> {
    Just(Just),
    Other(Other),
}

pub struct Conditional<'ast, ElseMissing> {
    pub r#if: IfBranch<'ast>,
    pub else_ifs: AstBox<'ast, [IfBranch<'ast>]>,
    pub else_body: MaybeOr<Block<'ast>, ElseMissing>,
}

pub struct IfBranch<'ast> {
    pub condition: Expr<'ast>,
    pub body: Block<'ast>,
}

#[derive(Copy, Clone)]
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
    // Logical
    LessThan,
    LessThanEquals,
    GreaterThan,
    GreaterThanEquals,
    EqualEqual,
}

pub enum AssignOp {
    Assign,
}
