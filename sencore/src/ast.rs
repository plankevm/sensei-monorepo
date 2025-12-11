type Span = crate::Span<usize>;

#[derive(Debug, Clone)]
pub struct Name {
    pub name: Box<str>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub func_bind: Name,
    pub bind_type_expr: Expr,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct FuncApp {
    pub func_expr: Expr,
    pub applying_expr: Expr,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub lets: Vec<LetBind>,
    pub end_expr: Expr,
}

#[derive(Debug, Clone)]
pub struct LetBind {
    pub span: Span,
    pub recursive: bool,
    pub bind_local: Name,
    pub local_type: Option<Expr>,
    pub assigned: Expr,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub span: Span,
    pub name: Name,
    pub r#type: Expr,
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub def_uuid: u32,
    pub fields_span: Span,
    pub fields: Vec<StructField>,
    pub associated_defs: Vec<LetBind>,
}

#[derive(Debug, Clone)]
pub struct StructInitField {
    pub span: Span,
    pub name: Name,
    pub value: Expr,
}

#[derive(Debug, Clone)]
pub struct StructInit {
    pub struct_type: Expr,
    pub fields: Vec<StructInitField>,
}

#[derive(Debug, Clone)]
pub struct IfThenElse {
    pub span: Span,
    pub condition: Expr,
    pub true_branch: Expr,
    pub false_branch: Expr,
}

#[derive(Debug, Clone)]
pub struct MemberAccess {
    pub r#struct: Expr,
    pub member: Name,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /* Leaf Expressions */
    ConstVoid,
    ConstInt(i32),
    ConstBool(bool),
    Var(Box<str>),

    FuncApp(Box<FuncApp>),
    IfThenElse(Box<IfThenElse>),
    Block(Box<Block>),
    MemberAccess(Box<MemberAccess>),
    FuncDef(Box<FuncDef>),
    StructDef(Box<StructDef>),
    StructInit(Box<StructInit>),
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub struct Ast {
    pub runtime_main: Expr,
}
