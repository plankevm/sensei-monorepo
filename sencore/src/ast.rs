type Span = crate::Span<usize>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name {
    pub name: Box<str>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncDef {
    pub is_comptime: bool,
    pub func_bind: Name,
    pub bind_type_expr: Expr,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncApp {
    pub func_expr: Expr,
    pub applying_expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub lets: Vec<LetBind>,
    pub end_expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LetBind {
    pub span: Span,
    pub is_comptime: bool,
    pub bind_local: Name,
    pub assigned: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructField {
    pub span: Span,
    pub name: Name,
    pub r#type: Expr,
}

pub type StructDefUniqueId = u32;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructDef {
    pub def_uuid: StructDefUniqueId,
    pub fields_span: Span,
    pub fields: Vec<StructField>,
    pub associated_defs: Vec<LetBind>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructInitField {
    pub span: Span,
    pub name: Name,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructInit {
    pub struct_type: Expr,
    pub fields: Vec<StructInitField>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfThenElse {
    pub condition: Expr,
    pub true_branch: Expr,
    pub false_branch: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemberAccess {
    pub r#struct: Expr,
    pub member: Name,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
    /* Leaf Expressions */
    ConstVoid,
    ConstInt(i32),
    ConstBool(bool),
    Var(Box<str>),

    Value(Box<crate::comptime_value::Value>),

    MemberAccess(Box<MemberAccess>),
    IfThenElse(Box<IfThenElse>),
    FuncApp(Box<FuncApp>),
    Block(Box<Block>),
    FuncDef(Box<FuncDef>),
    StructDef(Box<StructDef>),
    StructInit(Box<StructInit>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

impl std::ops::Deref for Expr {
    type Target = ExprKind;

    fn deref(&self) -> &Self::Target {
        &self.kind
    }
}

#[derive(Debug)]
pub struct Ast {
    pub runtime_main: Expr,
}
