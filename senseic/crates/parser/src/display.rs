use std::fmt::{self, Display};

use crate::ast::*;

/// Wrapper for displaying an AST in s-expression format with indentation and spans.
pub struct AstDisplay<'ast> {
    ast: &'ast Ast<'ast>,
    interner: &'ast StringInterner,
}

impl<'ast, 'src> AstDisplay<'ast> {
    pub fn new(ast: &'ast Ast<'ast>, interner: &'ast StringInterner) -> Self {
        Self { ast, interner }
    }
}

impl<'ast> Display for AstDisplay<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ctx = DisplayContext { interner: self.interner, indent: 0 };
        ctx.fmt_ast(f, self.ast)
    }
}

struct DisplayContext<'ast> {
    interner: &'ast StringInterner,
    indent: usize,
}

impl<'ast> DisplayContext<'ast> {
    fn write_indent(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..self.indent {
            write!(f, "  ")?;
        }
        Ok(())
    }

    fn with_indent<R>(&mut self, delta: usize, func: impl FnOnce(&mut Self) -> R) -> R {
        self.indent += delta;
        let result = func(self);
        self.indent -= delta;
        result
    }

    fn lookup(&self, istr: IStr) -> &str {
        self.interner.resolve(istr)
    }

    fn fmt_span(&self, f: &mut fmt::Formatter<'_>, span: &neosen_data::Span<u32>) -> fmt::Result {
        write!(f, "[{}..{}]", span.start, span.end)
    }

    fn fmt_ast(&mut self, f: &mut fmt::Formatter<'_>, ast: &Ast<'ast>) -> fmt::Result {
        if ast.declarations.is_empty() {
            write!(f, "(ast)")
        } else {
            writeln!(f, "(ast")?;
            self.with_indent(1, |ctx| {
                for decl in &ast.declarations {
                    ctx.write_indent(f)?;
                    ctx.fmt_declaration(f, decl)?;
                    writeln!(f)?;
                }
                Ok(())
            })?;
            write!(f, ")")
        }
    }

    fn fmt_declaration(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        decl: &Declaration<'ast>,
    ) -> fmt::Result {
        match decl {
            Declaration::Init(block) => {
                writeln!(f, "(init")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    ctx.fmt_block(f, block)
                })?;
                writeln!(f)?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Declaration::Run(block) => {
                writeln!(f, "(run")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    ctx.fmt_block(f, block)
                })?;
                writeln!(f)?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Declaration::ConstDef(const_def) => {
                write!(f, "(const-def {:?}", self.lookup(const_def.ident))?;
                writeln!(f)?;
                self.with_indent(1, |ctx| {
                    if let Some(ty) = &const_def.r#type {
                        ctx.write_indent(f)?;
                        writeln!(f, "(type")?;
                        ctx.with_indent(1, |ctx| {
                            ctx.write_indent(f)?;
                            ctx.fmt_type_expr(f, ty)
                        })?;
                        writeln!(f)?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    ctx.write_indent(f)?;
                    writeln!(f, "(value")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, &const_def.expr)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
        }
    }

    fn fmt_block(&mut self, f: &mut fmt::Formatter<'_>, block: &Block<'ast>) -> fmt::Result {
        if block.statements.is_empty() && block.last_expr.is_none() {
            write!(f, "(block)")
        } else {
            writeln!(f, "(block")?;
            self.with_indent(1, |ctx| {
                for stmt in block.statements.iter() {
                    ctx.write_indent(f)?;
                    ctx.fmt_statement(f, stmt)?;
                    writeln!(f)?;
                }
                if let Some(end_expr) = &block.last_expr {
                    ctx.write_indent(f)?;
                    writeln!(f, "(trailing-expr")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, end_expr)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                }
                Ok(())
            })?;
            self.write_indent(f)?;
            write!(f, ")")
        }
    }

    fn fmt_statement(&mut self, f: &mut fmt::Formatter<'_>, stmt: &Statement<'ast>) -> fmt::Result {
        match stmt {
            Statement::Let(let_stmt) => {
                write!(f, "(let {:?}", self.lookup(let_stmt.ident))?;
                if let_stmt.mutable {
                    write!(f, " mut")?;
                }
                writeln!(f)?;
                self.with_indent(1, |ctx| {
                    if let Some(ty) = &let_stmt.r#type {
                        ctx.write_indent(f)?;
                        writeln!(f, "(type")?;
                        ctx.with_indent(1, |ctx| {
                            ctx.write_indent(f)?;
                            ctx.fmt_type_expr(f, ty)
                        })?;
                        writeln!(f)?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    ctx.write_indent(f)?;
                    writeln!(f, "(value")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, &let_stmt.value)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Statement::Return(expr) => {
                writeln!(f, "(return")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    ctx.fmt_expr(f, expr)
                })?;
                writeln!(f)?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Statement::Assign(assign) => {
                write!(f, "(assign ")?;
                self.fmt_assign_op(f, &assign.op)?;
                writeln!(f)?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    write!(f, "(target ")?;
                    ctx.fmt_assign_target(f, &assign.target)?;
                    writeln!(f, ")")?;
                    ctx.write_indent(f)?;
                    writeln!(f, "(value")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, &assign.value)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Statement::Block(block) => self.fmt_block(f, block),
            Statement::Conditional(cond) => {
                writeln!(f, "(conditional")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    writeln!(f, "(if")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_if_branch(f, &cond.r#if)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    for else_if in cond.else_ifs.iter() {
                        ctx.write_indent(f)?;
                        writeln!(f, "(else-if")?;
                        ctx.with_indent(1, |ctx| {
                            ctx.write_indent(f)?;
                            ctx.fmt_if_branch(f, else_if)
                        })?;
                        writeln!(f)?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    match &cond.else_body {
                        MaybeOr::Just(else_body) => {
                            ctx.write_indent(f)?;
                            writeln!(f, "(else")?;
                            ctx.with_indent(1, |ctx| {
                                ctx.write_indent(f)?;
                                ctx.fmt_block(f, else_body)
                            })?;
                            writeln!(f)?;
                            ctx.write_indent(f)?;
                            writeln!(f, ")")?;
                        }
                        MaybeOr::Other(_) => {}
                    }
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Statement::Expr(expr) => {
                writeln!(f, "(expr")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    ctx.fmt_expr(f, expr)
                })?;
                writeln!(f)?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Statement::ConstDef(const_def) => {
                write!(f, "(const-def {:?}", self.lookup(const_def.ident))?;
                writeln!(f)?;
                self.with_indent(1, |ctx| {
                    if let Some(ty) = &const_def.r#type {
                        ctx.write_indent(f)?;
                        writeln!(f, "(type")?;
                        ctx.with_indent(1, |ctx| {
                            ctx.write_indent(f)?;
                            ctx.fmt_type_expr(f, ty)
                        })?;
                        writeln!(f)?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    ctx.write_indent(f)?;
                    writeln!(f, "(value")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, &const_def.expr)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
        }
    }

    fn fmt_assign_target(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        target: &AssignTarget<'ast>,
    ) -> fmt::Result {
        match target {
            AssignTarget::Ident(istr) => write!(f, "{:?}", self.lookup(*istr)),
            AssignTarget::Member(member) => {
                write!(f, "(member {:?}", self.lookup(member.ident))?;
                writeln!(f)?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    ctx.fmt_expr(f, member.expr)
                })?;
                writeln!(f)?;
                self.write_indent(f)?;
                write!(f, ")")
            }
        }
    }

    fn fmt_assign_op(&self, f: &mut fmt::Formatter<'_>, op: &AssignOp) -> fmt::Result {
        match op {
            AssignOp::Assign => write!(f, "="),
        }
    }

    fn fmt_expr(&mut self, f: &mut fmt::Formatter<'_>, expr: &Expr<'ast>) -> fmt::Result {
        match expr {
            Expr::TypeExpr(type_expr) => {
                write!(f, "(type-expr")?;
                writeln!(f)?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    ctx.fmt_type_expr(f, type_expr)
                })?;
                writeln!(f)?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Expr::Block(block) => self.fmt_block(f, block),
            Expr::Binary(binary) => {
                write!(f, "(binary ")?;
                self.fmt_binary_op(f, &binary.op)?;
                writeln!(f)?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    write!(f, "(lhs")?;
                    writeln!(f)?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, &binary.lhs)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    ctx.write_indent(f)?;
                    write!(f, "(rhs")?;
                    writeln!(f)?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, &binary.rhs)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Expr::IntLiteral(int_lit) => {
                write!(f, "(int ")?;
                self.fmt_int_literal(f, int_lit)?;
                write!(f, ")")
            }
            Expr::BoolLiteral(b) => write!(f, "(bool {})", b),
            Expr::Ident(istr) => write!(f, "(ident {:?})", self.lookup(*istr)),
            Expr::Member(member) => {
                write!(f, "(member {:?}", self.lookup(member.ident))?;
                writeln!(f)?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    ctx.fmt_expr(f, member.expr)
                })?;
                writeln!(f)?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Expr::FnCall(fn_call) => {
                writeln!(f, "(fn-call")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    write!(f, "(fn")?;
                    writeln!(f)?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, &fn_call.fn_expr)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    ctx.write_indent(f)?;
                    if fn_call.param_exprs.is_empty() {
                        writeln!(f, "(args)")?;
                    } else {
                        writeln!(f, "(args")?;
                        ctx.with_indent(1, |ctx| {
                            for arg in fn_call.param_exprs.iter() {
                                ctx.write_indent(f)?;
                                ctx.fmt_expr(f, arg)?;
                                writeln!(f)?;
                            }
                            Ok(())
                        })?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Expr::Conditional(cond) => {
                writeln!(f, "(conditional")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    writeln!(f, "(if")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_if_branch(f, &cond.r#if)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    for else_if in cond.else_ifs.iter() {
                        ctx.write_indent(f)?;
                        writeln!(f, "(else-if")?;
                        ctx.with_indent(1, |ctx| {
                            ctx.write_indent(f)?;
                            ctx.fmt_if_branch(f, else_if)
                        })?;
                        writeln!(f)?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    // For Expr::Conditional, else_body is MaybeOr<Block, Infallible>
                    // Since Infallible can't be constructed, it's always Just(block)
                    match &cond.else_body {
                        MaybeOr::Just(else_body) => {
                            ctx.write_indent(f)?;
                            writeln!(f, "(else")?;
                            ctx.with_indent(1, |ctx| {
                                ctx.write_indent(f)?;
                                ctx.fmt_block(f, else_body)
                            })?;
                            writeln!(f)?;
                            ctx.write_indent(f)?;
                            writeln!(f, ")")?;
                        }
                        MaybeOr::Other(infallible) => match *infallible {},
                    }
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            Expr::StructLiteral(struct_lit) => {
                writeln!(f, "(struct-literal")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    write!(f, "(type ")?;
                    ctx.fmt_name_path(f, &struct_lit.type_path)?;
                    writeln!(f, ")")?;
                    ctx.write_indent(f)?;
                    if struct_lit.fields.is_empty() {
                        writeln!(f, "(fields)")?;
                    } else {
                        writeln!(f, "(fields")?;
                        ctx.with_indent(1, |ctx| {
                            for field in struct_lit.fields.iter() {
                                ctx.write_indent(f)?;
                                write!(f, "(field {:?}", ctx.lookup(field.name))?;
                                writeln!(f)?;
                                ctx.with_indent(1, |ctx| {
                                    ctx.write_indent(f)?;
                                    ctx.fmt_expr(f, &field.value)
                                })?;
                                writeln!(f)?;
                                ctx.write_indent(f)?;
                                writeln!(f, ")")?;
                            }
                            Ok(())
                        })?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
        }
    }

    fn fmt_if_branch(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        branch: &IfBranch<'ast>,
    ) -> fmt::Result {
        writeln!(f, "(if-branch")?;
        self.with_indent(1, |ctx| {
            ctx.write_indent(f)?;
            writeln!(f, "(condition")?;
            ctx.with_indent(1, |ctx| {
                ctx.write_indent(f)?;
                ctx.fmt_expr(f, &branch.condition)
            })?;
            writeln!(f)?;
            ctx.write_indent(f)?;
            writeln!(f, ")")?;
            ctx.write_indent(f)?;
            writeln!(f, "(body")?;
            ctx.with_indent(1, |ctx| {
                ctx.write_indent(f)?;
                ctx.fmt_block(f, &branch.body)
            })?;
            writeln!(f)?;
            ctx.write_indent(f)?;
            writeln!(f, ")")?;
            Ok(())
        })?;
        self.write_indent(f)?;
        write!(f, ")")
    }

    fn fmt_binary_op(&self, f: &mut fmt::Formatter<'_>, op: &BinaryOp) -> fmt::Result {
        let op_str = match op {
            BinaryOp::AddWrap => "+%",
            BinaryOp::AddChecked => "+",
            BinaryOp::SubWrap => "-%",
            BinaryOp::SubChecked => "-",
            BinaryOp::MulWrap => "*%",
            BinaryOp::MulChecked => "*",
            BinaryOp::DivToPos => "/+",
            BinaryOp::DivToNeg => "/-",
            BinaryOp::DivToZero => "/$",
            BinaryOp::DivFromZero => "/^",
            BinaryOp::LessThan => "<",
            BinaryOp::LessThanEquals => "<=",
            BinaryOp::GreaterThan => ">",
            BinaryOp::GreaterThanEquals => ">=",
            BinaryOp::EqualEqual => "==",
        };
        write!(f, "{}", op_str)
    }

    fn fmt_int_literal(&self, f: &mut fmt::Formatter<'_>, int_lit: &IntLiteral) -> fmt::Result {
        if !int_lit.positive {
            write!(f, "-")?;
        }

        write!(f, "0x{:x}", int_lit.num)
    }

    fn fmt_type_expr(&mut self, f: &mut fmt::Formatter<'_>, ty: &TypeExpr<'ast>) -> fmt::Result {
        match ty {
            TypeExpr::NamePath(name_path) => self.fmt_name_path(f, name_path),
            TypeExpr::FnDef(fn_def) => {
                writeln!(f, "(fn-def")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    if fn_def.params.is_empty() {
                        writeln!(f, "(params)")?;
                    } else {
                        writeln!(f, "(params")?;
                        ctx.with_indent(1, |ctx| {
                            for param in fn_def.params.iter() {
                                ctx.write_indent(f)?;
                                write!(f, "(param {:?}", ctx.lookup(param.name))?;
                                writeln!(f)?;
                                ctx.with_indent(1, |ctx| {
                                    ctx.write_indent(f)?;
                                    ctx.fmt_type_expr(f, &param.r#type)
                                })?;
                                writeln!(f)?;
                                ctx.write_indent(f)?;
                                writeln!(f, ")")?;
                            }
                            Ok(())
                        })?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    ctx.write_indent(f)?;
                    writeln!(f, "(result")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_type_expr(f, &fn_def.result)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    ctx.write_indent(f)?;
                    writeln!(f, "(body")?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_block(f, &fn_def.body)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
            TypeExpr::StructDef(struct_def) => {
                writeln!(f, "(struct-def")?;
                self.with_indent(1, |ctx| {
                    ctx.write_indent(f)?;
                    if struct_def.fields.is_empty() {
                        writeln!(f, "(fields)")?;
                    } else {
                        writeln!(f, "(fields")?;
                        ctx.with_indent(1, |ctx| {
                            for field in struct_def.fields.iter() {
                                ctx.write_indent(f)?;
                                write!(f, "(field {:?}", ctx.lookup(field.name))?;
                                writeln!(f)?;
                                ctx.with_indent(1, |ctx| {
                                    ctx.write_indent(f)?;
                                    ctx.fmt_type_expr(f, &field.r#type)
                                })?;
                                writeln!(f)?;
                                ctx.write_indent(f)?;
                                writeln!(f, ")")?;
                            }
                            Ok(())
                        })?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
                    Ok(())
                })?;
                self.write_indent(f)?;
                write!(f, ")")
            }
        }
    }

    fn fmt_name_path(&self, f: &mut fmt::Formatter<'_>, name_path: &NamePath) -> fmt::Result {
        write!(f, "(name-path")?;
        for segment in name_path.path_segments.iter() {
            write!(f, " {:?}", self.lookup(*segment))?;
        }
        write!(f, " {:?})", self.lookup(name_path.final_member))
    }
}
