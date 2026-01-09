use std::fmt::{self, Display};

use crate::ast::*;

/// Wrapper for displaying an AST in s-expression format with indentation and spans.
pub struct AstDisplay<'b, 'ast> {
    ast: &'b Ast<'ast>,
    interner: &'b StringInterner,
}

impl<'b, 'ast> AstDisplay<'b, 'ast> {
    pub fn new(ast: &'b Ast<'ast>, interner: &'b StringInterner) -> Self {
        Self { ast, interner }
    }
}

impl<'b, 'ast> Display for AstDisplay<'b, 'ast> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ctx = DisplayContext { interner: self.interner, indent: 0 };
        ctx.fmt_ast(f, self.ast)
    }
}

struct DisplayContext<'i> {
    interner: &'i StringInterner,
    indent: usize,
}

impl<'i> DisplayContext<'i> {
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

    fn fmt_ast(&mut self, f: &mut fmt::Formatter<'_>, ast: &Ast<'_>) -> fmt::Result {
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
        decl: &Declaration<'_>,
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
            Declaration::PublicConstDef(const_def) => {
                self.fmt_const_def(f, const_def, "public-const-def")
            }
            Declaration::ConstDef(const_def) => {
                self.fmt_const_def(f, const_def, "private-const-def")
            }
            Declaration::Import(import) => {
                write!(f, "(import ")?;
                self.fmt_import_kind(f, &import.kind)?;
                write!(f, " {:?})", import.path)
            }
        }
    }

    fn fmt_import_kind(&self, f: &mut fmt::Formatter<'_>, kind: &ImportKind<'_>) -> fmt::Result {
        match kind {
            ImportKind::All => write!(f, "*"),
            ImportKind::As(alias) => write!(f, "(as {:?})", self.lookup(*alias)),
            ImportKind::Selection(items) => {
                write!(f, "(choice")?;
                for item in items.iter() {
                    write!(f, " {:?}", self.lookup(*item))?;
                }
                write!(f, ")")
            }
        }
    }

    fn fmt_const_def(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        const_def: &ConstDef<'_>,
        name: &'static str,
    ) -> fmt::Result {
        write!(f, "({} {:?}", name, self.lookup(const_def.ident))?;
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

    fn fmt_block(&mut self, f: &mut fmt::Formatter<'_>, block: &Block<'_>) -> fmt::Result {
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

    fn fmt_statement(&mut self, f: &mut fmt::Formatter<'_>, stmt: &Statement<'_>) -> fmt::Result {
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
                    ctx.fmt_name_path(f, &assign.target)?;
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

    fn fmt_assign_op(&self, f: &mut fmt::Formatter<'_>, op: &AssignOp) -> fmt::Result {
        match op {
            AssignOp::Assign => write!(f, "="),
        }
    }

    fn fmt_expr(&mut self, f: &mut fmt::Formatter<'_>, expr: &Expr<'_>) -> fmt::Result {
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
                        ctx.fmt_expr(f, binary.lhs)
                    })?;
                    writeln!(f)?;
                    ctx.write_indent(f)?;
                    writeln!(f, ")")?;
                    ctx.write_indent(f)?;
                    write!(f, "(rhs")?;
                    writeln!(f)?;
                    ctx.with_indent(1, |ctx| {
                        ctx.write_indent(f)?;
                        ctx.fmt_expr(f, binary.rhs)
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
                        ctx.fmt_expr(f, fn_call.fn_expr)
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

    fn fmt_if_branch(&mut self, f: &mut fmt::Formatter<'_>, branch: &IfBranch<'_>) -> fmt::Result {
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
            BinaryOp::DivToZero => "/<",
            BinaryOp::DivFromZero => "/>",
            BinaryOp::Mod => "%",
            BinaryOp::LessThan => "<",
            BinaryOp::LessThanEquals => "<=",
            BinaryOp::GreaterThan => ">",
            BinaryOp::GreaterThanEquals => ">=",
            BinaryOp::EqualEqual => "==",
            BinaryOp::NotEquals => "!=",
            BinaryOp::LogicalAnd => "&&",
            BinaryOp::LogicalOr => "||",
            BinaryOp::BitAnd => "&",
            BinaryOp::BitOr => "|",
            BinaryOp::BitXor => "^",
            BinaryOp::ShiftLeft => "<<",
            BinaryOp::ShiftRight => ">>",
        };
        write!(f, "{}", op_str)
    }

    fn fmt_int_literal(&self, f: &mut fmt::Formatter<'_>, int_lit: &IntLiteral) -> fmt::Result {
        if !int_lit.positive {
            write!(f, "-")?;
        }

        write!(f, "0x{:x}", int_lit.num)
    }

    fn fmt_type_expr(&mut self, f: &mut fmt::Formatter<'_>, ty: &TypeExpr<'_>) -> fmt::Result {
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
                    if let Some(result_ty) = &fn_def.result {
                        ctx.write_indent(f)?;
                        writeln!(f, "(result")?;
                        ctx.with_indent(1, |ctx| {
                            ctx.write_indent(f)?;
                            ctx.fmt_type_expr(f, result_ty)
                        })?;
                        writeln!(f)?;
                        ctx.write_indent(f)?;
                        writeln!(f, ")")?;
                    }
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
        let name_path = &name_path.0;
        let last_member_index = name_path.len() - 1;
        for segment in &name_path[..last_member_index] {
            write!(f, " {:?}", self.lookup(*segment))?;
        }
        write!(f, " {:?})", self.lookup(name_path[last_member_index]))
    }
}
