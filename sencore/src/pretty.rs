use crate::ast::*;
use crate::comptime_value::{Closure, StructType, StructValue, Type, Value, VirtualMemoryPointer};
use std::fmt::{self, Display, Write};

const INDENT: &str = "  ";

/// Returns true if the type is simple (can be printed inline).
fn is_simple_type(ty: &Type) -> bool {
    match ty {
        Type::Void | Type::Num | Type::Bool | Type::MemoryPointer | Type::Type | Type::Function => {
            true
        }
        Type::Struct(_) => false,
    }
}

/// Returns true if the value is simple (can be printed inline).
fn is_simple_value(value: &Value) -> bool {
    match value {
        Value::Void | Value::Num(_) | Value::Bool(_) | Value::MemoryPointer(_) => true,
        Value::Type(ty) => is_simple_type(ty),
        Value::Struct(_) | Value::Closure(_) => false,
    }
}

/// Returns true if the expression is "simple" (should be printed inline).
/// Compound expressions like func, if, block, etc. return false.
fn is_simple(expr: &Expr) -> bool {
    match &expr.kind {
        // Leaf expressions are always simple
        ExprKind::ConstVoid | ExprKind::ConstInt(_) | ExprKind::ConstBool(_) | ExprKind::Var(_) => {
            true
        }

        ExprKind::Value(v) => is_simple_value(v),

        // Compound forms are never simple
        ExprKind::FuncDef(_)
        | ExprKind::FuncApp(_)
        | ExprKind::IfThenElse(_)
        | ExprKind::Block(_)
        | ExprKind::StructDef(_) => false,

        // StructInit is simple only if it has no fields
        ExprKind::StructInit(init) => init.fields.is_empty() && is_simple(&init.struct_type),

        // MemberAccess is simple if the struct expr is simple
        ExprKind::MemberAccess(m) => is_simple(&m.r#struct),
    }
}

pub struct PrettyPrinter<'a, W: Write> {
    out: &'a mut W,
    indent: usize,
}

impl<'a, W: Write> PrettyPrinter<'a, W> {
    pub fn new(out: &'a mut W) -> Self {
        Self { out, indent: 0 }
    }

    fn write_indent(&mut self) -> fmt::Result {
        for _ in 0..self.indent {
            self.out.write_str(INDENT)?;
        }
        Ok(())
    }

    fn indented<F>(&mut self, f: F) -> fmt::Result
    where
        F: FnOnce(&mut Self) -> fmt::Result,
    {
        self.indent += 1;
        let result = f(self);
        self.indent -= 1;
        result
    }

    pub fn print_expr(&mut self, expr: &Expr) -> fmt::Result {
        match &expr.kind {
            ExprKind::ConstVoid => write!(self.out, "()"),
            ExprKind::ConstInt(n) => write!(self.out, "{}", n),
            ExprKind::ConstBool(b) => write!(self.out, "{}", b),
            ExprKind::Var(name) => write!(self.out, "{}", name),

            ExprKind::Value(v) => self.print_value(v),

            ExprKind::FuncDef(def) => self.print_func_def(def),
            ExprKind::FuncApp(_) => self.print_func_app(expr),
            ExprKind::IfThenElse(ite) => self.print_if_then_else(ite),
            ExprKind::Block(block) => self.print_block(block),
            ExprKind::MemberAccess(_) => self.print_member_access(expr),
            ExprKind::StructDef(def) => self.print_struct_def(def),
            ExprKind::StructInit(init) => self.print_struct_init(init),
        }
    }

    fn print_func_def(&mut self, def: &FuncDef) -> fmt::Result {
        if def.is_comptime {
            write!(self.out, "(func comptime {} ", def.func_bind.name)?;
        } else {
            write!(self.out, "(func {} ", def.func_bind.name)?;
        }
        self.print_expr(&def.bind_type_expr)?;

        if is_simple(&def.body) {
            write!(self.out, " ")?;
            self.print_expr(&def.body)?;
            write!(self.out, ")")
        } else {
            self.indented(|this| {
                writeln!(this.out)?;
                this.write_indent()?;
                this.print_expr(&def.body)
            })?;
            writeln!(self.out)?;
            self.write_indent()?;
            write!(self.out, ")")
        }
    }

    /// Unfold left-nested FuncApp into (e1 e2 ... eN)
    fn print_func_app(&mut self, expr: &Expr) -> fmt::Result {
        let mut args = Vec::new();
        let mut current = expr;

        // Walk the left-nested FuncApp chain
        while let ExprKind::FuncApp(app) = &current.kind {
            args.push(&app.applying_expr);
            current = &app.func_expr;
        }

        // current is now the leftmost expression (e1)
        // args contains [eN, ..., e3, e2] in reverse order
        args.reverse();

        let all_simple = is_simple(current) && args.iter().all(|a| is_simple(a));

        write!(self.out, "(")?;
        self.print_expr(current)?;

        if all_simple {
            for arg in args {
                write!(self.out, " ")?;
                self.print_expr(arg)?;
            }
            write!(self.out, ")")
        } else {
            self.indented(|this| {
                for arg in args {
                    writeln!(this.out)?;
                    this.write_indent()?;
                    this.print_expr(arg)?;
                }
                Ok(())
            })?;
            writeln!(self.out)?;
            self.write_indent()?;
            write!(self.out, ")")
        }
    }

    fn print_if_then_else(&mut self, ite: &IfThenElse) -> fmt::Result {
        let branches_simple = is_simple(&ite.true_branch) && is_simple(&ite.false_branch);

        write!(self.out, "(if ")?;
        self.print_expr(&ite.condition)?;

        if branches_simple {
            write!(self.out, " ")?;
            self.print_expr(&ite.true_branch)?;
            write!(self.out, " ")?;
            self.print_expr(&ite.false_branch)?;
            write!(self.out, ")")
        } else {
            self.indented(|this| {
                writeln!(this.out)?;
                this.write_indent()?;
                this.print_expr(&ite.true_branch)?;
                writeln!(this.out)?;
                this.write_indent()?;
                this.print_expr(&ite.false_branch)
            })?;
            writeln!(self.out)?;
            self.write_indent()?;
            write!(self.out, ")")
        }
    }

    fn print_block(&mut self, block: &Block) -> fmt::Result {
        if block.lets.is_empty() {
            write!(self.out, "(block ")?;
            self.print_expr(&block.end_expr)?;
            write!(self.out, ")")
        } else {
            write!(self.out, "(block")?;
            self.indented(|this| {
                for let_bind in &block.lets {
                    writeln!(this.out)?;
                    this.write_indent()?;
                    this.print_let_bind(let_bind)?;
                }
                writeln!(this.out)?;
                this.write_indent()?;
                this.print_expr(&block.end_expr)
            })?;
            writeln!(self.out)?;
            self.write_indent()?;
            write!(self.out, ")")
        }
    }

    fn print_let_bind(&mut self, let_bind: &LetBind) -> fmt::Result {
        if let_bind.is_comptime {
            write!(self.out, "(comptime {}", let_bind.bind_local.name)?;
        } else {
            write!(self.out, "({}", let_bind.bind_local.name)?;
        }
        write!(self.out, " ")?;
        self.print_expr(&let_bind.assigned)?;
        write!(self.out, ")")
    }

    /// Unfold left-nested MemberAccess into (attr seg1 seg2 ... struct_expr)
    fn print_member_access(&mut self, expr: &Expr) -> fmt::Result {
        let mut segments = Vec::new();
        let mut current = expr;

        // Walk the left-nested MemberAccess chain
        while let ExprKind::MemberAccess(access) = &current.kind {
            segments.push(&access.member);
            current = &access.r#struct;
        }

        // segments contains [segN, ..., seg2, seg1] in reverse order
        segments.reverse();

        write!(self.out, "(attr")?;
        for seg in segments {
            write!(self.out, " {}", seg.name)?;
        }
        write!(self.out, " ")?;
        self.print_expr(current)?;
        write!(self.out, ")")
    }

    fn print_struct_def(&mut self, def: &StructDef) -> fmt::Result {
        write!(self.out, "(struct_def")?;
        self.indented(|this| {
            // Fields section
            writeln!(this.out)?;
            this.write_indent()?;
            write!(this.out, "(fields")?;
            if !def.fields.is_empty() {
                this.indented(|this| {
                    for field in &def.fields {
                        writeln!(this.out)?;
                        this.write_indent()?;
                        write!(this.out, "({} ", field.name.name)?;
                        this.print_expr(&field.r#type)?;
                        write!(this.out, ")")?;
                    }
                    Ok(())
                })?;
                writeln!(this.out)?;
                this.write_indent()?;
            }
            write!(this.out, ")")?;

            // Defs section
            writeln!(this.out)?;
            this.write_indent()?;
            write!(this.out, "(defs")?;
            if !def.associated_defs.is_empty() {
                this.indented(|this| {
                    for assoc_def in &def.associated_defs {
                        writeln!(this.out)?;
                        this.write_indent()?;
                        this.print_let_bind(assoc_def)?;
                    }
                    Ok(())
                })?;
                writeln!(this.out)?;
                this.write_indent()?;
            }
            write!(this.out, ")")
        })?;
        writeln!(self.out)?;
        self.write_indent()?;
        write!(self.out, ")")
    }

    fn print_struct_init(&mut self, init: &StructInit) -> fmt::Result {
        write!(self.out, "(struct_init ")?;
        self.print_expr(&init.struct_type)?;
        for field in &init.fields {
            write!(self.out, " ({} ", field.name.name)?;
            self.print_expr(&field.value)?;
            write!(self.out, ")")?;
        }
        write!(self.out, ")")
    }

    // ========== Value Printing ==========

    fn print_value(&mut self, value: &Value) -> fmt::Result {
        match value {
            Value::Void => write!(self.out, "<value ()>"),
            Value::Num(n) => write!(self.out, "<value {}>", n),
            Value::Bool(b) => write!(self.out, "<value {}>", b),
            Value::MemoryPointer(ptr) => self.print_memory_pointer(ptr),
            Value::Type(ty) => self.print_type_value(ty),
            Value::Struct(s) => self.print_struct_value(s),
            Value::Closure(c) => self.print_closure_value(c),
        }
    }

    fn print_memory_pointer(&mut self, ptr: &VirtualMemoryPointer) -> fmt::Result {
        write!(self.out, "<value ptr@{}+{}>", ptr.allocation, ptr.offset)
    }

    fn print_type_value(&mut self, ty: &Type) -> fmt::Result {
        match ty {
            Type::Void => write!(self.out, "<value type:void>"),
            Type::Num => write!(self.out, "<value type:num>"),
            Type::Bool => write!(self.out, "<value type:bool>"),
            Type::MemoryPointer => write!(self.out, "<value type:ptr>"),
            Type::Type => write!(self.out, "<value type:type>"),
            Type::Function => write!(self.out, "<value type:fn>"),
            Type::Struct(st) => self.print_struct_type(st),
        }
    }

    fn print_struct_type(&mut self, st: &StructType) -> fmt::Result {
        write!(self.out, "<value type:(struct")?;
        self.indented(|this| {
            // Fields
            writeln!(this.out)?;
            this.write_indent()?;
            write!(this.out, "(fields")?;
            if !st.fields.is_empty() {
                this.indented(|this| {
                    for (name, ty) in &st.fields {
                        writeln!(this.out)?;
                        this.write_indent()?;
                        write!(this.out, "({} ", name)?;
                        this.print_type_inline(ty)?;
                        write!(this.out, ")")?;
                    }
                    Ok(())
                })?;
                writeln!(this.out)?;
                this.write_indent()?;
            }
            write!(this.out, ")")?;

            // Defs
            writeln!(this.out)?;
            this.write_indent()?;
            write!(this.out, "(defs")?;
            if !st.defs.is_empty() {
                this.indented(|this| {
                    for def in &st.defs {
                        writeln!(this.out)?;
                        this.write_indent()?;
                        this.print_value(def)?;
                    }
                    Ok(())
                })?;
                writeln!(this.out)?;
                this.write_indent()?;
            }
            write!(this.out, ")")
        })?;
        writeln!(self.out)?;
        self.write_indent()?;
        write!(self.out, ")>")
    }

    /// Print a type inline (without the <value ...> wrapper, for use inside struct types).
    fn print_type_inline(&mut self, ty: &Type) -> fmt::Result {
        match ty {
            Type::Void => write!(self.out, "void"),
            Type::Num => write!(self.out, "num"),
            Type::Bool => write!(self.out, "bool"),
            Type::MemoryPointer => write!(self.out, "ptr"),
            Type::Type => write!(self.out, "type"),
            Type::Function => write!(self.out, "fn"),
            Type::Struct(_) => write!(self.out, "struct"), // Simplified for inline
        }
    }

    fn print_struct_value(&mut self, sv: &StructValue) -> fmt::Result {
        write!(self.out, "<value (struct")?;
        self.indented(|this| {
            writeln!(this.out)?;
            this.write_indent()?;
            write!(this.out, "(type ")?;
            this.print_type_inline(&sv.r#type)?;
            write!(this.out, ")")?;

            for (i, field_value) in sv.field_values.iter().enumerate() {
                writeln!(this.out)?;
                this.write_indent()?;
                write!(this.out, "(field_{} ", i)?;
                this.print_value(field_value)?;
                write!(this.out, ")")?;
            }
            Ok(())
        })?;
        writeln!(self.out)?;
        self.write_indent()?;
        write!(self.out, ")>")
    }

    fn print_closure_value(&mut self, closure: &Closure) -> fmt::Result {
        write!(self.out, "<value (closure {} ", closure.binds)?;
        self.print_type_inline(&closure.r#type)?;

        if is_simple(&closure.body) {
            write!(self.out, " ")?;
            self.print_expr(&closure.body)?;
            write!(self.out, ")>")
        } else {
            self.indented(|this| {
                writeln!(this.out)?;
                this.write_indent()?;
                this.print_expr(&closure.body)
            })?;
            writeln!(self.out)?;
            self.write_indent()?;
            write!(self.out, ")>")
        }
    }

    pub fn print_ast(&mut self, ast: &Ast) -> fmt::Result {
        self.print_expr(&ast.runtime_main)
    }
}

pub fn pretty_print(expr: &Expr) -> String {
    let mut out = String::new();
    let mut printer = PrettyPrinter::new(&mut out);
    printer
        .print_expr(expr)
        .expect("formatting to string cannot fail");
    out
}

pub fn pretty_print_ast(ast: &Ast) -> String {
    let mut out = String::new();
    let mut printer = PrettyPrinter::new(&mut out);
    printer
        .print_ast(ast)
        .expect("formatting to string cannot fail");
    out
}

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut printer = PrettyPrinter::new(f);
        printer.print_expr(self)
    }
}

impl Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut printer = PrettyPrinter::new(f);
        printer.print_ast(self)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut printer = PrettyPrinter::new(f);
        printer.print_value(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{Parser, lower_sexpr_to_ast};

    fn parse(source: &str) -> Ast {
        let mut parser = Parser::new(source);
        let node = parser.parse_list().unwrap().expect("expected s-expr");
        lower_sexpr_to_ast(&node).unwrap()
    }

    #[test]
    fn test_constants() {
        assert_eq!(pretty_print_ast(&parse("(42)")), "42");
        assert_eq!(pretty_print_ast(&parse("(true)")), "true");
        assert_eq!(pretty_print_ast(&parse("(false)")), "false");
        assert_eq!(pretty_print_ast(&parse("(())")), "()");
    }

    #[test]
    fn test_var() {
        assert_eq!(pretty_print_ast(&parse("(foo)")), "foo");
    }

    #[test]
    fn test_func() {
        assert_eq!(
            pretty_print_ast(&parse("(func x word x)")),
            "(func x word x)"
        );
    }

    #[test]
    fn test_apply() {
        assert_eq!(pretty_print_ast(&parse("(apply f x)")), "(f x)");
        assert_eq!(pretty_print_ast(&parse("(apply f x y z)")), "(f x y z)");
    }

    #[test]
    fn test_if() {
        assert_eq!(pretty_print_ast(&parse("(if true 1 2)")), "(if true 1 2)");
    }

    #[test]
    fn test_block_empty() {
        assert_eq!(pretty_print_ast(&parse("(block x)")), "(block x)");
    }

    #[test]
    fn test_block_with_lets() {
        let ast = parse("(block (x 10) (y 20) x)");
        let output = pretty_print_ast(&ast);
        assert!(output.contains("(block"));
        assert!(output.contains("(x 10)"));
        assert!(output.contains("(y 20)"));
    }

    #[test]
    fn test_attr() {
        assert_eq!(
            pretty_print_ast(&parse("(attr foo my_struct)")),
            "(attr foo my_struct)"
        );
        assert_eq!(
            pretty_print_ast(&parse("(attr foo bar my_struct)")),
            "(attr foo bar my_struct)"
        );
    }

    #[test]
    fn test_struct_def() {
        let ast = parse("(struct_def (fields (x word) (y bool)) (defs))");
        let output = pretty_print_ast(&ast);
        assert!(output.contains("(struct_def"));
        assert!(output.contains("(fields"));
        assert!(output.contains("(x word)"));
        assert!(output.contains("(y bool)"));
        assert!(output.contains("(defs)"));
    }

    #[test]
    fn test_struct_def_with_defs() {
        let ast = parse("(struct_def (fields (x word)) (defs (new (func self word self))))");
        let output = pretty_print_ast(&ast);
        assert!(output.contains("(defs"));
        assert!(output.contains("(new (func self word self))"));
    }

    #[test]
    fn test_struct_init() {
        assert_eq!(
            pretty_print_ast(&parse("(struct_init Point (x 10) (y 20))")),
            "(struct_init Point (x 10) (y 20))"
        );
    }

    #[test]
    fn test_struct_init_empty() {
        assert_eq!(
            pretty_print_ast(&parse("(struct_init EmptyStruct)")),
            "(struct_init EmptyStruct)"
        );
    }

    #[test]
    fn test_display_trait() {
        let ast = parse("(if true 1 2)");
        assert_eq!(format!("{}", ast), "(if true 1 2)");
        assert_eq!(format!("{}", ast.runtime_main), "(if true 1 2)");
    }
}
