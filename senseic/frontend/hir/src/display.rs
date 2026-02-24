use crate::{BlockId, ConstId, Expr, FnDefId, Hir, Instruction, StructDefId};
use sensei_parser::PlankInterner;
use std::fmt::{self, Display, Formatter};

pub struct DisplayHir<'hir, 'interner> {
    hir: &'hir Hir,
    interner: &'interner PlankInterner,
}

impl<'hir, 'interner> DisplayHir<'hir, 'interner> {
    pub fn new(hir: &'hir Hir, interner: &'interner PlankInterner) -> Self {
        Self { hir, interner }
    }

    fn fmt_expr(&self, f: &mut Formatter<'_>, expr: Expr) -> fmt::Result {
        match expr {
            Expr::ConstRef(id) => write!(f, "ConstRef({id:?})"),
            Expr::LocalRef(id) => write!(f, "LocalRef({id:?})"),
            Expr::FnDef(id) => write!(f, "FnDef({id:?})"),
            Expr::Bool(b) => write!(f, "Bool({b})"),
            Expr::Void => write!(f, "Void"),
            Expr::BigNum(id) => {
                let value = &self.hir.big_nums[id];
                write!(f, "BigNum({value})")
            }
            Expr::Type(id) => write!(f, "Type({id:?})"),
            Expr::Call { callee, args } => {
                let arg_locals = &self.hir.call_params[args];
                write!(f, "Call {{ callee: {callee:?}, args: {arg_locals:?} }}")
            }
            Expr::Member { object, member } => {
                let name = &self.interner[member];
                write!(f, "Member {{ object: {object:?}, member: {name:?} }}")
            }
            Expr::StructLit { ty, fields } => {
                write!(f, "StructLit {{ ty: {ty:?}, fields: [")?;
                for (i, field) in self.hir.fields[fields].iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    let name = &self.interner[field.name];
                    write!(f, "{name:?}: {:?}", field.value)?;
                }
                write!(f, "] }}")
            }
            Expr::StructDef(id) => write!(f, "StructDef({id:?})"),
        }
    }

    fn fmt_instr(&self, f: &mut Formatter<'_>, instr: Instruction, indent: usize) -> fmt::Result {
        let indent_str = "    ".repeat(indent);
        match instr {
            Instruction::Set { local, expr } => {
                write!(f, "{indent_str}Set {{ local: {local:?}, expr: ")?;
                self.fmt_expr(f, expr)?;
                writeln!(f, " }}")
            }
            Instruction::Assign { target, value } => {
                write!(f, "{indent_str}Assign {{ target: {target:?}, value: ")?;
                self.fmt_expr(f, value)?;
                writeln!(f, " }}")
            }
            Instruction::AssertType { value, of_type } => {
                writeln!(f, "{indent_str}AssertType {{ value: {value:?}, of_type: {of_type:?} }}")
            }
            Instruction::Eval(expr) => {
                write!(f, "{indent_str}Eval(")?;
                self.fmt_expr(f, expr)?;
                writeln!(f, ")")
            }
            Instruction::Return(expr) => {
                write!(f, "{indent_str}Return(")?;
                self.fmt_expr(f, expr)?;
                writeln!(f, ")")
            }
            Instruction::If { condition, then_block, else_block } => {
                writeln!(f, "{indent_str}If {{ condition: {condition:?} }}")?;
                writeln!(f, "{indent_str}  then:")?;
                self.fmt_block(f, then_block, indent + 2)?;
                writeln!(f, "{indent_str}  else:")?;
                self.fmt_block(f, else_block, indent + 2)
            }
            Instruction::While { condition_block, body } => {
                writeln!(f, "{indent_str}While {{")?;
                writeln!(f, "{indent_str}  condition:")?;
                self.fmt_block(f, condition_block, indent + 2)?;
                writeln!(f, "{indent_str}  body:")?;
                self.fmt_block(f, body, indent + 2)?;
                writeln!(f, "{indent_str}}}")
            }
        }
    }

    fn fmt_block(&self, f: &mut Formatter<'_>, block_id: BlockId, indent: usize) -> fmt::Result {
        let instructions = &self.hir.blocks[block_id];
        for &instr in instructions {
            self.fmt_instr(f, instr, indent)?;
        }
        Ok(())
    }

    fn fmt_const(&self, f: &mut Formatter<'_>, const_id: ConstId) -> fmt::Result {
        let const_name = self
            .hir
            .consts
            .const_name_to_id
            .iter()
            .find_map(|(&name, &id)| (id == const_id).then(|| &self.interner[name]))
            .expect("missing name map for const ID");

        let const_def = &self.hir.consts.const_defs[const_id];
        writeln!(f, "{const_id:?} ({const_name:?}) result={:?} {{", const_def.result)?;
        self.fmt_block(f, const_def.body, 1)?;
        writeln!(f, "}}")
    }

    fn fmt_fn_def(&self, f: &mut Formatter<'_>, fn_def_id: FnDefId) -> fmt::Result {
        let fn_def = &self.hir.fns[fn_def_id];
        let params = &self.hir.fn_params[fn_def_id];
        let captures = &self.hir.fn_captures[fn_def_id];

        writeln!(f, "{fn_def_id:?} {{")?;

        write!(f, "    params: [")?;
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            let comptime_str = if param.comptime { "comptime " } else { "" };
            write!(f, "{comptime_str}{:?}", param.local)?;
        }
        writeln!(f, "]")?;

        if !captures.is_empty() {
            write!(f, "    captures: [")?;
            for (i, capture) in captures.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{:?} -> {:?}", capture.outer_local, capture.inner_local)?;
            }
            writeln!(f, "]")?;
        }

        writeln!(f, "    body:")?;
        self.fmt_block(f, fn_def.body, 2)?;
        writeln!(f, "}}")
    }

    fn fmt_struct_def(&self, f: &mut Formatter<'_>, struct_def_id: StructDefId) -> fmt::Result {
        let struct_def = &self.hir.struct_defs[struct_def_id];
        let fields = &self.hir.fields[struct_def.fields];

        writeln!(f, "{struct_def_id:?} {{")?;
        writeln!(f, "    type_index: {:?}", struct_def.type_index)?;
        write!(f, "    fields: [")?;
        for (i, field) in fields.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            let name = &self.interner[field.name];
            write!(f, "{name:?}: {:?}", field.value)?;
        }
        writeln!(f, "]")?;
        writeln!(f, "}}")
    }
}

impl Display for DisplayHir<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "==== Constants ====")?;
        for (&_, &const_id) in self.hir.consts.const_name_to_id.iter() {
            self.fmt_const(f, const_id)?;
        }

        if !self.hir.fns.is_empty() {
            writeln!(f, "\n==== Function Definitions ====")?;
            for (fn_def_id, _) in self.hir.fns.enumerate_idx() {
                self.fmt_fn_def(f, fn_def_id)?;
            }
        }

        if !self.hir.struct_defs.is_empty() {
            writeln!(f, "\n==== Struct Definitions ====")?;
            for (struct_def_id, _) in self.hir.struct_defs.enumerate_idx() {
                self.fmt_struct_def(f, struct_def_id)?;
            }
        }

        writeln!(f, "\n==== Const Deps ====")?;
        for (const_id, deps) in self.hir.const_deps.enumerate_idx() {
            writeln!(f, "{const_id:?} -> {deps:?}")?;
        }

        writeln!(f, "\n==== Init ====")?;
        self.fmt_block(f, self.hir.init, 1)?;

        if let Some(run_block) = self.hir.run {
            writeln!(f, "\n==== Run ====")?;
            self.fmt_block(f, run_block, 1)?;
        }

        Ok(())
    }
}
