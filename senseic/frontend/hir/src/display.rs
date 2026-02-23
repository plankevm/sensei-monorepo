use crate::{BlockId, ConstId, Hir};
use sensei_parser::{StrId, StringInterner};
use std::fmt::{self, Display, Formatter};

pub struct DisplayHir<'hir, 'interner> {
    hir: &'hir Hir,
    interner: &'interner StringInterner<StrId>,
}

impl<'hir, 'interner> DisplayHir<'hir, 'interner> {
    pub fn new(hir: &'hir Hir, interner: &'interner StringInterner<StrId>) -> Self {
        Self { hir, interner }
    }

    fn fmt_block(&self, f: &mut Formatter<'_>, block_id: BlockId, indent: usize) -> fmt::Result {
        let indent_str = "    ".repeat(indent);
        let instructions = &self.hir.blocks[block_id];
        for instr in instructions {
            writeln!(f, "{indent_str}{instr:?}")?;
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
        writeln!(f, "{const_id:?} ({const_name:?}) -> [")?;
        self.fmt_block(f, const_def.body, 1)?;
        writeln!(f, "]")
    }
}

impl Display for DisplayHir<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "==== Constants ====")?;
        for (&_, &const_id) in self.hir.consts.const_name_to_id.iter() {
            self.fmt_const(f, const_id)?;
        }

        writeln!(f, "==== Init ====")?;
        self.fmt_block(f, self.hir.init, 1)?;

        if let Some(run_block) = self.hir.run {
            writeln!(f, "==== Run ====")?;
            self.fmt_block(f, run_block, 1)?;
        }

        Ok(())
    }
}
