use crate::{ConstId, Hir, Instruction};
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

    fn fmt_instructions(&self, f: &mut Formatter<'_>, instructions: &[Instruction]) -> fmt::Result {
        for i in instructions {
            writeln!(f, "    {i:?}")?;
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
        self.fmt_instructions(f, &const_def.instructions)?;
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
        self.fmt_instructions(f, &self.hir.init)?;

        if let Some(run_instructions) = self.hir.run.as_ref() {
            writeln!(f, "==== Run ====")?;
            self.fmt_instructions(f, run_instructions)?;
        }

        Ok(())
    }
}
