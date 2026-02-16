use crate::{cst::*, lexer::Lexed};
use sensei_core::{Idx, newtype_index};

impl<'cst> Ast<'cst> {
    pub fn new(cst: &'cst ConcreteSyntaxTree) -> Self {
        Self { cst }
    }
}

pub struct Ast<'cst> {
    cst: &'cst ConcreteSyntaxTree,
}
