use allocator_api2::vec::Vec;
use bumpalo::Bump;

use crate::{
    ast::*,
    lexer::{Lexer, Token},
};

#[derive(Debug, Clone)]
pub struct ParseError;

fn estimate_declaration_count(source: &str) -> usize {
    const AVG_DECLARATIONS_PER_SRC_BYTES: usize = 30;
    source.len().div_ceil(AVG_DECLARATIONS_PER_SRC_BYTES)
}

struct Parser<'src, 'ast> {
    arena: &'ast Bump,
    source: &'src str,
    tokens: std::iter::Peekable<Lexer<'src>>,
}

impl<'src, 'ast> Parser<'src, 'ast> {
    fn peek_token(&mut self) -> Option<Token> {
        self.tokens.peek().map(|(t, _)| *t)
    }

    #[allow(dead_code)]
    fn next_token(&mut self) -> Option<Token> {
        self.tokens.next().map(|(t, _)| t)
    }

    fn parse_import(&mut self) -> Result<Import<'ast>, ParseError> {
        Err(ParseError)
    }

    fn parse_next_decl(&mut self) -> Result<Option<Declaration<'ast>>, ParseError> {
        let _arena = &mut self.arena;
        let _source = &mut self.source;

        let Some(token) = self.peek_token() else { return Ok(None) };

        let d = match token {
            Token::Import => Declaration::Import(self.parse_import()?),
            _ => todo!(),
        };

        Ok(Some(d))
    }
}

pub fn parse<'ast, 'src: 'ast>(
    source: &'src str,
    arena: &'ast Bump,
) -> Result<Ast<'ast>, ParseError> {
    let mut declarations = Vec::with_capacity_in(estimate_declaration_count(source), arena);

    let mut parser = Parser { arena, source, tokens: Lexer::new(source).peekable() };

    while let Some(decl) = parser.parse_next_decl()? {
        declarations.push(decl);
    }

    Ok(Ast { declarations })
}
