use allocator_api2::vec::Vec;
use bumpalo::Bump;

use crate::{
    ast::*,
    diagnostics::DiagnosticsContext,
    lexer::{Lexer, SourceSpan, Token},
};
use neosen_data::Span;

#[derive(Debug, Clone)]
pub struct ParseError;

fn estimate_declaration_count(source: &str) -> usize {
    const AVG_DECLARATIONS_PER_SRC_BYTES: usize = 30;
    source.len().div_ceil(AVG_DECLARATIONS_PER_SRC_BYTES)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Recovered {
    No,
    Yes,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedToken {
    Token(Token),
    Ident,
    Literal,
    Expr,
}

impl std::fmt::Display for ExpectedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpectedToken::Token(tok) => write!(f, "{}", token_description(*tok)),
            ExpectedToken::Ident => write!(f, "identifier"),
            ExpectedToken::Literal => write!(f, "literal"),
            ExpectedToken::Expr => write!(f, "expression"),
        }
    }
}

fn token_description(token: Token) -> &'static str {
    match token {
        Token::Semicolon => "`;`",
        Token::Comma => "`,`",
        Token::Colon => "`:`",
        Token::Dot => "`.`",
        Token::LeftCurly => "`{`",
        Token::RightCurly => "`}`",
        Token::LeftRound => "`(`",
        Token::RightRound => "`)`",
        Token::LeftSquare => "`[`",
        Token::RightSquare => "`]`",
        Token::ThinArrow => "`->`",
        Token::Equals => "`=`",
        Token::Plus => "`+`",
        Token::PlusPercent => "`+%`",
        Token::Minus => "`-`",
        Token::MinusPercent => "`-%`",
        Token::Star => "`*`",
        Token::StarPercent => "`*%`",
        Token::Slash => "`/`",
        Token::SlashPlus => "`/+`",
        Token::SlashNeg => "`/-`",
        Token::SlashLess => "`/<`",
        Token::SlashGreater => "`/>`",
        Token::Percent => "`%`",
        Token::DoubleEquals => "`==`",
        Token::NotEquals => "`!=`",
        Token::LessThan => "`<`",
        Token::GreaterThan => "`>`",
        Token::LessEquals => "`<=`",
        Token::GreaterEquals => "`>=`",
        Token::And => "`&&`",
        Token::Or => "`||`",
        Token::Not => "`!`",
        Token::Ampersand => "`&`",
        Token::Pipe => "`|`",
        Token::Caret => "`^`",
        Token::Tilde => "`~`",
        Token::ShiftLeft => "`<<`",
        Token::ShiftRight => "`>>`",
        Token::If => "`if`",
        Token::Else => "`else`",
        Token::Fn => "`fn`",
        Token::Let => "`let`",
        Token::Mut => "`mut`",
        Token::Const => "`const`",
        Token::Init => "`init`",
        Token::Run => "`run`",
        Token::Struct => "`struct`",
        Token::Return => "`return`",
        Token::Comptime => "`comptime`",
        Token::Inline => "`inline`",
        Token::While => "`while`",
        Token::True => "`true`",
        Token::False => "`false`",
        Token::Identifier => "identifier",
        Token::DecLiteral => "decimal literal",
        Token::HexLiteral => "hex literal",
        Token::BinLiteral => "binary literal",
        Token::Error => "error",
    }
}

const EOF_SPAN: SourceSpan = Span { start: u32::MAX, end: u32::MAX };

pub struct Parser<'src, 'ast> {
    #[allow(dead_code)]
    arena: &'ast Bump,
    source: &'src str,
    interner: StringInterner,
    diagnostics: DiagnosticsContext<'ast>,

    token: Option<Token>,
    token_span: SourceSpan,
    prev_token: Option<Token>,
    prev_span: SourceSpan,

    expected_tokens: std::vec::Vec<ExpectedToken>,
    tokens: std::iter::Peekable<Lexer<'src>>,
}

impl<'src, 'ast> Parser<'src, 'ast> {
    pub fn new(source: &'src str, arena: &'ast Bump) -> Self {
        let mut lexer = Lexer::new(source).peekable();
        let (token, token_span) = lexer.next().map_or((None, EOF_SPAN), |(t, s)| (Some(t), s));

        Self {
            arena,
            source,
            interner: StringInterner::with_hasher(std::hash::RandomState::new()),
            diagnostics: DiagnosticsContext::new(arena),
            token,
            token_span,
            prev_token: None,
            prev_span: Span::new(0, 0),
            expected_tokens: std::vec::Vec::new(),
            tokens: lexer,
        }
    }

    pub fn bump(&mut self) {
        self.prev_token = self.token;
        self.prev_span = self.token_span;

        let (next_token, next_span) =
            self.tokens.next().map_or((None, EOF_SPAN), |(t, s)| (Some(t), s));
        self.token = next_token;
        self.token_span = next_span;

        self.expected_tokens.clear();
    }

    pub fn check_noexpect(&self, tok: Token) -> bool {
        self.token == Some(tok)
    }

    pub fn check(&mut self, tok: Token) -> bool {
        let is_present = self.check_noexpect(tok);
        if !is_present {
            self.push_expected(ExpectedToken::Token(tok));
        }
        is_present
    }

    pub fn eat(&mut self, tok: Token) -> bool {
        let is_present = self.check(tok);
        if is_present {
            self.bump();
        }
        is_present
    }

    pub fn expect(&mut self, tok: Token) -> Result<Recovered, ParseError> {
        if self.check_noexpect(tok) {
            self.bump();
            Ok(Recovered::No)
        } else {
            self.expected_one_of_not_found(&[tok])
        }
    }

    fn push_expected(&mut self, expected: ExpectedToken) {
        if !self.expected_tokens.contains(&expected) {
            self.expected_tokens.push(expected);
        }
    }

    fn expected_one_of_not_found(&mut self, expected: &[Token]) -> Result<Recovered, ParseError> {
        let mut all_expected: std::vec::Vec<ExpectedToken> = expected
            .iter()
            .map(|t| ExpectedToken::Token(*t))
            .chain(self.expected_tokens.iter().cloned())
            .collect();

        all_expected.sort_by_key(|a| a.to_string());
        all_expected.dedup();

        let expected_str = format_expected_list(&all_expected);
        let found_str = self.token.map(token_description).unwrap_or("end of file");

        let msg = format!("expected {}, found {}", expected_str, found_str);
        self.diagnostics.report(self.token_span, msg);

        if self.token.is_none() { Ok(Recovered::Yes) } else { Err(ParseError) }
    }

    pub fn at_eof(&self) -> bool {
        self.token.is_none()
    }

    pub fn current_span(&self) -> SourceSpan {
        self.token_span
    }

    pub fn prev_span(&self) -> SourceSpan {
        self.prev_span
    }

    pub fn intern(&mut self, s: &str) -> IStr {
        self.interner.intern(s)
    }

    pub fn slice(&self, span: SourceSpan) -> &'src str {
        &self.source[span.start as usize..span.end as usize]
    }

    pub fn current_slice(&self) -> &'src str {
        self.slice(self.token_span)
    }

    pub fn diagnostics(&self) -> &DiagnosticsContext<'ast> {
        &self.diagnostics
    }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.has_errors()
    }

    fn parse_next_decl(&mut self) -> Result<Option<Declaration<'ast>>, ParseError> {
        if self.at_eof() {
            return Ok(None);
        }

        todo!()
    }

    pub fn parse_ident(&mut self) -> Result<Ident, ParseError> {
        if self.check_noexpect(Token::Identifier) {
            let span = self.token_span;
            let text = self.current_slice();
            let istr = self.intern(text);
            self.bump();
            Ok(Ident::new(span, istr))
        } else {
            self.push_expected(ExpectedToken::Ident);
            self.expected_one_of_not_found(&[])?;
            unreachable!()
        }
    }
}

fn format_expected_list(expected: &[ExpectedToken]) -> String {
    match expected.len() {
        0 => "nothing".to_string(),
        1 => expected[0].to_string(),
        2 => format!("{} or {}", expected[0], expected[1]),
        _ => {
            let (last, rest) = expected.split_last().unwrap();
            let rest_str: std::vec::Vec<_> = rest.iter().map(|e| e.to_string()).collect();
            format!("{}, or {}", rest_str.join(", "), last)
        }
    }
}

pub fn parse<'ast, 'src: 'ast>(
    source: &'src str,
    arena: &'ast Bump,
) -> Result<Ast<'ast>, ParseError> {
    let mut declarations = Vec::with_capacity_in(estimate_declaration_count(source), arena);

    let mut parser = Parser::new(source, arena);

    while let Some(decl) = parser.parse_next_decl()? {
        declarations.push(decl);
    }

    Ok(Ast { declarations })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn new_parser<'src, 'ast>(source: &'src str, arena: &'ast Bump) -> Parser<'src, 'ast> {
        Parser::new(source, arena)
    }

    #[test]
    fn test_bump_advances_token() {
        let arena = Bump::new();
        let mut parser = new_parser("foo bar baz", &arena);

        assert_eq!(parser.token, Some(Token::Identifier));
        assert_eq!(parser.current_slice(), "foo");

        parser.bump();
        assert_eq!(parser.token, Some(Token::Identifier));
        assert_eq!(parser.current_slice(), "bar");
        assert_eq!(parser.prev_token, Some(Token::Identifier));

        parser.bump();
        assert_eq!(parser.token, Some(Token::Identifier));
        assert_eq!(parser.current_slice(), "baz");

        parser.bump();
        assert!(parser.at_eof());
    }

    #[test]
    fn test_check_noexpect_does_not_accumulate() {
        let arena = Bump::new();
        let parser = new_parser("foo", &arena);

        assert!(!parser.check_noexpect(Token::If));
        assert!(parser.expected_tokens.is_empty());

        assert!(parser.check_noexpect(Token::Identifier));
        assert!(parser.expected_tokens.is_empty());
    }

    #[test]
    fn test_check_accumulates_expectations() {
        let arena = Bump::new();
        let mut parser = new_parser("foo", &arena);

        assert!(!parser.check(Token::If));
        assert_eq!(parser.expected_tokens.len(), 1);

        assert!(!parser.check(Token::Else));
        assert_eq!(parser.expected_tokens.len(), 2);

        assert!(!parser.check(Token::If));
        assert_eq!(parser.expected_tokens.len(), 2);

        assert!(parser.check(Token::Identifier));
        assert_eq!(parser.expected_tokens.len(), 2);
    }

    #[test]
    fn test_eat_consumes_matching_token() {
        let arena = Bump::new();
        let mut parser = new_parser("if else", &arena);

        assert!(!parser.eat(Token::Else));
        assert_eq!(parser.token, Some(Token::If));

        assert!(parser.eat(Token::If));
        assert_eq!(parser.token, Some(Token::Else));
        assert_eq!(parser.prev_token, Some(Token::If));
    }

    #[test]
    fn test_expect_success() {
        let arena = Bump::new();
        let mut parser = new_parser("if else", &arena);

        let result = parser.expect(Token::If);
        assert!(matches!(result, Ok(Recovered::No)));
        assert_eq!(parser.token, Some(Token::Else));
    }

    #[test]
    fn test_expect_failure_reports_error() {
        let arena = Bump::new();
        let mut parser = new_parser("if else", &arena);

        let result = parser.expect(Token::Else);
        assert!(result.is_err());
        assert!(parser.has_errors());
        assert_eq!(parser.diagnostics().error_count(), 1);
    }

    #[test]
    fn test_expect_at_eof_recovers() {
        let arena = Bump::new();
        let mut parser = new_parser("", &arena);

        let result = parser.expect(Token::If);
        assert!(matches!(result, Ok(Recovered::Yes)));
        assert!(parser.has_errors());
    }

    #[test]
    fn test_bump_clears_expectations() {
        let arena = Bump::new();
        let mut parser = new_parser("foo bar", &arena);

        parser.check(Token::If);
        parser.check(Token::Else);
        assert_eq!(parser.expected_tokens.len(), 2);

        parser.bump();
        assert!(parser.expected_tokens.is_empty());
    }

    #[test]
    fn test_intern_strings() {
        let arena = Bump::new();
        let mut parser = new_parser("foo foo bar", &arena);

        let foo1 = parser.intern("foo");
        let foo2 = parser.intern("foo");
        let bar = parser.intern("bar");

        assert_eq!(foo1, foo2);
        assert_ne!(foo1, bar);
    }

    #[test]
    fn test_span_tracking() {
        let arena = Bump::new();
        let mut parser = new_parser("if else", &arena);

        assert_eq!(parser.current_span(), Span::new(0, 2));

        parser.bump();
        assert_eq!(parser.prev_span(), Span::new(0, 2));
        assert_eq!(parser.current_span(), Span::new(3, 7));
    }

    #[test]
    fn test_parse_ident_simple() {
        let arena = Bump::new();
        let mut parser = new_parser("foo", &arena);

        let ident = parser.parse_ident().unwrap();
        assert_eq!(ident.span, Span::new(0, 3));
        assert_eq!(parser.interner.resolve(ident.inner), "foo");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_ident_advances_token() {
        let arena = Bump::new();
        let mut parser = new_parser("foo bar", &arena);

        let ident1 = parser.parse_ident().unwrap();
        assert_eq!(parser.interner.resolve(ident1.inner), "foo");
        assert!(!parser.at_eof());

        let ident2 = parser.parse_ident().unwrap();
        assert_eq!(parser.interner.resolve(ident2.inner), "bar");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_ident_fails_on_keyword() {
        let arena = Bump::new();
        let mut parser = new_parser("if", &arena);

        let result = parser.parse_ident();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_ident_fails_on_literal() {
        let arena = Bump::new();
        let mut parser = new_parser("123", &arena);

        let result = parser.parse_ident();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }
}
