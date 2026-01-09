use allocator_api2::vec::Vec;
use bumpalo::Bump;

use crate::{
    ast::*,
    diagnostics::DiagnosticsContext,
    lexer::{Lexer, SourceSpan, Token},
};
use neosen_data::{Span, bigint::FrozenBigUint};

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

    pub fn skip_until(&mut self, stop_tokens: &[Token]) -> Recovered {
        while !self.at_eof() {
            if let Some(tok) = self.token
                && stop_tokens.contains(&tok)
            {
                return Recovered::Yes;
            }
            self.bump();
        }
        Recovered::Yes
    }

    pub fn skip_until_before(&mut self, stop_tokens: &[Token]) -> Recovered {
        while !self.at_eof() {
            if let Some(tok) = self.token
                && stop_tokens.contains(&tok)
            {
                return Recovered::Yes;
            }
            self.bump();
        }
        Recovered::Yes
    }

    pub fn recover_closing_delimiter(
        &mut self,
        close: Token,
        open_span: SourceSpan,
    ) -> Result<Recovered, ParseError> {
        if self.eat(close) {
            return Ok(Recovered::No);
        }

        if self.at_eof() {
            let msg = format!("unclosed delimiter: expected {}", token_description(close));
            self.diagnostics.report_with_span_note(
                self.token_span,
                &msg,
                open_span,
                "opening delimiter here",
            );
            return Ok(Recovered::Yes);
        }

        self.expected_one_of_not_found(&[close])
    }

    pub fn is_at_recovery_point(&self) -> bool {
        matches!(
            self.token,
            Some(
                Token::RightCurly
                    | Token::RightRound
                    | Token::RightSquare
                    | Token::Semicolon
                    | Token::Comma
            )
        ) || self.at_eof()
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

    pub fn parse_bool_literal(&mut self) -> Result<Spanned<bool>, ParseError> {
        let value = if self.check_noexpect(Token::True) {
            true
        } else if self.check_noexpect(Token::False) {
            false
        } else {
            self.push_expected(ExpectedToken::Literal);
            self.expected_one_of_not_found(&[])?;
            unreachable!()
        };
        let span = self.token_span;
        self.bump();
        Ok(Spanned::new(span, value))
    }

    pub fn parse_int_literal(&mut self) -> Result<Spanned<IntLiteral<'ast>>, ParseError> {
        let span = self.token_span;
        let text = self.current_slice();

        let (positive, num) = if self.check_noexpect(Token::DecLiteral) {
            let (positive, digits) = strip_sign(text);
            let num = FrozenBigUint::from_radix10_in(digits, self.arena);
            (positive, num)
        } else if self.check_noexpect(Token::HexLiteral) {
            let (positive, digits) = strip_sign(text);
            let digits = &digits[2..]; // strip "0x"
            let num = FrozenBigUint::from_radix16_in(digits, self.arena);
            (positive, num)
        } else if self.check_noexpect(Token::BinLiteral) {
            let (positive, digits) = strip_sign(text);
            let digits = &digits[2..]; // strip "0b"
            let num = FrozenBigUint::from_radix2_in(digits, self.arena);
            (positive, num)
        } else {
            self.push_expected(ExpectedToken::Literal);
            self.expected_one_of_not_found(&[])?;
            unreachable!()
        };

        self.bump();
        Ok(Spanned::new(span, IntLiteral { positive, num }))
    }

    pub fn parse_name_path(&mut self) -> Result<NamePath<'ast>, ParseError> {
        let mut segments = std::vec::Vec::new();

        let first = self.parse_ident()?;
        segments.push(first.inner);

        while self.eat(Token::Dot) {
            let segment = self.parse_ident()?;
            segments.push(segment.inner);
        }

        let path = self.arena.alloc_slice_copy(&segments);
        Ok(NamePath(path))
    }

    pub fn parse_primary_expr(&mut self) -> Result<Expr<'ast>, ParseError> {
        if self.check_noexpect(Token::Identifier) {
            let ident = self.parse_ident()?;
            Ok(Expr::Ident(ident.inner))
        } else if self.check_noexpect(Token::True) || self.check_noexpect(Token::False) {
            let bool_lit = self.parse_bool_literal()?;
            Ok(Expr::BoolLiteral(bool_lit.inner))
        } else if self.check_noexpect(Token::DecLiteral)
            || self.check_noexpect(Token::HexLiteral)
            || self.check_noexpect(Token::BinLiteral)
        {
            let int_lit = self.parse_int_literal()?;
            Ok(Expr::IntLiteral(int_lit.inner))
        } else {
            self.push_expected(ExpectedToken::Expr);
            self.expected_one_of_not_found(&[])?;
            unreachable!()
        }
    }

    pub fn parse_member_expr(&mut self) -> Result<Expr<'ast>, ParseError> {
        let mut expr = self.parse_primary_expr()?;

        while self.eat(Token::Dot) {
            let ident = self.parse_ident()?;
            let member = Member { expr: self.arena.alloc(expr), ident: ident.inner };
            expr = Expr::Member(member);
        }

        Ok(expr)
    }
}

fn strip_sign(s: &str) -> (bool, &str) {
    if let Some(rest) = s.strip_prefix('-') { (false, rest) } else { (true, s) }
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

    #[test]
    fn test_parse_ident_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let ident = parser.parse_ident().unwrap();
        assert_eq!(ident.span, Span::new(0, 3));
        assert_eq!(parser.interner.resolve(ident.inner), "foo");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_ident_advances_token() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo bar", &arena);

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
        let mut parser = Parser::new("if", &arena);

        let result = parser.parse_ident();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_ident_fails_on_literal() {
        let arena = Bump::new();
        let mut parser = Parser::new("123", &arena);

        let result = parser.parse_ident();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_bool_literal_true() {
        let arena = Bump::new();
        let mut parser = Parser::new("true", &arena);

        let result = parser.parse_bool_literal().unwrap();
        assert!(result.inner);
        assert_eq!(result.span, Span::new(0, 4));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_bool_literal_false() {
        let arena = Bump::new();
        let mut parser = Parser::new("false", &arena);

        let result = parser.parse_bool_literal().unwrap();
        assert!(!result.inner);
        assert_eq!(result.span, Span::new(0, 5));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_bool_literal_fails_on_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("truthy", &arena);

        let result = parser.parse_bool_literal();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_bool_literal_advances() {
        let arena = Bump::new();
        let mut parser = Parser::new("true false", &arena);

        let first = parser.parse_bool_literal().unwrap();
        assert!(first.inner);

        let second = parser.parse_bool_literal().unwrap();
        assert!(!second.inner);
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_int_literal_decimal() {
        let arena = Bump::new();
        let mut parser = Parser::new("12345", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "3039");
        assert_eq!(result.span, Span::new(0, 5));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_int_literal_decimal_negative() {
        let arena = Bump::new();
        let mut parser = Parser::new("-42", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(!result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "2a");
        assert_eq!(result.span, Span::new(0, 3));
    }

    #[test]
    fn test_parse_int_literal_decimal_with_underscores() {
        let arena = Bump::new();
        let mut parser = Parser::new("1_000_000", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "f4240");
    }

    #[test]
    fn test_parse_int_literal_hex() {
        let arena = Bump::new();
        let mut parser = Parser::new("0xDEAD", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "dead");
        assert_eq!(result.span, Span::new(0, 6));
    }

    #[test]
    fn test_parse_int_literal_hex_negative() {
        let arena = Bump::new();
        let mut parser = Parser::new("-0xBEEF", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(!result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "beef");
    }

    #[test]
    fn test_parse_int_literal_binary() {
        let arena = Bump::new();
        let mut parser = Parser::new("0b1010", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "a");
        assert_eq!(result.span, Span::new(0, 6));
    }

    #[test]
    fn test_parse_int_literal_binary_negative() {
        let arena = Bump::new();
        let mut parser = Parser::new("-0b1111", &arena);

        let result = parser.parse_int_literal().unwrap();
        assert!(!result.inner.positive);
        assert_eq!(format!("{:x}", result.inner.num), "f");
    }

    #[test]
    fn test_parse_int_literal_fails_on_identifier() {
        let arena = Bump::new();
        let mut parser = Parser::new("abc", &arena);

        let result = parser.parse_int_literal();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_name_path_single() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let result = parser.parse_name_path().unwrap();
        assert_eq!(result.0.len(), 1);
        assert_eq!(parser.interner.resolve(result.0[0]), "foo");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_name_path_two_segments() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar", &arena);

        let result = parser.parse_name_path().unwrap();
        assert_eq!(result.0.len(), 2);
        assert_eq!(parser.interner.resolve(result.0[0]), "foo");
        assert_eq!(parser.interner.resolve(result.0[1]), "bar");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_name_path_three_segments() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar.baz", &arena);

        let result = parser.parse_name_path().unwrap();
        assert_eq!(result.0.len(), 3);
        assert_eq!(parser.interner.resolve(result.0[0]), "foo");
        assert_eq!(parser.interner.resolve(result.0[1]), "bar");
        assert_eq!(parser.interner.resolve(result.0[2]), "baz");
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_name_path_stops_at_non_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar + baz", &arena);

        let result = parser.parse_name_path().unwrap();
        assert_eq!(result.0.len(), 2);
        assert_eq!(parser.interner.resolve(result.0[0]), "foo");
        assert_eq!(parser.interner.resolve(result.0[1]), "bar");
        assert_eq!(parser.token, Some(Token::Plus));
    }

    #[test]
    fn test_parse_name_path_fails_on_non_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("123", &arena);

        let result = parser.parse_name_path();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_name_path_trailing_dot_with_following_token() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar.+", &arena);

        let result = parser.parse_name_path();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_primary_expr_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result, Expr::Ident(_)));
        if let Expr::Ident(istr) = result {
            assert_eq!(parser.interner.resolve(istr), "foo");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_bool_true() {
        let arena = Bump::new();
        let mut parser = Parser::new("true", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result, Expr::BoolLiteral(true)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_bool_false() {
        let arena = Bump::new();
        let mut parser = Parser::new("false", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result, Expr::BoolLiteral(false)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_int_decimal() {
        let arena = Bump::new();
        let mut parser = Parser::new("42", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result, Expr::IntLiteral(_)));
        if let Expr::IntLiteral(lit) = result {
            assert!(lit.positive);
            assert_eq!(format!("{:x}", lit.num), "2a");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_int_hex() {
        let arena = Bump::new();
        let mut parser = Parser::new("0xDEAD", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result, Expr::IntLiteral(_)));
        if let Expr::IntLiteral(lit) = result {
            assert!(lit.positive);
            assert_eq!(format!("{:x}", lit.num), "dead");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_int_binary() {
        let arena = Bump::new();
        let mut parser = Parser::new("0b1010", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result, Expr::IntLiteral(_)));
        if let Expr::IntLiteral(lit) = result {
            assert!(lit.positive);
            assert_eq!(format!("{:x}", lit.num), "a");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_negative_int() {
        let arena = Bump::new();
        let mut parser = Parser::new("-123", &arena);

        let result = parser.parse_primary_expr().unwrap();
        assert!(matches!(result, Expr::IntLiteral(_)));
        if let Expr::IntLiteral(lit) = result {
            assert!(!lit.positive);
            assert_eq!(format!("{:x}", lit.num), "7b");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_primary_expr_fails_on_keyword() {
        let arena = Bump::new();
        let mut parser = Parser::new("if", &arena);

        let result = parser.parse_primary_expr();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_primary_expr_fails_on_operator() {
        let arena = Bump::new();
        let mut parser = Parser::new("+", &arena);

        let result = parser.parse_primary_expr();
        assert!(result.is_err());
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parse_member_simple() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar", &arena);

        let result = parser.parse_member_expr().unwrap();
        assert!(matches!(result, Expr::Member(_)));
        if let Expr::Member(member) = result {
            assert!(matches!(*member.expr, Expr::Ident(_)));
            assert_eq!(parser.interner.resolve(member.ident), "bar");
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_member_chained() {
        let arena = Bump::new();
        let mut parser = Parser::new("a.b.c", &arena);

        let result = parser.parse_member_expr().unwrap();
        // Should be ((a.b).c)
        assert!(matches!(result, Expr::Member(_)));
        if let Expr::Member(outer) = result {
            assert_eq!(parser.interner.resolve(outer.ident), "c");
            assert!(matches!(*outer.expr, Expr::Member(_)));
            if let Expr::Member(ref inner) = *outer.expr {
                assert_eq!(parser.interner.resolve(inner.ident), "b");
                assert!(matches!(*inner.expr, Expr::Ident(_)));
            }
        }
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_member_no_member_access() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo", &arena);

        let result = parser.parse_member_expr().unwrap();
        assert!(matches!(result, Expr::Ident(_)));
        assert!(parser.at_eof());
    }

    #[test]
    fn test_parse_member_stops_at_non_ident() {
        let arena = Bump::new();
        let mut parser = Parser::new("foo.bar + baz", &arena);

        let result = parser.parse_member_expr().unwrap();
        assert!(matches!(result, Expr::Member(_)));
        assert_eq!(parser.token, Some(Token::Plus));
    }
}
