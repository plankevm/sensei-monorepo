use logos::{Lexer as LogosLexer, Logos, Skip};

use neosen_data::Span;
pub type SourceSpan = Span<u32>;

fn lex_skip_line_comment(lex: &mut LogosLexer<Token>) {
    let remainder = lex.remainder();
    let mut chars = remainder.char_indices().peekable();
    while chars.next_if(|&(_, c)| c != '\n').is_some() {}
    let bytes_skipped = chars.peek().map_or(remainder.len(), |&(pos, _)| pos);
    lex.bump(bytes_skipped);
}

fn lex_skip_block_comment(lex: &mut LogosLexer<Token>) -> Result<Skip, ()> {
    let remainder = lex.remainder();
    let mut chars = remainder.char_indices().peekable();
    let mut depth: u32 = 1;

    while depth > 0 {
        match chars.next() {
            Some((_, '*')) if chars.next_if(|&(_, nc)| nc == '/').is_some() => depth -= 1,
            Some((_, '/')) if chars.next_if(|&(_, nc)| nc == '*').is_some() => depth += 1,
            Some(_) => {}
            None => return Err(()),
        }
    }

    let bytes_skipped = chars.peek().map_or(remainder.len(), |&(pos, _)| pos);
    lex.bump(bytes_skipped);

    Ok(Skip)
}

fn lex_string_literal(lex: &mut LogosLexer<Token>) -> Result<(), ()> {
    let remainder = lex.remainder();
    let mut chars = remainder.char_indices();

    loop {
        match chars.next() {
            Some((_, '\\')) => {
                // Skip the escaped character
                if chars.next().is_none() {
                    return Err(());
                }
            }
            Some((pos, '"')) => {
                lex.bump(pos + 1);
                return Ok(());
            }
            Some(_) => {}
            None => return Err(()),
        }
    }
}

#[derive(Logos, Debug, Clone, PartialEq, Eq, Copy)]
#[logos(skip r"[ \t]+")]
#[logos(skip(r"//", lex_skip_line_comment))]
#[logos(skip(r"/\*", lex_skip_block_comment))]
pub enum Token {
    // Delimiters
    #[token(";")]
    Semicolon,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token(".")]
    Dot,
    #[token("{")]
    LeftCurly,
    #[token("}")]
    RightCurly,
    #[token("(")]
    LeftRound,
    #[token(")")]
    RightRound,
    #[token("[")]
    LeftSquare,
    #[token("]")]
    RightSquare,

    // Operators
    #[token("->")]
    ThinArrow,
    #[token("=")]
    Equals,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,

    // Comparison
    #[token("==")]
    DoubleEquals,
    #[token("!=")]
    NotEquals,
    #[token("<")]
    LessThan,
    #[token(">")]
    GreaterThan,
    #[token("<=")]
    LessEquals,
    #[token(">=")]
    GreaterEquals,

    // Logical
    #[token("&&")]
    And,
    #[token("||")]
    Or,
    #[token("!")]
    Not,

    // Bitwise
    #[token("&")]
    Ampersand,
    #[token("|")]
    Pipe,
    #[token("^")]
    Caret,
    #[token("~")]
    Tilde,
    #[token("<<")]
    ShiftLeft,
    #[token(">>")]
    ShiftRight,

    // Keywords
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("fn")]
    Fn,
    #[token("let")]
    Let,
    #[token("mut")]
    Mut,
    #[token("const")]
    Const,
    #[token("init")]
    Init,
    #[token("run")]
    Run,
    #[token("struct")]
    Struct,
    #[token("import")]
    Import,
    #[token("from")]
    From,
    #[token("as")]
    As,
    #[token("export")]
    Export,
    #[token("return")]
    Return,
    #[token("true")]
    True,
    #[token("false")]
    False,

    #[regex("[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier,

    #[regex("-?[0-9][0-9_]*")]
    DecLiteral,
    #[regex("-?0x[0-9A-Fa-f][0-9A-Fa-f_]*")]
    HexLiteral,
    #[regex("-?0b[01][01_]*")]
    BinLiteral,
    #[token("\"", lex_string_literal)]
    StringLiteral,

    Error,
}

#[derive(Debug, Clone)]
pub struct Lexer<'src>(LogosLexer<'src, Token>);

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str) -> Self {
        Self(Token::lexer(source))
    }
}

impl<'src> Iterator for Lexer<'src> {
    type Item = (Token, std::ops::Range<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        let tok = self.0.next()?.unwrap_or(Token::Error);
        Some((tok, self.0.span()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_all(source: &str) -> Vec<(Token, std::ops::Range<usize>)> {
        Lexer::new(source).collect()
    }

    fn lex_tokens(source: &str) -> Vec<Token> {
        Lexer::new(source).map(|(tok, _)| tok).collect()
    }

    #[test]
    fn test_delimiters() {
        let source = "; , : . { } ( ) [ ]";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![
                Token::Semicolon,
                Token::Comma,
                Token::Colon,
                Token::Dot,
                Token::LeftCurly,
                Token::RightCurly,
                Token::LeftRound,
                Token::RightRound,
                Token::LeftSquare,
                Token::RightSquare,
            ]
        );
    }

    #[test]
    fn test_operators() {
        let source = "-> = + - * / %";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![
                Token::ThinArrow,
                Token::Equals,
                Token::Plus,
                Token::Minus,
                Token::Star,
                Token::Slash,
                Token::Percent,
            ]
        );
    }

    #[test]
    fn test_comparisons() {
        let source = "== != < > <= >=";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![
                Token::DoubleEquals,
                Token::NotEquals,
                Token::LessThan,
                Token::GreaterThan,
                Token::LessEquals,
                Token::GreaterEquals,
            ]
        );
    }

    #[test]
    fn test_logical() {
        let source = "&& || !";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::And, Token::Or, Token::Not,]);
    }

    #[test]
    fn test_bitwise() {
        let source = "& | ^ ~ << >>";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![
                Token::Ampersand,
                Token::Pipe,
                Token::Caret,
                Token::Tilde,
                Token::ShiftLeft,
                Token::ShiftRight,
            ]
        );
    }

    #[test]
    fn test_keywords() {
        let source =
            "if else fn let mut const init run struct import from as export return true false";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![
                Token::If,
                Token::Else,
                Token::Fn,
                Token::Let,
                Token::Mut,
                Token::Const,
                Token::Init,
                Token::Run,
                Token::Struct,
                Token::Import,
                Token::From,
                Token::As,
                Token::Export,
                Token::Return,
                Token::True,
                Token::False,
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        let source = "foo Bar _underscore x1 var_2";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier,
                Token::Identifier,
                Token::Identifier,
                Token::Identifier,
                Token::Identifier,
            ]
        );
    }

    #[test]
    fn test_identifier_not_keyword() {
        let source = "ifx elsewhere fns letter mutable constant";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier,
                Token::Identifier,
                Token::Identifier,
                Token::Identifier,
                Token::Identifier,
                Token::Identifier,
            ]
        );
    }

    #[test]
    fn test_decimal_literals() {
        let source = "123 1_000 0 42";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![Token::DecLiteral, Token::DecLiteral, Token::DecLiteral, Token::DecLiteral,]
        );
    }

    #[test]
    fn test_negative_decimal_literals() {
        let source = "-42 -1_000";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::DecLiteral, Token::DecLiteral,]);
    }

    #[test]
    fn test_hex_literals() {
        let source = "0xFF 0x1A_BC 0xdead 0x0";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![Token::HexLiteral, Token::HexLiteral, Token::HexLiteral, Token::HexLiteral,]
        );
    }

    #[test]
    fn test_negative_hex_literals() {
        let source = "-0xDEAD -0xff";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::HexLiteral, Token::HexLiteral,]);
    }

    #[test]
    fn test_binary_literals() {
        let source = "0b101 0b1010_0011 0b0 0b1";
        let tokens = lex_tokens(source);
        assert_eq!(
            tokens,
            vec![Token::BinLiteral, Token::BinLiteral, Token::BinLiteral, Token::BinLiteral,]
        );
    }

    #[test]
    fn test_negative_binary_literals() {
        let source = "-0b11 -0b1010";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::BinLiteral, Token::BinLiteral,]);
    }

    // ==================== String Literals ====================

    #[test]
    fn test_string_literal_simple() {
        let source = r#""hello""#;
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::StringLiteral]);
    }

    #[test]
    fn test_string_literal_empty() {
        let source = r#""""#;
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::StringLiteral]);
    }

    #[test]
    fn test_string_literal_with_escapes() {
        let source = r#""line\nbreak" "quote\"here" "tab\there""#;
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::StringLiteral, Token::StringLiteral, Token::StringLiteral,]);
    }

    #[test]
    fn test_line_comment_skipped() {
        let source = "// this is a comment\nfoo";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Error, Token::Identifier]);
    }

    #[test]
    fn test_line_comment_at_eof() {
        let source = "foo // comment at end";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Identifier]);
    }

    #[test]
    fn test_block_comment_skipped() {
        let source = "/* comment */ foo";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Identifier]);
    }

    #[test]
    fn test_nested_block_comment() {
        let source = "/* outer /* inner */ outer */ bar";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Identifier]);
    }

    #[test]
    fn test_string_literal_utf8_2byte() {
        let source = r#""héllo""#;
        let results = lex_all(source);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, Token::StringLiteral);
        assert_eq!(&source[results[0].1.clone()], "\"héllo\"");
    }

    #[test]
    fn test_string_literal_utf8_3byte() {
        let source = r#""日本語""#;
        let results = lex_all(source);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, Token::StringLiteral);
        assert_eq!(&source[results[0].1.clone()], "\"日本語\"");
    }

    #[test]
    fn test_string_literal_utf8_4byte() {
        let source = r#""🦀""#;
        let results = lex_all(source);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, Token::StringLiteral);
        assert_eq!(&source[results[0].1.clone()], "\"🦀\"");
    }

    #[test]
    fn test_block_comment_utf8() {
        let source = "/* émoji 🎉 */ foo";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Identifier]);
    }

    #[test]
    fn test_block_comment_utf8_cjk() {
        let source = "/* 日本語 */ bar";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Identifier]);
    }

    #[test]
    fn test_line_comment_utf8() {
        let source = "// café ☕\nfoo";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Error, Token::Identifier]);
    }

    #[test]
    fn test_invalid_char_at() {
        let source = "@";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Error]);
    }

    #[test]
    fn test_invalid_char_hash() {
        let source = "#";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Error]);
    }

    #[test]
    fn test_invalid_char_in_context() {
        let source = "foo @ bar";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Identifier, Token::Error, Token::Identifier]);
    }

    #[test]
    fn test_unclosed_block_comment() {
        let source = "/* no end";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Error, Token::Identifier, Token::Identifier]);
    }

    #[test]
    fn test_unclosed_nested_block_comment() {
        let source = "/* outer /* inner */";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Error, Token::Identifier]);
    }

    #[test]
    fn test_unclosed_string_literal() {
        let source = r#""no end"#;
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Error, Token::Identifier, Token::Identifier]);
    }

    #[test]
    fn test_string_escape_at_eof() {
        let source = r#""escape\"#;
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::Error, Token::Identifier, Token::Error]);
    }

    #[test]
    fn test_malformed_binary_no_digits() {
        let source = "0b__";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::DecLiteral, Token::Identifier]);
    }

    #[test]
    fn test_malformed_binary_prefix_only() {
        let source = "0b";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::DecLiteral, Token::Identifier]);
    }

    #[test]
    fn test_malformed_hex_prefix_only() {
        let source = "0x";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::DecLiteral, Token::Identifier]);
    }

    #[test]
    fn test_malformed_hex_no_digits() {
        let source = "0x__";
        let tokens = lex_tokens(source);
        assert_eq!(tokens, vec![Token::DecLiteral, Token::Identifier]);
    }

    #[test]
    fn test_span_identifier() {
        let source = "  foo  bar  ";
        let results = lex_all(source);
        assert_eq!(results.len(), 2);
        assert_eq!(&source[results[0].1.clone()], "foo");
        assert_eq!(&source[results[1].1.clone()], "bar");
    }

    #[test]
    fn test_span_string_literal() {
        let source = r#"  "hello world"  "#;
        let results = lex_all(source);
        assert_eq!(results.len(), 1);
        assert_eq!(&source[results[0].1.clone()], "\"hello world\"");
    }

    #[test]
    fn test_span_numeric_literals() {
        let source = "  123  0xFF  0b101  ";
        let results = lex_all(source);
        assert_eq!(results.len(), 3);
        assert_eq!(&source[results[0].1.clone()], "123");
        assert_eq!(&source[results[1].1.clone()], "0xFF");
        assert_eq!(&source[results[2].1.clone()], "0b101");
    }

    #[test]
    fn test_span_multi_char_operators() {
        let source = "  ->  ==  <=  <<  ";
        let results = lex_all(source);
        assert_eq!(results.len(), 4);
        assert_eq!(&source[results[0].1.clone()], "->");
        assert_eq!(&source[results[1].1.clone()], "==");
        assert_eq!(&source[results[2].1.clone()], "<=");
        assert_eq!(&source[results[3].1.clone()], "<<");
    }

    #[test]
    fn test_span_utf8_string_byte_length() {
        let source = r#""日""#;
        let results = lex_all(source);
        assert_eq!(results.len(), 1);
        let span = &results[0].1;
        assert_eq!(span.end - span.start, 5);
    }
}
