use logos::{Lexer as LogosLexer, Logos};

fn lex_skip_line_comment(lex: &mut LogosLexer<Token>) {
    let remainder = lex.remainder();
    let mut chars = remainder.char_indices().peekable();
    while chars.next_if(|&(_, c)| c != '\n').is_some() {}
    let bytes_skipped = chars.peek().map_or(remainder.len(), |&(pos, _)| pos);
    lex.bump(bytes_skipped);
}

fn lex_skip_block_comment(lex: &mut LogosLexer<Token>) {
    let remainder = lex.remainder();
    let mut chars = remainder.char_indices().peekable();
    'block_comment: while let Some((_, c)) = chars.next() {
        if c == '*' && chars.next_if(|&(_, nc)| nc == '/').is_some() {
            break 'block_comment;
        }
    }
    let bytes_skipped = chars.peek().map_or(remainder.len(), |&(pos, _)| pos);
    lex.bump(bytes_skipped);
}

#[derive(Logos, Debug, Clone, PartialEq, Eq, Copy)]
#[logos(skip r"[ \t]+")]
#[logos(skip(r"//", lex_skip_line_comment))]
#[logos(skip(r"/\*", lex_skip_block_comment))]
pub enum Token {
    #[token(":")]
    Colon,
    #[token("\n")]
    Newline,
    #[token("->")]
    ThinArrow, // ->
    #[token("=>")]
    ThickArrow, // =>
    #[token("?")]
    Question,
    #[token("=")]
    Equals,
    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,

    #[token("data")]
    Data,
    #[token("fn")]
    Fn,
    #[token("switch")]
    Switch,
    #[token("default")]
    Default,
    #[token("iret")]
    InternalReturn,

    #[regex("[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier,
    #[regex("@[a-zA-Z_][a-zA-Z0-9_]*")]
    Label,
    #[regex("\\.[a-zA-Z_][a-zA-Z0-9_]*")]
    DataRef,

    #[regex("-?[0-9]+")]
    DecLiteral,
    #[regex("-?0x[0-9a-fA-F]+")]
    HexLiteral,

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

    #[test]
    fn test_basic_tokens() {
        let input = "fn data : -> => ? = _ { } @label .dataref 123 0xFF";
        let result = Token::lexer(input).collect::<Result<Vec<_>, _>>().unwrap();

        assert_eq!(result[0], Token::Fn);
        assert_eq!(result[1], Token::Data);
        assert_eq!(result[2], Token::Colon);
        assert_eq!(result[3], Token::ThinArrow);
        assert_eq!(result[4], Token::ThickArrow);
        assert_eq!(result[5], Token::Question);
        assert_eq!(result[6], Token::Equals);
        assert_eq!(result[7], Token::Identifier);
        assert_eq!(result[8], Token::LeftBrace);
        assert_eq!(result[9], Token::RightBrace);
        assert_eq!(result[10], Token::Label);
        assert_eq!(result[11], Token::DataRef);
        assert_eq!(result[12], Token::DecLiteral);
        assert_eq!(result[13], Token::HexLiteral);
    }

    #[test]
    fn test_identifiers() {
        let input = "add sstore callvalue x y123 _test";
        let result = Token::lexer(input).collect::<Result<Vec<_>, _>>().unwrap();

        assert_eq!(result[0], Token::Identifier);
        assert_eq!(result[1], Token::Identifier);
        assert_eq!(result[2], Token::Identifier);
        assert_eq!(result[3], Token::Identifier);
        assert_eq!(result[4], Token::Identifier);
        assert_eq!(result[5], Token::Identifier);
    }

    #[test]
    fn test_hex_literals() {
        let input = "0x00 0xdead 0xBEEF 0x123456789abcdef 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
        let result = Token::lexer(input).collect::<Result<Vec<_>, _>>().unwrap();

        assert_eq!(result[0], Token::HexLiteral);
        assert_eq!(result[1], Token::HexLiteral);
        assert_eq!(result[2], Token::HexLiteral);
        assert_eq!(result[3], Token::HexLiteral);
        assert_eq!(result[4], Token::HexLiteral);
    }

    #[test]
    fn test_comments() {
        let input = r#"
            fn main // single line comment
            /* multi
            line
            comment */ data
            switch switch
        "#;
        let lexer = Token::lexer(input);
        let tokens: Vec<_> = lexer.collect::<Result<_, _>>().expect("Lexer error");

        assert_eq!(
            tokens,
            &[
                Token::Newline,
                Token::Fn,
                Token::Identifier,
                Token::Newline,
                Token::Data,
                Token::Newline,
                Token::Switch,
                Token::Switch,
                Token::Newline,
            ]
        );
    }
}
