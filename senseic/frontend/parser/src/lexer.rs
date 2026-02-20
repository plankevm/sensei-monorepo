use logos::{Lexer as LogosLexer, Logos};
use sensei_core::{Idx, IndexVec, Span, newtype_index};

type CharsPeekable<'a> = std::iter::Peekable<std::str::CharIndices<'a>>;

fn inner_do_lex<'a, R>(
    lexer: &'a mut LogosLexer<Token>,
    token_lexer: fn(&mut CharsPeekable<'a>) -> R,
) -> R {
    let remainder = lexer.remainder();
    let mut chars = remainder.char_indices().peekable();
    let result = token_lexer(&mut chars);
    let bytes_skipped = chars.peek().map_or(remainder.len(), |&(pos, _)| pos);
    lexer.bump(bytes_skipped);

    result
}

fn lex_line_comment(lexer: &mut LogosLexer<Token>) {
    fn inner<'a>(chars: &mut CharsPeekable<'a>) {
        while chars.next().is_some_and(|(_, c)| c != '\n') {}
    }
    inner_do_lex(lexer, inner)
}

fn lex_block_comment(lexer: &mut LogosLexer<Token>) -> Result<(), Token> {
    fn inner<'a>(chars: &mut CharsPeekable<'a>) -> Result<(), Token> {
        let mut depth: u32 = 1;
        while depth > 0 {
            match chars.next() {
                Some((_, '*')) if chars.next_if(|&(_, nc)| nc == '/').is_some() => depth -= 1,
                Some((_, '/')) if chars.next_if(|&(_, nc)| nc == '*').is_some() => depth += 1,
                Some(_) => {}
                None => return Err(Token::UnclosedBlockCommentError),
            }
        }
        Ok(())
    }

    inner_do_lex(lexer, inner)
}

fn lex_number_literal<const RADIX: u32>(lexer: &mut LogosLexer<Token>) -> Result<(), Token> {
    fn inner<'a, const RADIX: u32>(chars: &mut CharsPeekable<'a>) -> Result<(), Token> {
        let mut malformed = false;
        while let Some((_, nc)) =
            chars.next_if(|&(_, nc)| matches!(nc, '_' | 'A'..='Z' | 'a'..='z' | '0'..='9'))
        {
            if nc != '_' && !nc.is_digit(RADIX) {
                malformed = true;
            }
        }

        if malformed { Err(Token::MalformedIdentError) } else { Ok(()) }
    }

    inner_do_lex(lexer, inner::<RADIX>)
}

#[derive(Logos, Debug, Clone, PartialEq, Eq, Copy, Default)]
#[logos(error(Token))]
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
    #[token("::")]
    DoubleColon,

    // Operators
    #[token("=")]
    Equals,
    #[token("+")]
    Plus,
    #[token("+%")]
    PlusPercent,
    #[token("-")]
    Minus,
    #[token("-%")]
    MinusPercent,
    #[token("*")]
    Star,
    #[token("*%")]
    StarPercent,
    #[token("/")]
    Slash,
    #[token("/+")]
    SlashPlus,
    #[token("/-")]
    SlashNeg,
    #[token("/<")]
    SlashLess,
    #[token("/>")]
    SlashGreater,
    #[token("%")]
    Percent,

    // Comparison
    #[token("==")]
    DoubleEquals,
    #[token("!=")]
    BangEquals,
    #[token("<")]
    LessThan,
    #[token(">")]
    GreaterThan,
    #[token("<=")]
    LessEquals,
    #[token(">=")]
    GreaterEquals,

    // Logical
    #[token("!")]
    Bang,
    #[token("&&")]
    AmperAmper,
    #[token("||")]
    PipePipe,

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
    #[token("return")]
    Return,
    #[token("comptime")]
    Comptime,
    #[token("inline")]
    Inline,
    #[token("while")]
    While,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("import")]
    Import,
    #[token("as")]
    As,

    #[regex("[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier,

    #[regex("-?[0-9]", lex_number_literal::<10>)]
    DecimalLiteral,
    #[regex("-?0x[0-9A-Fa-f]", lex_number_literal::<16>)]
    HexLiteral,
    #[regex("-?0b[01]", lex_number_literal::<2>)]
    BinLiteral,

    // Trivia
    #[regex("[ \t\n\r]+")]
    Whitespace,
    #[token(r"//", lex_line_comment)]
    LineComment,
    #[token(r"/*", lex_block_comment)]
    BlockComment,

    #[default]
    InvalidCharError,
    MalformedIdentError,
    UnclosedBlockCommentError,

    Eof,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl Token {
    pub const fn is_trivia(&self) -> bool {
        matches!(self, Token::Whitespace | Token::LineComment | Token::BlockComment)
    }

    pub const fn is_lex_error(&self) -> bool {
        matches!(
            self,
            Token::InvalidCharError | Token::MalformedIdentError | Token::UnclosedBlockCommentError
        )
    }

    pub const fn name(self) -> &'static str {
        match self {
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
            Token::BangEquals => "`!=`",
            Token::LessThan => "`<`",
            Token::GreaterThan => "`>`",
            Token::LessEquals => "`<=`",
            Token::GreaterEquals => "`>=`",
            Token::AmperAmper => "`&&`",
            Token::PipePipe => "`||`",
            Token::Bang => "`!`",
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
            Token::And => "`and`",
            Token::Or => "`or`",
            Token::Import => "`import`",
            Token::As => "`as`",
            Token::DoubleColon => "`::`",
            Token::Identifier => "identifier",
            Token::DecimalLiteral => "decimal literal",
            Token::HexLiteral => "hex literal",
            Token::BinLiteral => "binary literal",
            Token::Whitespace => "whitespace",
            Token::LineComment => "line comment",
            Token::BlockComment => "block comment",
            Token::InvalidCharError => "invalid character",
            Token::MalformedIdentError => "malformed literal",
            Token::UnclosedBlockCommentError => "unclosed block comment",
            Token::Eof => "EOF",
        }
    }
}

newtype_index! {
    pub struct TokenIdx;
    pub struct SourceByteOffset;
}

pub type SourceSpan = Span<SourceByteOffset>;

#[derive(Debug, Clone)]
pub struct Lexed<'src> {
    source: &'src str,
    tokens: IndexVec<TokenIdx, Token>,
    source_ends: IndexVec<TokenIdx, SourceByteOffset>,
}

const LEN_TO_TOKEN_CAPACITY: usize = 4;

impl<'src> Lexed<'src> {
    pub fn lex(source: &'src str) -> Self {
        let mut tokens = IndexVec::with_capacity(source.len().div_ceil(LEN_TO_TOKEN_CAPACITY));
        let mut source_ends = IndexVec::with_capacity(source.len().div_ceil(LEN_TO_TOKEN_CAPACITY));
        let mut last_end = SourceByteOffset::ZERO;

        let mut lexer = Lexer::new(source);
        loop {
            let (tok, span) = lexer.next_with_eof();
            tokens.push(tok);
            source_ends.push(span.end);
            debug_assert!(last_end == span.start);
            last_end = span.end;
            if tok == Token::Eof {
                break;
            }
        }

        Self { source, tokens, source_ends }
    }

    fn token_src_start(&self, token: TokenIdx) -> SourceByteOffset {
        if token == TokenIdx::ZERO { SourceByteOffset::ZERO } else { self.source_ends[token - 1] }
    }

    pub fn source(&self) -> &str {
        self.source
    }

    pub fn token_src(&self, token: TokenIdx) -> &str {
        &self.source[self.token_src_span(token).usize_range()]
    }

    pub fn tokens_src(&self, tokens: Span<TokenIdx>) -> &str {
        &self.source[self.tokens_src_span(tokens).usize_range()]
    }

    pub fn tokens_src_span(&self, tokens: Span<TokenIdx>) -> Span<SourceByteOffset> {
        let start = self.token_src_start(tokens.start);
        // Span is exclusive so we want the end token's start.
        let end = self.token_src_start(tokens.end);
        Span::new(start, end)
    }

    pub fn token_src_span(&self, index: TokenIdx) -> Span<SourceByteOffset> {
        let start = self.token_src_start(index);
        Span::new(start, self.source_ends[index])
    }

    pub fn get(&self, index: TokenIdx) -> (Token, Span<SourceByteOffset>) {
        (self.tokens[index], self.token_src_span(index))
    }

    pub fn len(&self) -> TokenIdx {
        self.tokens.len_idx()
    }
}

pub const MAX_SOURCE_LENGTH: u32 = u32::MAX - 1;

#[derive(Debug, Clone)]
pub struct Lexer<'src> {
    inner: LogosLexer<'src, Token>,
}

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str) -> Self {
        // Ensures source offsets always fit into u32 and results in at most 2^32-1 tokens
        // (including Eof).
        assert!(
            source.len() <= SourceByteOffset::MAX_USIZE,
            "source.len() exceeds MAX_SOURCE_LENGTH"
        );
        Self { inner: Token::lexer(source) }
    }

    pub fn remaining_source(&self) -> &'src str {
        self.inner.remainder()
    }

    pub fn next_with_eof(&mut self) -> (Token, SourceSpan) {
        let token = match self.inner.next() {
            Some(Ok(token) | Err(token)) => token,
            None => Token::Eof,
        };
        let span = self.inner.span();
        let span = Span::new(
            SourceByteOffset::new(span.start as u32),
            SourceByteOffset::new(span.end as u32),
        );
        (token, span)
    }
}

impl<'src> Iterator for Lexer<'src> {
    type Item = (Token, SourceSpan);

    fn next(&mut self) -> Option<Self::Item> {
        let (tok, span) = self.next_with_eof();
        (tok != Token::Eof).then_some((tok, span))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_all(source: &str) -> Vec<(Token, std::ops::Range<u32>, &str)> {
        Lexer::new(source)
            .map(|(tok, span)| (tok, span.start.get()..span.end.get(), &source[span.usize_range()]))
            .collect()
    }

    #[test]
    fn test_all_non_error_tokens() {
        assert_eq!(lex_all(";"), vec![(Token::Semicolon, 0..1, ";")]);
        assert_eq!(lex_all(","), vec![(Token::Comma, 0..1, ",")]);
        assert_eq!(lex_all(":"), vec![(Token::Colon, 0..1, ":")]);
        assert_eq!(lex_all("."), vec![(Token::Dot, 0..1, ".")]);
        assert_eq!(lex_all("{"), vec![(Token::LeftCurly, 0..1, "{")]);
        assert_eq!(lex_all("}"), vec![(Token::RightCurly, 0..1, "}")]);
        assert_eq!(lex_all("("), vec![(Token::LeftRound, 0..1, "(")]);
        assert_eq!(lex_all(")"), vec![(Token::RightRound, 0..1, ")")]);
        assert_eq!(lex_all("["), vec![(Token::LeftSquare, 0..1, "[")]);
        assert_eq!(lex_all("]"), vec![(Token::RightSquare, 0..1, "]")]);
        assert_eq!(lex_all("="), vec![(Token::Equals, 0..1, "=")]);
        assert_eq!(lex_all("+"), vec![(Token::Plus, 0..1, "+")]);
        assert_eq!(lex_all("+%"), vec![(Token::PlusPercent, 0..2, "+%")]);
        assert_eq!(lex_all("-"), vec![(Token::Minus, 0..1, "-")]);
        assert_eq!(lex_all("-%"), vec![(Token::MinusPercent, 0..2, "-%")]);
        assert_eq!(lex_all("*"), vec![(Token::Star, 0..1, "*")]);
        assert_eq!(lex_all("*%"), vec![(Token::StarPercent, 0..2, "*%")]);
        assert_eq!(lex_all("/"), vec![(Token::Slash, 0..1, "/")]);
        assert_eq!(lex_all("/+"), vec![(Token::SlashPlus, 0..2, "/+")]);
        assert_eq!(lex_all("/-"), vec![(Token::SlashNeg, 0..2, "/-")]);
        assert_eq!(lex_all("/<"), vec![(Token::SlashLess, 0..2, "/<")]);
        assert_eq!(lex_all("/>"), vec![(Token::SlashGreater, 0..2, "/>")]);
        assert_eq!(lex_all("%"), vec![(Token::Percent, 0..1, "%")]);
        assert_eq!(lex_all("=="), vec![(Token::DoubleEquals, 0..2, "==")]);
        assert_eq!(lex_all("!="), vec![(Token::BangEquals, 0..2, "!=")]);
        assert_eq!(lex_all("<"), vec![(Token::LessThan, 0..1, "<")]);
        assert_eq!(lex_all(">"), vec![(Token::GreaterThan, 0..1, ">")]);
        assert_eq!(lex_all("<="), vec![(Token::LessEquals, 0..2, "<=")]);
        assert_eq!(lex_all(">="), vec![(Token::GreaterEquals, 0..2, ">=")]);
        assert_eq!(lex_all("and"), vec![(Token::And, 0..3, "and")]);
        assert_eq!(lex_all("or"), vec![(Token::Or, 0..2, "or")]);
        assert_eq!(lex_all("!"), vec![(Token::Bang, 0..1, "!")]);
        assert_eq!(lex_all("&"), vec![(Token::Ampersand, 0..1, "&")]);
        assert_eq!(lex_all("|"), vec![(Token::Pipe, 0..1, "|")]);
        assert_eq!(lex_all("^"), vec![(Token::Caret, 0..1, "^")]);
        assert_eq!(lex_all("~"), vec![(Token::Tilde, 0..1, "~")]);
        assert_eq!(lex_all("<<"), vec![(Token::ShiftLeft, 0..2, "<<")]);
        assert_eq!(lex_all(">>"), vec![(Token::ShiftRight, 0..2, ">>")]);
        assert_eq!(lex_all("if"), vec![(Token::If, 0..2, "if")]);
        assert_eq!(lex_all("else"), vec![(Token::Else, 0..4, "else")]);
        assert_eq!(lex_all("fn"), vec![(Token::Fn, 0..2, "fn")]);
        assert_eq!(lex_all("let"), vec![(Token::Let, 0..3, "let")]);
        assert_eq!(lex_all("mut"), vec![(Token::Mut, 0..3, "mut")]);
        assert_eq!(lex_all("const"), vec![(Token::Const, 0..5, "const")]);
        assert_eq!(lex_all("init"), vec![(Token::Init, 0..4, "init")]);
        assert_eq!(lex_all("run"), vec![(Token::Run, 0..3, "run")]);
        assert_eq!(lex_all("struct"), vec![(Token::Struct, 0..6, "struct")]);
        assert_eq!(lex_all("return"), vec![(Token::Return, 0..6, "return")]);
        assert_eq!(lex_all("comptime"), vec![(Token::Comptime, 0..8, "comptime")]);
        assert_eq!(lex_all("inline"), vec![(Token::Inline, 0..6, "inline")]);
        assert_eq!(lex_all("while"), vec![(Token::While, 0..5, "while")]);
        assert_eq!(lex_all("true"), vec![(Token::True, 0..4, "true")]);
        assert_eq!(lex_all("false"), vec![(Token::False, 0..5, "false")]);
    }

    #[test]
    fn test_identifiers() {
        let results = lex_all("foo Bar _underscore x1 var_2");
        assert_eq!(results.len(), 9);
        assert_eq!(results[0], (Token::Identifier, 0..3, "foo"));
        assert_eq!(results[1], (Token::Whitespace, 3..4, " "));
        assert_eq!(results[2], (Token::Identifier, 4..7, "Bar"));
        assert_eq!(results[3], (Token::Whitespace, 7..8, " "));
        assert_eq!(results[4], (Token::Identifier, 8..19, "_underscore"));
        assert_eq!(results[5], (Token::Whitespace, 19..20, " "));
        assert_eq!(results[6], (Token::Identifier, 20..22, "x1"));
        assert_eq!(results[7], (Token::Whitespace, 22..23, " "));
        assert_eq!(results[8], (Token::Identifier, 23..28, "var_2"));
    }

    #[test]
    fn test_identifier_not_keyword() {
        let results = lex_all("ifx elsewhere fns letter mutable constant");
        assert_eq!(results.len(), 11);
        assert_eq!(results[0], (Token::Identifier, 0..3, "ifx"));
        assert_eq!(results[1], (Token::Whitespace, 3..4, " "));
        assert_eq!(results[2], (Token::Identifier, 4..13, "elsewhere"));
        assert_eq!(results[3], (Token::Whitespace, 13..14, " "));
        assert_eq!(results[4], (Token::Identifier, 14..17, "fns"));
        assert_eq!(results[5], (Token::Whitespace, 17..18, " "));
        assert_eq!(results[6], (Token::Identifier, 18..24, "letter"));
        assert_eq!(results[7], (Token::Whitespace, 24..25, " "));
        assert_eq!(results[8], (Token::Identifier, 25..32, "mutable"));
        assert_eq!(results[9], (Token::Whitespace, 32..33, " "));
        assert_eq!(results[10], (Token::Identifier, 33..41, "constant"));
    }

    #[test]
    fn test_decimal_literals() {
        let results = lex_all("123 1_000 0 42");
        assert_eq!(results.len(), 7);
        assert_eq!(results[0], (Token::DecimalLiteral, 0..3, "123"));
        assert_eq!(results[1], (Token::Whitespace, 3..4, " "));
        assert_eq!(results[2], (Token::DecimalLiteral, 4..9, "1_000"));
        assert_eq!(results[3], (Token::Whitespace, 9..10, " "));
        assert_eq!(results[4], (Token::DecimalLiteral, 10..11, "0"));
        assert_eq!(results[5], (Token::Whitespace, 11..12, " "));
        assert_eq!(results[6], (Token::DecimalLiteral, 12..14, "42"));
    }

    #[test]
    fn test_negative_decimal_literals() {
        let results = lex_all("-42 -1_000");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::DecimalLiteral, 0..3, "-42"));
        assert_eq!(results[1], (Token::Whitespace, 3..4, " "));
        assert_eq!(results[2], (Token::DecimalLiteral, 4..10, "-1_000"));
    }

    #[test]
    fn test_hex_literals() {
        let results = lex_all("0xFF 0x1A_BC 0xdead 0x0");
        assert_eq!(results.len(), 7);
        assert_eq!(results[0], (Token::HexLiteral, 0..4, "0xFF"));
        assert_eq!(results[1], (Token::Whitespace, 4..5, " "));
        assert_eq!(results[2], (Token::HexLiteral, 5..12, "0x1A_BC"));
        assert_eq!(results[3], (Token::Whitespace, 12..13, " "));
        assert_eq!(results[4], (Token::HexLiteral, 13..19, "0xdead"));
        assert_eq!(results[5], (Token::Whitespace, 19..20, " "));
        assert_eq!(results[6], (Token::HexLiteral, 20..23, "0x0"));
    }

    #[test]
    fn test_negative_hex_literals() {
        let results = lex_all("-0xDEAD -0xff");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::HexLiteral, 0..7, "-0xDEAD"));
        assert_eq!(results[1], (Token::Whitespace, 7..8, " "));
        assert_eq!(results[2], (Token::HexLiteral, 8..13, "-0xff"));
    }

    #[test]
    fn test_binary_literals() {
        let results = lex_all("0b101 0b1010_0011 0b0 0b1");
        assert_eq!(results.len(), 7);
        assert_eq!(results[0], (Token::BinLiteral, 0..5, "0b101"));
        assert_eq!(results[1], (Token::Whitespace, 5..6, " "));
        assert_eq!(results[2], (Token::BinLiteral, 6..17, "0b1010_0011"));
        assert_eq!(results[3], (Token::Whitespace, 17..18, " "));
        assert_eq!(results[4], (Token::BinLiteral, 18..21, "0b0"));
        assert_eq!(results[5], (Token::Whitespace, 21..22, " "));
        assert_eq!(results[6], (Token::BinLiteral, 22..25, "0b1"));
    }

    #[test]
    fn test_negative_binary_literals() {
        let results = lex_all("-0b11 -0b1010");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::BinLiteral, 0..5, "-0b11"));
        assert_eq!(results[1], (Token::Whitespace, 5..6, " "));
        assert_eq!(results[2], (Token::BinLiteral, 6..13, "-0b1010"));
    }

    #[test]
    fn test_line_comment() {
        let results = lex_all("// this is a comment\nfoo");
        assert_eq!(results.len(), 2);
        assert_eq!(results[0], (Token::LineComment, 0..21, "// this is a comment\n"));
        assert_eq!(results[1], (Token::Identifier, 21..24, "foo"));
    }

    #[test]
    fn test_line_comment_at_eof() {
        let results = lex_all("foo // comment at end");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::Identifier, 0..3, "foo"));
        assert_eq!(results[1], (Token::Whitespace, 3..4, " "));
        assert_eq!(results[2], (Token::LineComment, 4..21, "// comment at end"));
    }

    #[test]
    fn test_block_comment() {
        let results = lex_all("/* comment */ foo");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::BlockComment, 0..13, "/* comment */"));
        assert_eq!(results[1], (Token::Whitespace, 13..14, " "));
        assert_eq!(results[2], (Token::Identifier, 14..17, "foo"));
    }

    #[test]
    fn test_nested_block_comment() {
        let results = lex_all("/* outer /* inner */ outer */ bar");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::BlockComment, 0..29, "/* outer /* inner */ outer */"));
        assert_eq!(results[1], (Token::Whitespace, 29..30, " "));
        assert_eq!(results[2], (Token::Identifier, 30..33, "bar"));
    }

    #[test]
    fn test_deeply_nested_block_comment() {
        let results = lex_all("/* a /* b /* c */ b */ a */ x");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::BlockComment, 0..27, "/* a /* b /* c */ b */ a */"));
        assert_eq!(results[1], (Token::Whitespace, 27..28, " "));
        assert_eq!(results[2], (Token::Identifier, 28..29, "x"));
    }

    #[test]
    fn test_nested_block_comment_with_content() {
        let results = lex_all("/* /* nested */ code(); /* more */ */ after");
        assert_eq!(results.len(), 3);
        assert_eq!(
            results[0],
            (Token::BlockComment, 0..37, "/* /* nested */ code(); /* more */ */")
        );
        assert_eq!(results[1], (Token::Whitespace, 37..38, " "));
        assert_eq!(results[2], (Token::Identifier, 38..43, "after"));
    }

    #[test]
    fn test_block_comment_utf8() {
        let results = lex_all("/* émoji 🎉 */ foo");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::BlockComment, 0..17, "/* émoji 🎉 */"));
        assert_eq!(results[1], (Token::Whitespace, 17..18, " "));
        assert_eq!(results[2], (Token::Identifier, 18..21, "foo"));
    }

    #[test]
    fn test_block_comment_utf8_cjk() {
        let results = lex_all("/* 日本語 */ bar");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::BlockComment, 0..15, "/* 日本語 */"));
        assert_eq!(results[1], (Token::Whitespace, 15..16, " "));
        assert_eq!(results[2], (Token::Identifier, 16..19, "bar"));
    }

    #[test]
    fn test_line_comment_utf8() {
        let results = lex_all("// café ☕\nfoo");
        assert_eq!(results.len(), 2);
        assert_eq!(results[0], (Token::LineComment, 0..13, "// café ☕\n"));
        assert_eq!(results[1], (Token::Identifier, 13..16, "foo"));
    }

    #[test]
    fn test_invalid_char_at() {
        let results = lex_all("@");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::InvalidCharError, 0..1, "@"));
    }

    #[test]
    fn test_invalid_char_hash() {
        let results = lex_all("#");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::InvalidCharError, 0..1, "#"));
    }

    #[test]
    fn test_invalid_char_in_context() {
        let results = lex_all("foo @ bar");
        assert_eq!(results.len(), 5);
        assert_eq!(results[0], (Token::Identifier, 0..3, "foo"));
        assert_eq!(results[1], (Token::Whitespace, 3..4, " "));
        assert_eq!(results[2], (Token::InvalidCharError, 4..5, "@"));
        assert_eq!(results[3], (Token::Whitespace, 5..6, " "));
        assert_eq!(results[4], (Token::Identifier, 6..9, "bar"));
    }

    #[test]
    fn test_unclosed_block_comment() {
        let results = lex_all("/* no end");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::UnclosedBlockCommentError, 0..9, "/* no end"));
    }

    #[test]
    fn test_unclosed_nested_block_comment() {
        let results = lex_all("/* outer /* inner */");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::UnclosedBlockCommentError, 0..20, "/* outer /* inner */"));
    }

    #[test]
    fn test_malformed_binary_no_digits() {
        let results = lex_all("0b__");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::MalformedIdentError, 0..4, "0b__"));
    }

    #[test]
    fn test_malformed_binary_prefix_only() {
        let results = lex_all("0b");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::MalformedIdentError, 0..2, "0b"));
    }

    #[test]
    fn test_malformed_hex_prefix_only() {
        let results = lex_all("0x");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::MalformedIdentError, 0..2, "0x"));
    }

    #[test]
    fn test_malformed_hex_no_digits() {
        let results = lex_all("0x__");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::MalformedIdentError, 0..4, "0x__"));
    }

    #[test]
    fn test_span_identifier() {
        let results = lex_all("  foo  bar  ");
        assert_eq!(results.len(), 5);
        assert_eq!(results[0], (Token::Whitespace, 0..2, "  "));
        assert_eq!(results[1], (Token::Identifier, 2..5, "foo"));
        assert_eq!(results[2], (Token::Whitespace, 5..7, "  "));
        assert_eq!(results[3], (Token::Identifier, 7..10, "bar"));
        assert_eq!(results[4], (Token::Whitespace, 10..12, "  "));
    }

    #[test]
    fn test_span_numeric_literals() {
        let results = lex_all("  123  0xFF  0b101  ");
        assert_eq!(results.len(), 7);
        assert_eq!(results[0], (Token::Whitespace, 0..2, "  "));
        assert_eq!(results[1], (Token::DecimalLiteral, 2..5, "123"));
        assert_eq!(results[2], (Token::Whitespace, 5..7, "  "));
        assert_eq!(results[3], (Token::HexLiteral, 7..11, "0xFF"));
        assert_eq!(results[4], (Token::Whitespace, 11..13, "  "));
        assert_eq!(results[5], (Token::BinLiteral, 13..18, "0b101"));
        assert_eq!(results[6], (Token::Whitespace, 18..20, "  "));
    }

    #[test]
    fn test_span_multi_char_operators() {
        let results = lex_all("  ==  <=  <<  ");
        assert_eq!(results.len(), 7);
        assert_eq!(results[0], (Token::Whitespace, 0..2, "  "));
        assert_eq!(results[1], (Token::DoubleEquals, 2..4, "=="));
        assert_eq!(results[2], (Token::Whitespace, 4..6, "  "));
        assert_eq!(results[3], (Token::LessEquals, 6..8, "<="));
        assert_eq!(results[4], (Token::Whitespace, 8..10, "  "));
        assert_eq!(results[5], (Token::ShiftLeft, 10..12, "<<"));
        assert_eq!(results[6], (Token::Whitespace, 12..14, "  "));
    }

    #[test]
    fn test_whitespace_varieties() {
        let results = lex_all("a\tb\nc\r\nd");
        assert_eq!(results.len(), 7);
        assert_eq!(results[0], (Token::Identifier, 0..1, "a"));
        assert_eq!(results[1], (Token::Whitespace, 1..2, "\t"));
        assert_eq!(results[2], (Token::Identifier, 2..3, "b"));
        assert_eq!(results[3], (Token::Whitespace, 3..4, "\n"));
        assert_eq!(results[4], (Token::Identifier, 4..5, "c"));
        assert_eq!(results[5], (Token::Whitespace, 5..7, "\r\n"));
        assert_eq!(results[6], (Token::Identifier, 7..8, "d"));
    }

    #[test]
    fn test_multiple_whitespace_combined() {
        let results = lex_all("a   \t\n  b");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::Identifier, 0..1, "a"));
        assert_eq!(results[1], (Token::Whitespace, 1..8, "   \t\n  "));
        assert_eq!(results[2], (Token::Identifier, 8..9, "b"));
    }

    #[test]
    fn test_comment_span() {
        let results = lex_all("/* block */ // line");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Token::BlockComment, 0..11, "/* block */"));
        assert_eq!(results[1], (Token::Whitespace, 11..12, " "));
        assert_eq!(results[2], (Token::LineComment, 12..19, "// line"));
    }

    #[test]
    fn test_nested_comment_span() {
        let results = lex_all("/* outer /* inner */ end */");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], (Token::BlockComment, 0..27, "/* outer /* inner */ end */"));
    }
}
