use crate::{
    cst::TokenIdx,
    diagnostics::DiagnosticsContext,
    lexer::{Lexer, SourceSpan, Token},
    parser::parse,
};
use bumpalo::Bump;

mod parser;

#[derive(Debug, Clone)]
pub enum ParserError {
    LexerError { token: Token, span: SourceSpan },
    UnexpectedToken { found: Option<Token>, expected: Vec<Token>, span: SourceSpan },
    MissingToken { expected: Token, at_span: SourceSpan },
    UnclosedDelimiter { opener: Token, open_span: SourceSpan, found_span: SourceSpan },
}

#[derive(Debug, Default)]
pub struct ErrorCollector {
    pub errors: Vec<ParserError>,
}

impl DiagnosticsContext for ErrorCollector {
    fn emit_lexer_error(&mut self, token: Token, _index: TokenIdx, src_span: SourceSpan) {
        self.errors.push(ParserError::LexerError { token, span: src_span });
    }

    fn emit_unexpected_token(
        &mut self,
        found: Option<Token>,
        expected: &[Token],
        src_span: SourceSpan,
    ) {
        self.errors.push(ParserError::UnexpectedToken {
            found,
            expected: expected.to_vec(),
            span: src_span,
        });
    }

    fn emit_missing_token(&mut self, expected: Token, at_span: SourceSpan) {
        self.errors.push(ParserError::MissingToken { expected, at_span });
    }

    fn emit_unclosed_delimiter(
        &mut self,
        opener: Token,
        open_span: SourceSpan,
        found_span: SourceSpan,
    ) {
        self.errors.push(ParserError::UnclosedDelimiter { opener, open_span, found_span });
    }
}

pub struct LineIndex {
    line_starts: Vec<u32>,
    source_len: u32,
}

impl LineIndex {
    pub fn new(source: &str) -> Self {
        let mut line_starts = vec![0u32];
        for (i, ch) in source.char_indices() {
            if ch == '\n' {
                line_starts.push((i + 1) as u32);
            }
        }
        LineIndex { line_starts, source_len: source.len() as u32 }
    }

    pub fn line_col(&self, byte_offset: u32) -> (usize, usize) {
        let offset = byte_offset.min(self.source_len);

        let line_idx = match self.line_starts.binary_search(&offset) {
            Ok(idx) => idx,
            Err(idx) => idx.saturating_sub(1),
        };

        let line = line_idx + 1;
        let col = (offset - self.line_starts[line_idx]) as usize + 1;
        (line, col)
    }

    pub fn line_text<'a>(&self, source: &'a str, line: usize) -> &'a str {
        if line == 0 || line > self.line_starts.len() {
            return "";
        }
        let start = self.line_starts[line - 1] as usize;
        let end = self.line_starts.get(line).map(|&e| e as usize).unwrap_or(source.len());

        source[start..end].trim_end_matches('\n').trim_end_matches('\r')
    }
}

fn token_name(token: Token) -> &'static str {
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
        Token::DecimalLiteral => "decimal literal",
        Token::HexLiteral => "hex literal",
        Token::BinLiteral => "binary literal",
        Token::Whitespace => "whitespace",
        Token::LineComment => "line comment",
        Token::BlockComment => "block comment",
        Token::InvalidCharError => "invalid character",
        Token::MalformedIdentError => "malformed literal",
        Token::UnclosedBlockCommentError => "unclosed block comment",
    }
}

fn underline(col_start: usize, col_end: usize) -> String {
    let prefix = " ".repeat(col_start.saturating_sub(1));
    let carets = "^".repeat(col_end.saturating_sub(col_start).max(1));
    format!("{}{}", prefix, carets)
}

pub fn format_error(error: &ParserError, source: &str, line_index: &LineIndex) -> String {
    match error {
        ParserError::LexerError { token, span } => {
            format_lexer_error(*token, *span, source, line_index)
        }
        ParserError::UnexpectedToken { found, expected, span } => {
            format_unexpected_token(*found, expected, *span, source, line_index)
        }
        ParserError::MissingToken { expected, at_span } => {
            format_missing_token(*expected, *at_span, source, line_index)
        }
        ParserError::UnclosedDelimiter { opener, open_span, found_span } => {
            format_unclosed_delimiter(*opener, *open_span, *found_span, source, line_index)
        }
    }
}

fn format_lexer_error(
    token: Token,
    span: SourceSpan,
    source: &str,
    line_index: &LineIndex,
) -> String {
    let (line, col_start) = line_index.line_col(span.start);
    let (_, col_end) = line_index.line_col(span.end);
    let line_text = line_index.line_text(source, line);
    let snippet = &source[span.usize_range()];

    let message = match token {
        Token::InvalidCharError => format!("invalid character `{}`", snippet),
        Token::MalformedIdentError => format!("malformed literal `{}`", snippet),
        Token::UnclosedBlockCommentError => "unclosed block comment".to_string(),
        _ => format!("lexer error: {:?}", token),
    };

    format!(
        "error: {}\n  --> line {}:{}\n   |\n{:>3}| {}\n   | {}",
        message,
        line,
        col_start,
        line,
        line_text,
        underline(col_start, col_end)
    )
}

fn format_unexpected_token(
    found: Option<Token>,
    expected: &[Token],
    span: SourceSpan,
    source: &str,
    line_index: &LineIndex,
) -> String {
    let (line, col_start) = line_index.line_col(span.start);
    let (_, col_end) = line_index.line_col(span.end);
    let line_text = line_index.line_text(source, line);

    let expected_str = match expected.len() {
        0 => "nothing".to_string(),
        1 => token_name(expected[0]).to_string(),
        _ => {
            let names: Vec<_> = expected.iter().map(|t| token_name(*t)).collect();
            format!("one of {}", names.join(", "))
        }
    };

    format!(
        "error: unexpected {}, expected {}\n  --> line {}:{}\n   |\n{:>3}| {}\n   | {}",
        found.map_or("EOF", token_name),
        expected_str,
        line,
        col_start,
        line,
        line_text,
        underline(col_start, col_end)
    )
}

fn format_missing_token(
    expected: Token,
    at_span: SourceSpan,
    source: &str,
    line_index: &LineIndex,
) -> String {
    let (line, col) = line_index.line_col(at_span.start);
    let line_text = line_index.line_text(source, line);

    format!(
        "error: missing {}\n  --> line {}:{}\n   |\n{:>3}| {}\n   | {}",
        token_name(expected),
        line,
        col,
        line,
        line_text,
        underline(col, col + 1)
    )
}

fn format_unclosed_delimiter(
    opener: Token,
    open_span: SourceSpan,
    found_span: SourceSpan,
    source: &str,
    line_index: &LineIndex,
) -> String {
    let (open_line, open_col) = line_index.line_col(open_span.start);
    let (_, open_col_end) = line_index.line_col(open_span.end);
    let (found_line, found_col) = line_index.line_col(found_span.start);
    let open_line_text = line_index.line_text(source, open_line);

    let mut result = format!(
        "error: unclosed delimiter {}\n  --> line {}:{}\n   |\n{:>3}| {}\n   | {}",
        token_name(opener),
        open_line,
        open_col,
        open_line,
        open_line_text,
        underline(open_col, open_col_end)
    );

    if found_line != open_line {
        let found_line_text = line_index.line_text(source, found_line);
        result.push_str(&format!(
            "\n   |\n{:>3}| {}\n   | {} expected closing delimiter here",
            found_line,
            found_line_text,
            underline(found_col, found_col + 1)
        ));
    }

    result
}

fn dedent(s: &str) -> String {
    let mut lines: Vec<&str> = s.lines().collect();

    // Remove leading empty line (common when string starts with newline)
    if lines.first().is_some_and(|l| l.trim().is_empty()) {
        lines.remove(0);
    }
    // Remove trailing empty line
    if lines.last().is_some_and(|l| l.trim().is_empty()) {
        lines.pop();
    }

    // Find minimum indentation across non-empty lines
    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);

    // Strip common indentation
    lines
        .into_iter()
        .map(|l| if l.len() >= min_indent { &l[min_indent..] } else { l.trim() })
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn assert_parser_errors(source: &str, expected_errors: &[&str]) {
    let source = dedent(source);
    let arena = Bump::new();
    let lexer = Lexer::new(&source);
    let mut collector = ErrorCollector::default();

    let _cst = parse(&arena, lexer, 64, &mut collector);

    let line_index = LineIndex::new(&source);
    let actual: Vec<String> =
        collector.errors.iter().map(|e| format_error(e, &source, &line_index)).collect();

    let expected: Vec<String> = expected_errors.iter().map(|s| dedent(s)).collect();

    // Join with separator for cleaner multiline diff output
    let actual_joined = actual.join("\n\n---\n\n");
    let expected_joined = expected.join("\n\n---\n\n");
    pretty_assertions::assert_str_eq!(actual_joined, expected_joined);
}
