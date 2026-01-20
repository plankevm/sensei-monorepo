use crate::{
    cst::TokenIdx,
    diagnostics::DiagnosticsContext,
    lexer::{SourceSpan, Token},
};

#[derive(Debug, Clone)]
pub enum ParserError {
    LexerError { token: Token, span: SourceSpan },
    UnexpectedToken { found: Token, expected: Vec<Token>, span: SourceSpan },
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

    fn emit_unexpected_token(&mut self, found: Token, expected: &[Token], src_span: SourceSpan) {
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

#[derive(Debug)]
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
    found: Token,
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
        1 => expected[0].name().to_string(),
        _ => {
            let names: Vec<_> = expected.iter().map(|t| t.name()).collect();
            format!("one of {}", names.join(", "))
        }
    };

    format!(
        "error: unexpected {}, expected {}\n  --> line {}:{}\n   |\n{:>3}| {}\n   | {}",
        found,
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
        expected,
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
        opener,
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
