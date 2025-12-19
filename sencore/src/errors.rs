use crate::Span;
use std::fmt::Write;

#[derive(Debug, Clone, Copy)]
pub struct SourceLocation {
    pub line: usize,
    pub column: usize,
}

pub fn byte_offset_to_location(source: &str, offset: usize) -> SourceLocation {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    SourceLocation { line, column: col }
}


pub fn format_error(source: &str, message: &str, span: Span<usize>) -> String {
    let start_loc = byte_offset_to_location(source, span.start);
    let end_loc = byte_offset_to_location(source, span.end.saturating_sub(1).max(span.start));

    let lines: Vec<&str> = source.lines().collect();

    let mut output = String::new();

    writeln!(output, "error: {}", message).unwrap();
    writeln!(output, "  --> {}:{}", start_loc.line, start_loc.column).unwrap();
    writeln!(output).unwrap();

    let context_before = 2;
    let context_after = 2;

    let first_line = start_loc.line;
    let last_line = end_loc.line;

    let display_start = first_line.saturating_sub(context_before).max(1);
    let display_end = (last_line + context_after).min(lines.len());

    let max_line_num = display_end;
    let line_num_width = max_line_num.to_string().len();

    for line_num in display_start..=display_end {
        let line_idx = line_num - 1;
        let line_content = lines.get(line_idx).unwrap_or(&"");

        writeln!(
            output,
            "{:>width$} | {}",
            line_num,
            line_content,
            width = line_num_width
        )
        .unwrap();

        if line_num >= first_line && line_num <= last_line {
            let highlight_start = if line_num == first_line {
                start_loc.column - 1
            } else {
                0
            };

            let highlight_end = if line_num == last_line {
                end_loc.column
            } else {
                line_content.len()
            };

            let highlight_len = highlight_end.saturating_sub(highlight_start).max(1);

            let spaces = " ".repeat(highlight_start);
            let carets = "^".repeat(highlight_len);

            writeln!(
                output,
                "{:>width$} | {}{}",
                "",
                spaces,
                carets,
                width = line_num_width
            )
            .unwrap();
        }
    }

    output
}
