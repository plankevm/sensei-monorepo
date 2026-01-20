use crate::{
    cst::display::DisplayCST,
    error_report::{ErrorCollector, LineIndex, format_error},
    lexer::Lexer,
    parser::parse,
};
use bumpalo::Bump;

// mod resiliency;
mod errorless;

fn dedent(s: &str) -> String {
    s.lines().map(|line| line.trim()).filter(|line| !line.is_empty()).collect::<Vec<_>>().join("\n")
}

fn dedent_preserve_indent(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let non_empty_lines: Vec<&str> =
        lines.iter().copied().filter(|l| !l.trim().is_empty()).collect();

    if non_empty_lines.is_empty() {
        return String::new();
    }

    let min_indent =
        non_empty_lines.iter().map(|line| line.len() - line.trim_start().len()).min().unwrap_or(0);

    non_empty_lines.iter().map(|line| &line[min_indent..]).collect::<Vec<_>>().join("\n")
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

    let actual_joined = actual.join("\n\n---\n\n");
    let expected_joined = expected.join("\n\n---\n\n");
    pretty_assertions::assert_str_eq!(actual_joined, expected_joined);
}

pub fn assert_parses_to_cst_no_errors(source: &str, expected: &str) {
    let arena = Bump::new();
    let lexer = Lexer::new(&source);
    let mut collector = ErrorCollector::default();

    let cst = parse(&arena, lexer, 64, &mut collector);

    if !collector.errors.is_empty() {
        let line_index = LineIndex::new(&source);
        let errors: Vec<String> =
            collector.errors.iter().map(|e| format_error(e, &source, &line_index)).collect();
        panic!(
            "Expected no parser errors, but found {}:\n\n{}",
            collector.errors.len(),
            errors.join("\n\n---\n\n")
        );
    }

    let actual = format!("{}", DisplayCST::new(cst, &source));

    pretty_assertions::assert_str_eq!(actual.trim(), expected.trim());
}
