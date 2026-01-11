use bumpalo::Bump;
use neosen_parser::{AstDisplay, parse};

fn main() {
    let mut args = std::env::args();
    args.next();
    let file_path = args.next().expect("Missing: PATH");

    let source = std::fs::read_to_string(&file_path).expect("Failed to read file");

    let arena = Bump::with_capacity(8000);
    let output = parse(&source, &arena);

    println!("=== AST ===");
    println!("{}", AstDisplay::new(&output.ast, &output.interner));

    if output.diagnostics.has_errors() {
        println!("\n=== Diagnostics ({} errors) ===", output.diagnostics.error_count());
        for diag in output.diagnostics.errors() {
            let (line, col) = offset_to_line_col(&source, diag.span.start as usize);
            println!("{}:{}:{}: error: {}", file_path, line, col, diag.message);
            for note in diag.notes.iter() {
                if let Some(note_span) = note.span {
                    let (note_line, note_col) = offset_to_line_col(&source, note_span.start as usize);
                    println!("  {}:{}:{}: note: {}", file_path, note_line, note_col, note.message);
                } else {
                    println!("  note: {}", note.message);
                }
            }
        }
    }
}

fn offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, c) in source.char_indices() {
        if i >= offset {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}
