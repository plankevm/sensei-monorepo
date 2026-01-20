use bumpalo::Bump;
use neosen_parser::{
    cst::display::DisplayCST,
    error_report::{ErrorCollector, LineIndex, format_error},
    lexer::Lexer,
    parser::parse,
};

fn main() {
    let mut args = std::env::args();
    args.next();
    let file_path = args.next().expect("Missing: PATH");
    let mut show_lines = false;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--show-lines" | "-l" => show_lines = true,
            unknown => panic!("Unexpected value or flag {unknown:?}"),
        }
    }

    let source = std::fs::read_to_string(&file_path).expect("Failed to read file");
    let arena = Bump::with_capacity(8000);

    let lexer = Lexer::new(&source);
    let mut collector = ErrorCollector::default();
    let cst = parse(&arena, lexer, 64, &mut collector);

    if !collector.errors.is_empty() {
        let line_index = LineIndex::new(&source);
        for error in &collector.errors {
            eprintln!("{}\n", format_error(error, &source, &line_index));
        }
    }

    let mut display = DisplayCST::new(cst, &source);
    if show_lines {
        display = display.show_line()
    }

    println!("{}", display);
}
