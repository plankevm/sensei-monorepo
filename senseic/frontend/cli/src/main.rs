use sensei_parser::{
    cst::display::DisplayCST,
    error_report::{ErrorCollector, LineIndex, format_error},
    lexer::Lexed,
    parser::parse,
};

fn main() {
    let mut args = std::env::args();
    args.next();
    let file_path = args.next().expect("Missing: PATH");
    let mut show_lines = false;

    for arg in args {
        match arg.as_str() {
            "--show-lines" | "-l" => show_lines = true,
            unknown => panic!("Unexpected value or flag {unknown:?}"),
        }
    }

    let source = std::fs::read_to_string(&file_path).expect("Failed to read file");

    let lexed = Lexed::lex(&source);
    let mut collector = ErrorCollector::default();
    let cst = parse(&lexed, &mut collector);

    let display = DisplayCST::new(&cst, &source, &lexed).show_line(show_lines);
    println!("{}", display);

    if !collector.errors.is_empty() {
        let line_index = LineIndex::new(&source);
        for error in &collector.errors {
            eprintln!("{}\n", format_error(error, &source, &line_index));
        }

        std::process::exit(1);
    }
}
