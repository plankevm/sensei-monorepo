use clap::Parser;
use sensei_hir::{display::DisplayHir, lower};
use sensei_parser::{
    cst::display::DisplayCST,
    error_report::{ErrorCollector, LineIndex, format_error},
    interner::PlankInterner,
    lexer::Lexed,
    parser::parse,
};

#[derive(Parser)]
#[command(name = "senseic", about = "Sensei compiler frontend")]
struct Args {
    file_path: String,

    #[arg(short = 'l', long = "show-lines", help = "enables line numbers in the CST output")]
    show_lines: bool,

    #[arg(short = 'c', long = "show-cst", help = "show CST")]
    show_cst: bool,
}

fn main() {
    let args = Args::parse();
    let source = std::fs::read_to_string(&args.file_path).expect("Failed to read file");

    let lexed = Lexed::lex(&source);
    let mut collector = ErrorCollector::default();
    let mut interner = PlankInterner::default();
    let cst = parse(&lexed, &mut interner, &mut collector);

    if args.show_cst {
        let display = DisplayCST::new(&cst, &source, &lexed).show_line(args.show_lines);
        println!("{}", display);
    }

    if !collector.errors.is_empty() {
        let line_index = LineIndex::new(&source);
        for error in &collector.errors {
            eprintln!("{}\n", format_error(error, &source, &line_index));
        }

        std::process::exit(1);
    }

    let hir = lower(&cst);

    print!("{}", DisplayHir::new(&hir, &interner));
}
