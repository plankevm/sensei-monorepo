use clap::Parser;
use sensei_hir::{display::DisplayHir, lower};
use sensei_parser::{
    cst::display::DisplayCST,
    error_report::{ErrorCollector, LineIndex, format_error},
    interner::PlankInterner,
    lexer::Lexed,
    module::ModuleManager,
    parser::parse,
};
use std::path::{Path, PathBuf};

#[derive(Parser)]
#[command(name = "senseic", about = "Sensei compiler frontend")]
struct Args {
    file_path: String,

    #[arg(short = 'l', long = "show-lines", help = "enables line numbers in the CST output")]
    show_lines: bool,

    #[arg(short = 'c', long = "show-cst", help = "show CST")]
    show_cst: bool,

    #[arg(long = "module-name")]
    module_name: Option<String>,

    #[arg(long = "module-root", requires = "module_name")]
    module_root: Option<String>,

    #[arg(long = "dep", value_parser = parse_dep)]
    deps: Vec<(String, PathBuf)>,
}

fn parse_dep(s: &str) -> Result<(String, PathBuf), String> {
    let (name, path) =
        s.split_once('=').ok_or_else(|| format!("expected format name=path, got '{s}'"))?;
    Ok((name.to_string(), PathBuf::from(path)))
}

fn main() {
    let args = Args::parse();
    let source = std::fs::read_to_string(&args.file_path).expect("Failed to read file");

    let mut interner = PlankInterner::default();
    let mut module_manager = ModuleManager::new();
    if let Some(name) = &args.module_name {
        let name_id = interner.intern(name);
        let root = match &args.module_root {
            Some(root) => PathBuf::from(root),
            None => Path::new(&args.file_path)
                .parent()
                .expect("file path has no parent directory")
                .to_path_buf(),
        };
        module_manager.register(name_id, root);
    }
    for (name, path) in &args.deps {
        let name_id = interner.intern(name);
        module_manager.register(name_id, path.clone());
    }

    let lexed = Lexed::lex(&source);
    let mut collector = ErrorCollector::default();
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
