use clap::Parser;
use sensei_hir::{display::DisplayHir, lower};
use sensei_parser::{
    cst::display::DisplayCST,
    error_report::{LineIndex, format_error},
    interner::PlankInterner,
    lexer::Lexed,
    module::ModuleManager,
    project::parse_project,
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
    let mut interner = PlankInterner::default();
    let mut module_manager = ModuleManager::default();
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

    let project = parse_project(Path::new(&args.file_path), &module_manager, &mut interner);

    if args.show_cst {
        let source = &project.sources[project.entry];
        let lexed = Lexed::lex(source);
        let display = DisplayCST::new(&project.csts[project.entry], source, &lexed)
            .show_line(args.show_lines);
        println!("{}", display);
    }

    let mut has_errors = false;
    for (source_id, errors) in project.errors.enumerate_idx() {
        if errors.is_empty() {
            continue;
        }
        has_errors = true;
        let source = &project.sources[source_id];
        let line_index = LineIndex::new(source);
        for error in errors {
            eprintln!("{}\n", format_error(error, source, &line_index));
        }
    }
    if has_errors {
        std::process::exit(1);
    }

    let hir = lower(&project);

    print!("{}", DisplayHir::new(&hir, &interner));
}
