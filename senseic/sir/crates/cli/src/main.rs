use clap::Parser;
use sir_optimizations::Optimization;
use sir_parser::{EmitConfig, parse_or_panic};
use std::{
    fs,
    io::{self, Read},
    path::PathBuf,
};

#[derive(Parser)]
#[command(name = "sir")]
#[command(about = "Sensei IR to EVM bytecode compiler", long_about = None)]
#[command(version)]
struct Cli {
    /// Input file (use '-' or omit for stdin)
    input: Option<PathBuf>,

    /// Compile only init function (no main)
    #[arg(long)]
    init_only: bool,

    /// Override init function name
    #[arg(long, default_value = "init")]
    init_name: String,

    /// Override main function name
    #[arg(long, default_value = "main")]
    main_name: String,

    /// Use maximized assembly mode (default: minimized)
    #[arg(long)]
    maximized: bool,

    /// Enable copy propagation optimization
    #[arg(long)]
    copy_propagation: bool,

    /// Enable constant propagation optimization
    #[arg(long)]
    constant_propagation: bool,
}

fn read_input(input: Option<PathBuf>) -> String {
    let use_stdin = match &input {
        None => true,
        Some(path) => path.to_str() == Some("-"),
    };

    if use_stdin {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer).expect("stdin read to succeed");
        buffer
    } else {
        let path = input.unwrap();
        fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read file '{}': {}", path.display(), e))
    }
}

fn main() {
    let cli = Cli::parse();

    // Read input source
    let source = read_input(cli.input);

    // Build emit configuration
    let config = if cli.init_only {
        EmitConfig::init_only_with_name(&cli.init_name)
    } else {
        EmitConfig::new(&cli.init_name, &cli.main_name)
    };

    // Parse IR to EthIRProgram
    let mut program = parse_or_panic(&source, config);

    if cli.copy_propagation {
        Optimization::CopyPropagation.apply(&mut program);
    }

    if cli.constant_propagation {
        Optimization::ConstantPropagation.apply(&mut program);
    }

    let mut bytecode = Vec::with_capacity(0x6000);
    sir_debug_backend::ir_to_bytecode(&program, &mut bytecode);

    // Format and print output
    print!("0x");
    for byte in bytecode {
        print!("{:02x}", byte);
    }
    println!();
}
