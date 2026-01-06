use sencore::comptime_value::{Closure, Value};
use sencore::errors::{format_error, format_error_stack};
use sencore::parser::{Parser, lower_sexpr_to_ast};

fn main() {
    let mut args = std::env::args();
    args.next().unwrap();
    let path = args.next().expect("Missing [PATH] argument");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("Failed to read file {:?}: {:?}", path, e));

    let mut parser = Parser::new(&source);
    let list = match parser.parse_list() {
        Ok(Some(list)) => list,
        Ok(None) => {
            eprintln!("error: input does not contain a list");
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("{}", format_error(&source, &e.message, e.span));
            std::process::exit(1);
        }
    };

    let ast = match lower_sexpr_to_ast(&list) {
        Ok(ast) => ast,
        Err(e) => {
            eprintln!("{}", format_error(&source, &e.message, e.span));
            std::process::exit(1);
        }
    };

    println!("========= Interpreter Input =========");
    println!("{}", ast);

    let value = match sencore::interpreter::interpret(&ast.runtime_main) {
        Ok(value) => value,
        Err(e) => {
            eprintln!("\n\n{}", format_error_stack(&source, &e));
            std::process::exit(1);
        }
    };

    println!("========= Interpreter Output =========");
    println!("{}", value);

    // match value {
    //     Value::Closure(closure) => {
    //         println!("Closure");
    //         println!("  {} : {:?}", closure.binds, closure.r#type);
    //         println!("  {}", closure.body);
    //     }
    //     value => println!("{:#?}", value),
    // }
}
