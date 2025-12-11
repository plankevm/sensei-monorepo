use sencore::parser::{lower_sexpr_to_ast, Parser};

fn main() {
    let mut args = std::env::args();
    args.next().unwrap();
    let path = args.next().expect("Missing [PATH] argument");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("Failed to read file {:?}: {:?}", path, e));

    let mut parser = Parser::new(&source);
    let list = parser
        .parse_list()
        .expect("parsing failed")
        .expect("input does not contain list?");

    let ast = lower_sexpr_to_ast(&list).expect("lowering failed");

    println!("{}", ast);
}
