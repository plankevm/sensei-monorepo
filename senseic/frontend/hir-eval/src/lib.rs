use hashbrown::HashMap;
use sensei_core::{IndexVec, index_vec, list_of_lists::ListOfLists};
use sensei_hir::{ConstId, Hir};
use sensei_mir::{self as mir, Mir};
use sensei_values::{TypeId, TypeInterner, ValueId};

mod comptime;
mod lower;
mod value;

use value::ValueInterner;

#[derive(Clone)]
enum ConstState {
    NotEvaluated,
    InProgress,
    Evaluated(ValueId),
}

pub(crate) struct Evaluator<'hir> {
    pub hir: &'hir Hir,
    pub values: ValueInterner,
    pub types: TypeInterner,
    const_states: IndexVec<ConstId, ConstState>,
    pub mir_blocks: ListOfLists<mir::BlockId, mir::Instruction>,
    pub mir_fns: IndexVec<mir::FnId, mir::FnDef>,
    pub mir_fn_locals: ListOfLists<mir::FnId, Option<TypeId>>,
    pub mir_args: ListOfLists<mir::ArgsId, mir::LocalId>,
    pub fn_cache: HashMap<ValueId, mir::FnId>,
}

impl<'hir> Evaluator<'hir> {
    fn new(hir: &'hir Hir) -> Self {
        let const_count = hir.consts.const_defs.len();
        Self {
            hir,
            values: ValueInterner::new(),
            types: TypeInterner::new(),
            const_states: index_vec![ConstState::NotEvaluated; const_count],
            mir_blocks: ListOfLists::new(),
            mir_fns: IndexVec::new(),
            mir_fn_locals: ListOfLists::new(),
            mir_args: ListOfLists::new(),
            fn_cache: HashMap::new(),
        }
    }

    pub fn ensure_const_evaluated(&mut self, const_id: ConstId) -> ValueId {
        match self.const_states[const_id] {
            ConstState::Evaluated(value_id) => value_id,
            ConstState::InProgress => panic!("cyclical const dependency detected"),
            ConstState::NotEvaluated => {
                self.const_states[const_id] = ConstState::InProgress;
                let const_def = self.hir.consts.const_defs[const_id];
                let value_id = lower::eval_const_body(self, const_def);
                self.const_states[const_id] = ConstState::Evaluated(value_id);
                value_id
            }
        }
    }
}

pub fn evaluate(hir: &Hir) -> Mir {
    let mut eval = Evaluator::new(hir);

    for const_id in hir.consts.const_defs.iter_idx() {
        eval.ensure_const_evaluated(const_id);
    }

    let init = lower::lower_block_as_fn(&mut eval, hir.init);
    let run = hir.run.map(|block| lower::lower_block_as_fn(&mut eval, block));

    Mir {
        blocks: eval.mir_blocks,
        args: eval.mir_args,
        fns: eval.mir_fns,
        fn_locals: eval.mir_fn_locals,
        types: eval.types,
        init,
        run,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_and_lower(source: &str) -> Hir {
        let lexed = sensei_parser::lexer::Lexed::lex(source);
        let mut collector = sensei_parser::error_report::ErrorCollector::default();
        let mut interner = sensei_parser::interner::PlankInterner::default();
        let cst = sensei_parser::parser::parse(&lexed, &mut interner, &mut collector);
        assert!(collector.errors.is_empty(), "parse errors: {:?}", collector.errors);
        let mut big_nums = sensei_values::BigNumInterner::new();
        sensei_hir::lower(&cst, &mut big_nums)
    }

    #[test]
    fn empty_init() {
        let hir = parse_and_lower("init {}");
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
        assert!(mir.run.is_none());
    }

    #[test]
    fn simple_const_and_init() {
        let hir = parse_and_lower(
            "const X = 42;
             init { let a = X; }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }

    #[test]
    fn const_referencing_const() {
        let hir = parse_and_lower(
            "const A = true;
             const B = A;
             init {}",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }

    #[test]
    fn init_and_run() {
        let hir = parse_and_lower(
            "
            init {}
            run {}
            ",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 2);
        assert!(mir.run.is_some());
    }

    #[test]
    fn bool_literal_in_init() {
        let hir = parse_and_lower("init { let x = true; let y = false; }");
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }

    #[test]
    fn typed_let_binding() {
        let hir = parse_and_lower("init { let x: u256 = 42; }");
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }

    #[test]
    fn function_call() {
        let hir = parse_and_lower(
            "const add = fn (a: u256, b: u256) u256 { a };
             init { let x = add(1, 2); }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 2);
    }

    #[test]
    fn function_with_capture() {
        let hir = parse_and_lower(
            "const K = 10;
             const f = fn (x: u256) u256 { K };
             init { let y = f(1); }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 2);
    }

    #[test]
    fn function_call_deduplication() {
        let hir = parse_and_lower(
            "const id = fn (x: u256) u256 { x };
             init { let a = id(1); let b = id(2); }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 2);
    }

    #[test]
    fn struct_def_and_literal() {
        let hir = parse_and_lower(
            "const Point = struct {} { x: u256, y: u256 };
             init { let p = Point { x: 1, y: 2 }; let v = p.x; }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }

    #[test]
    fn comptime_struct_propagation() {
        let hir = parse_and_lower(
            "const Point = struct {} { x: u256, y: u256 };
             const ORIGIN = Point { x: 0, y: 0 };
             init { let p = ORIGIN; }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }

    #[test]
    fn if_else() {
        let hir = parse_and_lower(
            "const FLAG = true;
             init { let x = if FLAG { 1 } else { 2 }; }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }

    #[test]
    fn while_loop() {
        let hir = parse_and_lower(
            "const check = fn (x: u256) bool { true };
             init {
                let i: u256 = 0;
                while check(i) { i = 1; }
             }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 2);
    }

    #[test]
    fn assign() {
        let hir = parse_and_lower(
            "init {
                let i: u256 = 0;
                i = 1;
             }",
        );
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }

    #[test]
    fn const_literal_evaluation() {
        let hir = parse_and_lower("const X = 42; init {}");
        let mir = evaluate(&hir);
        assert_eq!(mir.fns.len(), 1);
    }
}
