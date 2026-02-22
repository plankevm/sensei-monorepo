use hashbrown::{HashMap, hash_map::Entry};
use sensei_core::{
    Idx, IncIterable, IndexVec, Span,
    list_of_lists::{ListOfLists, ListOfListsPusher},
    newtype_index,
};
use sensei_parser::{
    StrId,
    ast::{self, Statement, TopLevelDef},
    cst::ConcreteSyntaxTree,
    lexer::TokenIdx,
};

pub mod display;
pub mod types;
mod values;

newtype_index! {
    pub struct ConstId;
    pub struct LocalId;
}

#[derive(Debug, Clone, Default)]
pub struct ConstMap {
    pub const_name_to_id: HashMap<StrId, ConstId>,
    pub const_defs: IndexVec<ConstId, ConstDef>,
}

#[derive(Debug, Clone)]
pub struct ConstDef {
    pub source: Span<TokenIdx>,
    pub instructions: Vec<Instruction>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    ConstRef(ConstId),
    LocalRef(LocalId),
    Bool(bool),
    Void,
}

#[derive(Debug, Clone)]
pub enum Instruction {
    Set { sets: LocalId, expr: Expr },
    BlockYield(Expr),
}

#[derive(Debug, Clone)]
pub struct Hir {
    pub consts: ConstMap,
    pub const_deps: ListOfLists<ConstId, ConstId>,
    pub init: Vec<Instruction>,
    pub run: Option<Vec<Instruction>>,
}

struct BlockLowerer<'a, 'b> {
    consts: &'a ConstMap,
    deps: Option<ListOfListsPusher<'b, ConstId, ConstId>>,
    locals: Vec<(StrId, LocalId)>,
    next_local_id: LocalId,
    instructions: Vec<Instruction>,
}

impl<'a, 'b> BlockLowerer<'a, 'b> {
    fn new(consts: &'a ConstMap, deps: Option<ListOfListsPusher<'b, ConstId, ConstId>>) -> Self {
        Self {
            consts,
            deps,
            locals: Vec::new(),
            next_local_id: LocalId::ZERO,
            instructions: Vec::new(),
        }
    }

    fn alloc_local(&mut self, name: StrId) -> LocalId {
        let id = self.next_local_id.get_and_inc();
        self.locals.push((name, id));
        id
    }

    fn lookup_local(&self, name: StrId) -> Option<LocalId> {
        self.locals.iter().rev().find_map(|(n, id)| (*n == name).then_some(*id))
    }

    fn emit(&mut self, instr: Instruction) {
        self.instructions.push(instr);
    }

    fn lower_expr(&mut self, expr: ast::Expr<'_>) -> Expr {
        match expr {
            ast::Expr::Ident(name) => {
                if let Some(local_id) = self.lookup_local(name) {
                    Expr::LocalRef(local_id)
                } else if let Some(&const_id) = self.consts.const_name_to_id.get(&name) {
                    if let Some(deps) = &mut self.deps
                        && !deps.current().contains(&const_id)
                    {
                        deps.push(const_id);
                    }
                    Expr::ConstRef(const_id)
                } else {
                    // TODO: diagnostic
                    panic!("unresolved identifier")
                }
            }
            ast::Expr::Block(block) => self.lower_nested_block(block),
            ast::Expr::BoolLiteral(b) => Expr::Bool(b),
            other => todo!("TODO expr lowering for: {other:?}"),
        }
    }

    fn scoped<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let scope_start = self.locals.len();
        let result = f(self);
        self.locals.truncate(scope_start);
        result
    }

    fn lower_nested_block(&mut self, block: ast::BlockExpr<'_>) -> Expr {
        self.scoped(|lowerer| {
            for stmt in block.statements() {
                lowerer.lower_statement(stmt);
            }

            match block.end_expr() {
                Some(expr) => lowerer.lower_expr(expr),
                None => Expr::Void,
            }
        })
    }

    fn lower_statement(&mut self, stmt: Statement<'_>) {
        match stmt {
            Statement::Let(let_stmt) => {
                let value = self.lower_expr(let_stmt.value());
                let local_id = self.alloc_local(let_stmt.name);
                self.emit(Instruction::Set { sets: local_id, expr: value });
            }
            Statement::Expr(expr) => {
                let _ = self.lower_expr(expr);
            }
        }
    }

    fn into_block<F>(mut self, f: F) -> Vec<Instruction>
    where
        F: FnOnce(&mut Self) -> Expr,
    {
        let result = f(&mut self);
        self.emit(Instruction::BlockYield(result));
        self.instructions
    }
}

pub fn lower(cst: &ConcreteSyntaxTree) -> Hir {
    let mut consts = ConstMap::default();
    let file = ast::File::new(cst.file_view()).expect("failed to init file from CST");

    let mut found_init = false;
    let mut found_run = false;

    for def in file.iter_defs() {
        match def {
            TopLevelDef::Const(const_def) => {
                match consts.const_name_to_id.entry(const_def.name) {
                    Entry::Occupied(_) => {
                        // TODO: error diagnostic
                        panic!("duplicate const def")
                    }
                    Entry::Vacant(entry) => {
                        let new_const_id = consts
                            .const_defs
                            .push(ConstDef { source: const_def.span(), instructions: Vec::new() });

                        entry.insert(new_const_id);
                    }
                }
            }
            TopLevelDef::Init(_) => {
                assert!(!found_init, "more than one init"); // TODO: Error diagnostic
                found_init = true;
            }
            TopLevelDef::Run(_) => {
                assert!(!found_run, "more than one run"); // TODO: Error diagnostic
                found_run = true;
            }
            TopLevelDef::Import(_) => todo!("imports"),
        }
    }

    let mut const_deps: ListOfLists<ConstId, ConstId> = ListOfLists::new();
    // TODO: Capacity estimation
    let mut init = Vec::with_capacity(0);
    let mut run = None;

    for def in file.iter_defs() {
        match def {
            TopLevelDef::Const(const_def) => {
                let id = consts.const_name_to_id[&const_def.name];
                let dep_id = const_deps.push_with(|pusher| {
                    consts.const_defs[id].instructions = BlockLowerer::new(&consts, Some(pusher))
                        .into_block(|lowerer| lowerer.lower_expr(const_def.assign));
                });
                assert_eq!(id, dep_id, "ID in-syncness invariant violated");
            }
            TopLevelDef::Init(init_def) => {
                init = BlockLowerer::new(&consts, None)
                    .into_block(|lowerer| lowerer.lower_nested_block(init_def.body()))
            }
            TopLevelDef::Run(run_def) => {
                run = Some(
                    BlockLowerer::new(&consts, None)
                        .into_block(|lowerer| lowerer.lower_nested_block(run_def.body())),
                )
            }
            TopLevelDef::Import(_) => todo!(),
        }
    }

    Hir { consts, const_deps, init, run }
}
