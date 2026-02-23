use alloy_primitives::U256;
use hashbrown::{HashMap, hash_map::Entry};
use sensei_core::{
    Idx, IncIterable, IndexVec, Span,
    list_of_lists::{ListOfLists, ListOfListsPusher},
    newtype_index,
};
use sensei_parser::{
    StrId,
    ast::{self, Statement, TopLevelDef},
    cst::{ConcreteSyntaxTree, NodeIdx, NumLitId},
    lexer::TokenIdx,
};

pub mod display;
pub mod types;
mod values;

newtype_index! {
    pub struct ConstId;
    pub struct LocalId;
    pub struct BlockId;
    pub struct FnDefId;
    pub struct StructDefId;
    pub struct CallArgsId;
    pub struct FieldsId;

    pub struct BigNumId;
}

#[derive(Debug, Clone, Copy)]
pub enum Expr {
    // References
    ConstRef(ConstId),
    LocalRef(LocalId),
    FnDef(FnDefId),
    // Literals
    Bool(bool),
    Void,
    BigNum(BigNumId),
    // Compound expressions
    Call { callee: LocalId, args: CallArgsId },
    Member { object: LocalId, member: StrId },
    StructLit { ty: LocalId, fields: FieldsId },
    StructDef(StructDefId),
}

impl Expr {
    fn has_side_effects(&self) -> bool {
        matches!(
            self,
            Expr::Call { .. } | Expr::Member { .. } | Expr::StructLit { .. } | Expr::StructDef(_)
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Instruction {
    // Define local
    Set { local: LocalId, expr: Expr },
    // Mutate local
    Assign { target: LocalId, value: Expr },
    Eval(Expr),
    Return(Expr),
    BlockYield(Expr),
    If { condition: Expr, then_block: BlockId, else_block: BlockId, follow: BlockId },
    While { condition_block: BlockId, body: BlockId, follow: BlockId },
}

#[derive(Debug, Clone, Copy)]
pub struct ParamInfo {
    pub comptime: bool,
    pub local: LocalId,
}

#[derive(Debug, Clone, Copy)]
pub struct FieldInfo {
    pub name: StrId,
    pub value: LocalId,
}

#[derive(Debug, Clone, Copy)]
pub struct FnDef {
    pub source: NodeIdx,
    pub body: BlockId,
}

#[derive(Debug, Clone, Copy)]
pub struct StructDef {
    pub source: NodeIdx,
    pub type_index: LocalId,
    pub fields: FieldsId,
}

#[derive(Debug, Clone, Default)]
pub struct ConstMap {
    pub const_name_to_id: HashMap<StrId, ConstId>,
    pub const_defs: IndexVec<ConstId, ConstDef>,
}

#[derive(Debug, Clone, Copy)]
pub struct ConstDef {
    pub source: Span<TokenIdx>,
    pub body: BlockId,
}

#[derive(Debug, Clone)]
pub struct CallParam {
    pub local: LocalId,
    pub is_comptime: bool,
}

#[derive(Debug, Clone)]
pub struct Hir {
    // Instruction storage
    pub blocks: ListOfLists<BlockId, Instruction>,
    pub call_params: ListOfLists<CallArgsId, CallParam>,
    pub fields: ListOfLists<FieldsId, FieldInfo>,
    pub big_nums: IndexVec<BigNumId, U256>,
    // Top-level definitions
    pub consts: ConstMap,
    pub const_deps: ListOfLists<ConstId, ConstId>,
    pub fns: IndexVec<FnDefId, FnDef>,
    pub fn_params: ListOfLists<FnDefId, ParamInfo>,
    pub struct_defs: IndexVec<StructDefId, StructDef>,
    // Entry points
    pub init: BlockId,
    pub run: Option<BlockId>,
}

struct HirBuilder {
    blocks: ListOfLists<BlockId, Instruction>,
    call_args: ListOfLists<CallArgsId, CallParam>,
    fields: ListOfLists<FieldsId, FieldInfo>,
    big_nums: IndexVec<BigNumId, U256>,
    fns: IndexVec<FnDefId, FnDef>,
    fn_params: ListOfLists<FnDefId, ParamInfo>,
    struct_defs: IndexVec<StructDefId, StructDef>,
}

impl HirBuilder {
    fn new() -> Self {
        Self {
            blocks: ListOfLists::new(),
            call_args: ListOfLists::new(),
            fields: ListOfLists::new(),
            big_nums: IndexVec::new(),
            fns: IndexVec::new(),
            fn_params: ListOfLists::new(),
            struct_defs: IndexVec::new(),
        }
    }
}

struct BlockLowerer<'a, 'b, 'c> {
    consts: &'a ConstMap,
    deps: Option<&'b mut ListOfListsPusher<'c, ConstId, ConstId>>,
    num_lit_limbs: &'a ListOfLists<NumLitId, u32>,
    big_nums: &'a mut IndexVec<BigNumId, U256>,
    block: ListOfListsPusher<'a, BlockId, Instruction>,
    locals: Vec<(StrId, LocalId)>,
    next_local_id: LocalId,
}

impl<'a, 'b, 'c> BlockLowerer<'a, 'b, 'c> {
    fn alloc_local(&mut self, name: StrId) -> LocalId {
        let id = self.next_local_id.get_and_inc();
        self.locals.push((name, id));
        id
    }

    fn lookup_local(&self, name: StrId) -> Option<LocalId> {
        self.locals.iter().rev().find_map(|(n, id)| (*n == name).then_some(*id))
    }

    fn emit(&mut self, instr: Instruction) {
        self.block.push(instr);
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
            ast::Expr::NumLiteral { negative, id } => {
                let limbs = &self.num_lit_limbs[id];
                let value = sensei_core::bigint::limbs_to_u256(limbs, negative);
                let big_num_id = self.big_nums.push(value);
                Expr::BigNum(big_num_id)
            }
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
                self.emit(Instruction::Set { local: local_id, expr: value });
            }
            Statement::Expr(expr) => {
                let value = self.lower_expr(expr);
                if value.has_side_effects() {
                    self.emit(Instruction::Eval(value));
                }
            }
            Statement::Return(_) => todo!("return statement lowering"),
            Statement::Assign(_) => todo!("assign statement lowering"),
            Statement::While(_) => todo!("while statement lowering"),
        }
    }

    fn lower_top_level_block(&mut self, block: ast::BlockExpr<'_>) {
        let result = self.lower_nested_block(block);
        self.emit(Instruction::BlockYield(result));
    }

    fn lower_top_level_expr(&mut self, expr: ast::Expr<'_>) {
        let result = self.lower_expr(expr);
        self.emit(Instruction::BlockYield(result));
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
                        let new_const_id = consts.const_defs.push(ConstDef {
                            source: const_def.span(),
                            body: BlockId::ZERO, // placeholder, filled in later
                        });

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

    let mut builder = HirBuilder::new();
    let mut const_deps: ListOfLists<ConstId, ConstId> = ListOfLists::new();
    let mut init = BlockId::ZERO;
    let mut run = None;

    let num_lit_limbs = &cst.num_lit_limbs;

    for def in file.iter_defs() {
        match def {
            TopLevelDef::Const(const_def) => {
                let id = consts.const_name_to_id[&const_def.name];
                let dep_id = const_deps.push_with(|mut dep_pusher| {
                    let HirBuilder { blocks, big_nums, .. } = &mut builder;
                    consts.const_defs[id].body = blocks.push_with(|block| {
                        BlockLowerer {
                            consts: &consts,
                            deps: Some(&mut dep_pusher),
                            num_lit_limbs,
                            big_nums,
                            block,
                            locals: Vec::new(),
                            next_local_id: LocalId::ZERO,
                        }
                        .lower_top_level_expr(const_def.assign)
                    });
                });
                assert_eq!(id, dep_id, "ID in-syncness invariant violated");
            }
            TopLevelDef::Init(init_def) => {
                let HirBuilder { blocks, big_nums, .. } = &mut builder;
                init = blocks.push_with(|block| {
                    BlockLowerer {
                        consts: &consts,
                        deps: None,
                        num_lit_limbs,
                        big_nums,
                        block,
                        locals: Vec::new(),
                        next_local_id: LocalId::ZERO,
                    }
                    .lower_top_level_block(init_def.body())
                });
            }
            TopLevelDef::Run(run_def) => {
                let HirBuilder { blocks, big_nums, .. } = &mut builder;
                run = Some(blocks.push_with(|block| {
                    BlockLowerer {
                        consts: &consts,
                        deps: None,
                        num_lit_limbs,
                        big_nums,
                        block,
                        locals: Vec::new(),
                        next_local_id: LocalId::ZERO,
                    }
                    .lower_top_level_block(run_def.body())
                }));
            }
            TopLevelDef::Import(_) => unreachable!(),
        }
    }

    Hir {
        blocks: builder.blocks,
        call_params: builder.call_args,
        fields: builder.fields,
        big_nums: builder.big_nums,
        consts,
        const_deps,
        fns: builder.fns,
        fn_params: builder.fn_params,
        struct_defs: builder.struct_defs,
        init,
        run,
    }
}
