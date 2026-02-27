use alloy_primitives::U256;
use hashbrown::HashMap;
use sensei_core::{Idx, IncIterable, IndexVec, Span, list_of_lists::ListOfLists, newtype_index};
use sensei_parser::{
    StrId,
    ast::{self, Statement, TopLevelDef},
    cst::{ConcreteSyntaxTree, NodeIdx, NumLitId},
    lexer::TokenIdx,
    project::{FileImport, ParsedProject},
    source::SourceId,
};

pub use sensei_types;
use sensei_types::TypeId;

pub mod display;

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
    Type(TypeId),
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
    AssertType { value: LocalId, of_type: LocalId },
    Eval(Expr),
    Return(Expr),
    If { condition: LocalId, then_block: BlockId, else_block: BlockId },
    While { condition_block: BlockId, body: BlockId },
}

const _INSTR_SIZE: () = const { assert!(std::mem::size_of::<Instruction>() == 20) };

#[derive(Debug, Clone, Copy)]
pub struct ParamInfo {
    pub comptime: bool,
    pub local: LocalId,
}

#[derive(Debug, Clone, Copy)]
pub struct CaptureInfo {
    pub outer_local: LocalId,
    pub inner_local: LocalId,
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

#[derive(Debug, Clone, Copy)]
pub struct ConstDef {
    pub name: StrId,
    pub source: Span<TokenIdx>,
    pub body: BlockId,
    pub result: LocalId,
}

#[derive(Debug, Clone)]
pub struct Hir {
    // Instruction storage
    pub blocks: ListOfLists<BlockId, Instruction>,
    pub call_params: ListOfLists<CallArgsId, LocalId>,
    pub fields: ListOfLists<FieldsId, FieldInfo>,
    pub big_nums: IndexVec<BigNumId, U256>,
    // Top-level definitions
    pub consts: IndexVec<ConstId, ConstDef>,
    pub const_deps: ListOfLists<ConstId, ConstId>,
    pub fns: IndexVec<FnDefId, FnDef>,
    pub fn_params: ListOfLists<FnDefId, ParamInfo>,
    pub fn_captures: ListOfLists<FnDefId, CaptureInfo>,
    pub struct_defs: IndexVec<StructDefId, StructDef>,
    // Entry points
    pub init: BlockId,
    pub run: Option<BlockId>,
}

struct HirBuilder {
    blocks: ListOfLists<BlockId, Instruction>,
    call_args: ListOfLists<CallArgsId, LocalId>,
    fields: ListOfLists<FieldsId, FieldInfo>,
    big_nums: IndexVec<BigNumId, U256>,
    fns: IndexVec<FnDefId, FnDef>,
    fn_params: ListOfLists<FnDefId, ParamInfo>,
    fn_captures: ListOfLists<FnDefId, CaptureInfo>,
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
            fn_captures: ListOfLists::new(),
            struct_defs: IndexVec::new(),
        }
    }
}

struct BlockLowerer<'a> {
    consts: HashMap<StrId, ConstId>,
    num_lit_limbs: &'a ListOfLists<NumLitId, u32>,
    track_deps: bool,
    deps: Vec<ConstId>,
    builder: &'a mut HirBuilder,
    instructions: Vec<Instruction>,
    locals: Vec<(StrId, LocalId)>,
    fn_scope_start: usize,
    next_local_id: LocalId,
    arg_buf: Vec<LocalId>,
    field_buf: Vec<FieldInfo>,
    capture_buf: Vec<CaptureInfo>,
}

impl<'a> BlockLowerer<'a> {
    fn reset(&mut self, track_deps: bool) {
        self.track_deps = track_deps;
        self.deps.clear();
        self.instructions.clear();
        self.locals.clear();
        self.fn_scope_start = 0;
        self.next_local_id = LocalId::ZERO;
        debug_assert!(self.arg_buf.is_empty());
        debug_assert!(self.field_buf.is_empty());
        debug_assert!(self.capture_buf.is_empty());
    }

    fn alloc_local(&mut self, name: StrId) -> LocalId {
        if TypeId::resolve_primitive(name).is_some() {
            // TODO: Diagnostic
            panic!("shadowing primitive");
        }

        let id = self.next_local_id.get_and_inc();
        self.locals.push((name, id));
        id
    }

    fn alloc_temp(&mut self) -> LocalId {
        self.next_local_id.get_and_inc()
    }

    fn lower_expr_to_local(&mut self, expr: ast::Expr<'_>) -> LocalId {
        let value = self.lower_expr(expr);
        let local = self.alloc_temp();
        self.emit(Instruction::Set { local, expr: value });
        local
    }

    fn create_sub_block(&mut self, f: impl FnOnce(&mut Self)) -> BlockId {
        let locals_start = self.locals.len();
        let block_start = self.instructions.len();
        f(self);
        self.locals.truncate(locals_start);
        self.flush_instructions_from(block_start)
    }

    fn create_fn_body_block(&mut self, f: impl FnOnce(&mut Self)) -> BlockId {
        let saved_scope_start = self.fn_scope_start;
        let saved_next_local = std::mem::replace(&mut self.next_local_id, LocalId::ZERO);
        self.fn_scope_start = self.locals.len();
        let block_start = self.instructions.len();
        f(self);
        self.locals.truncate(self.fn_scope_start);
        self.fn_scope_start = saved_scope_start;
        self.next_local_id = saved_next_local;
        self.flush_instructions_from(block_start)
    }

    fn lower_body_to_block(&mut self, block: ast::BlockExpr<'_>) -> BlockId {
        self.create_sub_block(|lowerer| {
            for stmt in block.statements() {
                lowerer.lower_statement(stmt);
            }
            if let Some(e) = block.end_expr() {
                let value = lowerer.lower_expr(e);
                if value.has_side_effects() {
                    lowerer.emit(Instruction::Eval(value));
                }
            }
        })
    }

    fn lower_body_to_block_with_result(
        &mut self,
        block: ast::BlockExpr<'_>,
        result: LocalId,
    ) -> BlockId {
        self.create_sub_block(|lowerer| {
            for stmt in block.statements() {
                lowerer.lower_statement(stmt);
            }
            let value = block.end_expr().map(|e| lowerer.lower_expr(e)).unwrap_or(Expr::Void);
            lowerer.emit(Instruction::Set { local: result, expr: value });
        })
    }

    fn lookup_local(&self, name: StrId) -> Option<LocalId> {
        self.locals[self.fn_scope_start..]
            .iter()
            .rev()
            .find_map(|(n, id)| (*n == name).then_some(*id))
    }

    fn lookup_capture(&mut self, name: StrId) -> Option<LocalId> {
        self.locals[..self.fn_scope_start]
            .iter()
            .rev()
            .find_map(|(n, id)| (*n == name).then_some(*id))
            .map(|outer_local| {
                let inner_local = self.alloc_local(name);
                self.capture_buf.push(CaptureInfo { outer_local, inner_local });
                inner_local
            })
    }

    fn emit(&mut self, instr: Instruction) {
        self.instructions.push(instr);
    }

    fn flush_instructions_from(&mut self, start: usize) -> BlockId {
        self.builder.blocks.push_iter(self.instructions.drain(start..))
    }

    fn resolve_name(&mut self, name: StrId) -> Expr {
        if let Some(ty) = TypeId::resolve_primitive(name) {
            return Expr::Type(ty);
        }

        if let Some(local_id) = self.lookup_local(name) {
            return Expr::LocalRef(local_id);
        }

        if let Some(capture_local) = self.lookup_capture(name) {
            return Expr::LocalRef(capture_local);
        }

        if let Some(&const_id) = self.consts.get(&name) {
            if self.track_deps && !self.deps.contains(&const_id) {
                self.deps.push(const_id);
            }
            return Expr::ConstRef(const_id);
        }

        // TODO: diagnostic
        panic!("unresolved identifier")
    }

    fn lower_expr(&mut self, expr: ast::Expr<'_>) -> Expr {
        match expr {
            ast::Expr::Ident(name) => self.resolve_name(name),
            ast::Expr::Block(block) => self.lower_scope(block),
            ast::Expr::BoolLiteral(b) => Expr::Bool(b),
            ast::Expr::NumLiteral { negative, id } => {
                let limbs = &self.num_lit_limbs[id];
                let value = sensei_core::bigint::limbs_to_u256(limbs, negative)
                    .expect("number literal out of range");
                let big_num_id = self.builder.big_nums.push(value);
                Expr::BigNum(big_num_id)
            }
            ast::Expr::Member(member_expr) => {
                let object = self.lower_expr_to_local(member_expr.object());
                Expr::Member { object, member: member_expr.member }
            }
            ast::Expr::Call(call_expr) => {
                let callee = self.lower_expr_to_local(call_expr.callee());
                let buf_start = self.arg_buf.len();
                for arg in call_expr.args() {
                    let local = self.lower_expr_to_local(arg);
                    self.arg_buf.push(local);
                }
                let args = self.builder.call_args.push_iter(self.arg_buf.drain(buf_start..));
                Expr::Call { callee, args }
            }
            ast::Expr::StructLit(struct_lit) => {
                let ty = self.lower_expr_to_local(struct_lit.type_expr());
                let buf_start = self.field_buf.len();
                for field in struct_lit.fields() {
                    let value = self.lower_expr_to_local(field.value());
                    self.field_buf.push(FieldInfo { name: field.name, value });
                }
                let fields = self.builder.fields.push_iter(self.field_buf.drain(buf_start..));
                Expr::StructLit { ty, fields }
            }
            ast::Expr::StructDef(struct_def) => {
                let source = struct_def.node().idx();
                let type_index = self.lower_expr_to_local(struct_def.index_expr());
                let buf_start = self.field_buf.len();
                for field in struct_def.fields() {
                    let value = self.lower_expr_to_local(field.type_expr());
                    self.field_buf.push(FieldInfo { name: field.name, value });
                }
                let fields = self.builder.fields.push_iter(self.field_buf.drain(buf_start..));
                let struct_def_id =
                    self.builder.struct_defs.push(StructDef { source, type_index, fields });
                Expr::StructDef(struct_def_id)
            }
            ast::Expr::FnDef(fn_def) => {
                let source = fn_def.node().idx();
                let capture_start = self.capture_buf.len();

                let body = self.create_fn_body_block(|lowerer| {
                    // Phase 1: Allocate param locals (0..n)
                    for param in fn_def.params() {
                        lowerer.alloc_local(param.name);
                    }

                    // Phase 2: Lower param type annotations, emit AssertType
                    for (i, param) in fn_def.params().enumerate() {
                        let type_local = lowerer.lower_expr_to_local(param.type_expr());
                        let param_local = LocalId::new(i as u32);
                        lowerer.emit(Instruction::AssertType {
                            value: param_local,
                            of_type: type_local,
                        });
                    }

                    // Phase 3: Lower return type then body (following syntactic order)
                    let return_type_local = lowerer.lower_expr_to_local(fn_def.return_type());
                    let body_value = lowerer.lower_expr(fn_def.body());
                    let result_local = lowerer.alloc_temp();
                    lowerer.emit(Instruction::Set { local: result_local, expr: body_value });
                    lowerer.emit(Instruction::AssertType {
                        value: result_local,
                        of_type: return_type_local,
                    });
                    lowerer.emit(Instruction::Return(Expr::LocalRef(result_local)));
                });

                let fn_def_id = self.builder.fns.push(FnDef { source, body });
                let fn_params_id =
                    self.builder.fn_params.push_iter(fn_def.params().enumerate().map(|(i, p)| {
                        ParamInfo { comptime: p.comptime, local: LocalId::new(i as u32) }
                    }));
                let fn_captures_id =
                    self.builder.fn_captures.push_iter(self.capture_buf.drain(capture_start..));
                assert_eq!(fn_def_id, fn_params_id, "fn and fn_params out of sync");
                assert_eq!(fn_def_id, fn_captures_id, "fn and fn_captures out of sync");

                Expr::FnDef(fn_def_id)
            }
            ast::Expr::If(if_expr) => {
                let result = self.alloc_temp();
                let condition = self.lower_expr_to_local(if_expr.condition());
                let then_block = self.lower_body_to_block_with_result(if_expr.body(), result);
                let else_block =
                    self.lower_else_chain(result, if_expr.else_if_branches(), if_expr.else_body());
                self.emit(Instruction::If { condition, then_block, else_block });
                Expr::LocalRef(result)
            }
            ast::Expr::ComptimeBlock(_) => {
                todo!("comptime block lowering requires extra HIR instructions")
            }
            ast::Expr::Binary(binary) => {
                panic!("binary expression lowering not yet implemented (op: {:?})", binary.op)
            }
            ast::Expr::Unary(unary) => {
                panic!("unary expression lowering not yet implemented (op: {:?})", unary.op)
            }
        }
    }

    fn scoped<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let scope_start = self.locals.len();
        let result = f(self);
        self.locals.truncate(scope_start);
        result
    }

    fn lower_scope(&mut self, block: ast::BlockExpr<'_>) -> Expr {
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

    fn lower_else_chain<'cst>(
        &mut self,
        result: LocalId,
        mut branches: impl Iterator<Item = ast::ElseIfBranch<'cst>>,
        else_body: Option<ast::BlockExpr<'cst>>,
    ) -> BlockId {
        if let Some(first) = branches.next() {
            self.create_sub_block(|lowerer| {
                let condition = lowerer.lower_expr_to_local(first.condition());
                let then_block = lowerer.lower_body_to_block_with_result(first.body(), result);
                let else_block = lowerer.lower_else_chain(result, branches, else_body);
                lowerer.emit(Instruction::If { condition, then_block, else_block });
            })
        } else if let Some(body) = else_body {
            self.lower_body_to_block_with_result(body, result)
        } else {
            self.create_sub_block(|lowerer| {
                lowerer.emit(Instruction::Set { local: result, expr: Expr::Void });
            })
        }
    }

    fn lower_statement(&mut self, stmt: Statement<'_>) {
        match stmt {
            Statement::Let(let_stmt) => {
                let type_local = let_stmt.type_expr().map(|t| self.lower_expr_to_local(t));
                let value = self.lower_expr(let_stmt.value());
                let local_id = self.alloc_local(let_stmt.name);
                self.emit(Instruction::Set { local: local_id, expr: value });
                if let Some(type_local) = type_local {
                    self.emit(Instruction::AssertType { value: local_id, of_type: type_local });
                }
            }
            Statement::Expr(expr) => {
                let value = self.lower_expr(expr);
                if value.has_side_effects() {
                    self.emit(Instruction::Eval(value));
                }
            }
            Statement::Return(return_stmt) => {
                let value = self.lower_expr(return_stmt.value());
                self.emit(Instruction::Return(value));
            }
            Statement::Assign(assign_stmt) => {
                let target = match assign_stmt.target() {
                    ast::Expr::Ident(name) => {
                        self.lookup_local(name).expect("unresolved assignment target")
                    }
                    _ => panic!("complex assignment targets not yet supported"),
                };
                let value = self.lower_expr(assign_stmt.value());
                self.emit(Instruction::Assign { target, value });
            }
            Statement::While(while_stmt) => {
                if while_stmt.inline {
                    panic!("inline while not yet supported");
                }
                let condition_block = self.create_sub_block(|lowerer| {
                    lowerer.lower_expr_to_local(while_stmt.condition());
                });
                let body = self.lower_body_to_block(while_stmt.body());
                self.emit(Instruction::While { condition_block, body });
            }
        }
    }
}

pub fn lower(project: &ParsedProject) -> Hir {
    let (mut consts, source_consts) = register_consts(&project.csts);

    let mut builder = HirBuilder::new();
    let mut const_deps: ListOfLists<ConstId, ConstId> = ListOfLists::new();
    let mut init = None;
    let mut run = None;

    let mut lowerer = BlockLowerer {
        consts: HashMap::new(),
        num_lit_limbs: &project.csts[SourceId::ZERO].num_lit_limbs,
        track_deps: false,
        deps: Vec::new(),
        builder: &mut builder,
        instructions: Vec::new(),
        locals: Vec::new(),
        fn_scope_start: 0,
        next_local_id: LocalId::ZERO,
        arg_buf: Vec::new(),
        field_buf: Vec::new(),
        capture_buf: Vec::new(),
    };

    for (source_id, cst) in project.csts.enumerate_idx() {
        build_file_scope(source_id, &source_consts, &project.imports, &mut lowerer.consts);
        lowerer.num_lit_limbs = &cst.num_lit_limbs;

        let file = ast::File::new(cst.file_view()).expect("failed to init file from CST");
        for def in file.iter_defs() {
            match def {
                TopLevelDef::Const(const_def) => {
                    lowerer.reset(true);
                    let id = lowerer.consts[&const_def.name];
                    let hir_def = &mut consts[id];
                    hir_def.result = lowerer.alloc_local(const_def.name);
                    hir_def.body = lowerer.create_sub_block(|lowerer| {
                        if let Some(type_expr) = const_def.r#type {
                            let type_local = lowerer.lower_expr_to_local(type_expr);
                            let assign = lowerer.lower_expr(const_def.assign);
                            lowerer.emit(Instruction::Set { local: hir_def.result, expr: assign });
                            lowerer.emit(Instruction::AssertType {
                                value: hir_def.result,
                                of_type: type_local,
                            });
                        } else {
                            let assign = lowerer.lower_expr(const_def.assign);
                            lowerer.emit(Instruction::Set { local: hir_def.result, expr: assign });
                        }
                    });
                    let const_id_by_dep = const_deps.push_iter(lowerer.deps.drain(..));
                    assert_eq!(id, const_id_by_dep, "ID in-syncness invariant violated");
                }
                TopLevelDef::Init(init_def) => {
                    assert!(source_id == project.entry, "init only allowed in entry file");
                    lowerer.reset(false);
                    init = Some(lowerer.lower_body_to_block(init_def.body()));
                }
                TopLevelDef::Run(run_def) => {
                    assert!(source_id == project.entry, "run only allowed in entry file");
                    lowerer.reset(false);
                    run = Some(lowerer.lower_body_to_block(run_def.body()));
                }
                TopLevelDef::Import(_) => {}
            }
        }
    }

    let init = init.expect("missing init block");

    Hir {
        blocks: builder.blocks,
        call_params: builder.call_args,
        fields: builder.fields,
        big_nums: builder.big_nums,
        consts,
        const_deps,
        fns: builder.fns,
        fn_params: builder.fn_params,
        fn_captures: builder.fn_captures,
        struct_defs: builder.struct_defs,
        init,
        run,
    }
}

fn register_consts(
    csts: &IndexVec<SourceId, ConcreteSyntaxTree>,
) -> (IndexVec<ConstId, ConstDef>, ListOfLists<SourceId, (StrId, ConstId)>) {
    let mut consts: IndexVec<ConstId, ConstDef> = IndexVec::new();
    let mut source_consts: ListOfLists<SourceId, (StrId, ConstId)> = ListOfLists::new();

    for cst in csts.iter() {
        let file = ast::File::new(cst.file_view()).expect("failed to init file from CST");
        source_consts.push_with(|mut list| {
            for def in file.iter_defs() {
                let TopLevelDef::Const(const_def) = def else { continue };
                let const_id = consts.push(ConstDef {
                    name: const_def.name,
                    source: const_def.span(),
                    body: BlockId::ZERO,
                    result: LocalId::ZERO,
                });
                list.push((const_def.name, const_id));
            }
        });
    }

    (consts, source_consts)
}

fn build_file_scope(
    source_id: SourceId,
    source_consts: &ListOfLists<SourceId, (StrId, ConstId)>,
    imports: &ListOfLists<SourceId, FileImport>,
    scope: &mut HashMap<StrId, ConstId>,
) {
    scope.clear();
    for &(name, const_id) in &source_consts[source_id] {
        scope.insert(name, const_id);
    }
    for import in &imports[source_id] {
        match import.target_const {
            Some(const_name) => {
                let &(_, const_id) = source_consts[import.target_source]
                    .iter()
                    .find(|(name, _)| *name == const_name)
                    .expect("imported const not found");
                let prev = scope.insert(import.local_name, const_id);
                assert!(prev.is_none(), "name collision on import");
            }
            None => {
                for &(name, const_id) in &source_consts[import.target_source] {
                    let prev = scope.insert(name, const_id);
                    assert!(prev.is_none(), "name collision on glob import");
                }
            }
        }
    }
}
