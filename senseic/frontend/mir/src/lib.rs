use alloy_primitives::U256;
use sensei_core::{IndexVec, list_of_lists::ListOfLists, newtype_index};
use sensei_types::{TypeId, TypeInterner};

newtype_index! {
    pub struct FnId;
    pub struct BlockId;
    pub struct LocalId;
    pub struct ArgsId;
    pub struct BigNumId;
}

#[derive(Debug, Clone, Copy)]
pub enum Expr {
    LocalRef(LocalId),
    Bool(bool),
    Void,
    BigNum(BigNumId),
    Call { callee: FnId, args: ArgsId },
    FieldAccess { object: LocalId, field_index: u32 },
    StructLit { ty: TypeId, fields: ArgsId },
}

#[derive(Debug, Clone, Copy)]
pub enum Instruction {
    Set { local: LocalId, expr: Expr },
    Assign { target: LocalId, value: Expr },
    Eval(Expr),
    Return(Expr),
    If { condition: LocalId, then_block: BlockId, else_block: BlockId },
    While { condition_block: BlockId, body: BlockId },
}

#[derive(Debug, Clone, Copy)]
pub struct FnDef {
    pub body: BlockId,
    pub param_count: u32,
    pub return_type: TypeId,
}

#[derive(Debug)]
pub struct Mir {
    pub blocks: ListOfLists<BlockId, Instruction>,
    pub args: ListOfLists<ArgsId, LocalId>,
    pub big_nums: IndexVec<BigNumId, U256>,
    pub fns: IndexVec<FnId, FnDef>,
    pub fn_locals: ListOfLists<FnId, Option<TypeId>>,
    pub types: TypeInterner,
    pub init: BlockId,
    pub run: Option<BlockId>,
}
