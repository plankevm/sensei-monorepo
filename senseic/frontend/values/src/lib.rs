mod bignum_interner;
mod type_interner;

use sensei_core::newtype_index;

newtype_index! {
    pub struct ValueId;
}

pub use bignum_interner::{BigNumId, BigNumInterner};
pub use type_interner::{StructExtraInfo, StructInfo, Type, TypeId, TypeInterner};
