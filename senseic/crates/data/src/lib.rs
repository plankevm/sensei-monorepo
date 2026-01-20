pub mod bigint;
pub mod index;
pub mod index_vec;
pub mod must_use;
pub mod span;

pub use crate::{index::X32, index_vec::IndexVec, span::Span};

/// Alias denoting an arena allocated `T`.
pub type ABox<'arena, T> = &'arena mut T;

/// Core crate assumption.
const _USIZE_AT_LEAST_U32: () = const {
    assert!(u32::BITS <= usize::BITS);
};
