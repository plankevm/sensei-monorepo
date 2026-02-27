pub mod ast;
pub mod cst;
pub mod diagnostics;
pub mod error_report;
pub mod interner;
pub mod lexer;
pub mod module;
pub mod parser;
pub mod source;

pub use interner::{PlankInterner, StrId};

pub mod const_print;

#[cfg(test)]
pub mod tests;

/// Core crate assumption.
const _USIZE_AT_LEAST_U32: () = const {
    assert!(u32::BITS <= usize::BITS);
};
