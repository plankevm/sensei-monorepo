use sensei_core::newtype_index;

pub use sensei_core::intern::StringInterner;

pub mod ast;
pub mod cst;
pub mod diagnostics;
pub mod error_report;
pub mod lexer;
pub mod parser;

pub mod const_print;

#[cfg(test)]
pub mod tests;

newtype_index! {
    /// String ID
    pub struct StrId;
}

/// Core crate assumption.
const _USIZE_AT_LEAST_U32: () = const {
    assert!(u32::BITS <= usize::BITS);
};
