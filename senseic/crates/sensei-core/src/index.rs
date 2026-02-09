use crate::span::IncIterable;
use std::{
    num::NonZero,
    ops::{Add, AddAssign},
};

#[cold]
#[inline(never)]
#[cfg_attr(debug_assertions, track_caller)]
pub const fn panic_idx_overflow() -> ! {
    panic!("Overflowed 32-bits for an X32");
}

/// Safety: Implementor guarantees that their implementations of `from_raw` & `to_raw` are
/// injective. Meaning for all `x: Self`, `from_raw(to_raw(x)) == x`.
pub unsafe trait IdxInner: Ord + Eq + Copy + Add<u32> + AddAssign<u32> {
    fn from_raw(raw: NonZero<u32>) -> Self;
    fn to_raw(self) -> NonZero<u32>;
}

#[macro_export]
macro_rules! newtype_index {
    () => {};
    ($(#[$attr:meta])* struct $name:ident; $($rest:tt)*) => {
        $crate::newtype_index! {
            $(#[$attr])*
            pub(self) struct $name;
            $($rest)*
        }
    };
    ($(#[$attr:meta])* $vis:vis struct $name:ident; $($rest:tt)*) => {
        $(#[$attr])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(transparent)]
        $vis struct $name(::core::num::NonZero<u32>);

        unsafe impl $crate::index::IdxInner for $name {
            fn from_raw(raw: ::core::num::NonZero<u32>) -> $name {
                $name(raw)
            }

            fn to_raw(self) ->::core::num::NonZero<u32> {
                self.0
            }
        }

        impl ::core::ops::Add<u32> for $name {
            type Output = Self;

            fn add(self, rhs: u32) -> Self::Output {
                use $crate::Idx;
                Self::new(self.get().wrapping_add(rhs))
            }
        }

        impl ::core::ops::AddAssign<u32> for $name {
            fn add_assign(&mut self, other: u32) {
                *self = *self + other;
            }
        }

        impl ::core::ops::Sub<$name> for $name {
            type Output = u32;

            fn sub(self, rhs: $name) -> Self::Output {
                use $crate::Idx;
                self.get() - rhs.get()
            }
        }

        $crate::newtype_index!($($rest)*);
    };
}

pub trait Idx: Eq + Copy {
    fn max() -> Self;
    fn new(x: u32) -> Self;
    fn get(self) -> u32;
}

impl<I: IdxInner> Idx for I {
    fn max() -> Self {
        Self::new(u32::MAX - 1)
    }

    fn new(x: u32) -> Self {
        let nz = NonZero::new(x.wrapping_add(1)).unwrap_or_else(|| panic_idx_overflow());
        Self::from_raw(nz)
    }

    fn get(self) -> u32 {
        // Safety: `NonZero<u32>` guarantees `.get()` yields a value that's at least 1.
        unsafe { self.to_raw().get().unchecked_sub(1) }
    }
}

impl<I: IdxInner> IncIterable for I {
    #[inline(always)]
    fn get_and_inc(&mut self) -> Self {
        let current = *self;
        *self += 1;
        current
    }
}

#[cfg(test)]
mod tests {
    newtype_index! {
        pub struct TestIdx;
    }
}
