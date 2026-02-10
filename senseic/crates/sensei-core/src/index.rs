use crate::span::IncIterable;
use std::{
    convert::TryFrom,
    fmt::Debug,
    num::NonZero,
    ops::{Add, AddAssign, Sub},
};

#[cold]
#[inline(never)]
#[cfg_attr(debug_assertions, track_caller)]
pub const fn panic_idx_overflow() -> ! {
    panic!("Index overflow: value exceeds maximum representable index");
}

pub trait Idx:
    Ord
    + Eq
    + Copy
    + Add<u32, Output = Self>
    + AddAssign<u32>
    + Sub<Self, Output = u32>
    + TryFrom<usize>
    + Debug
{
    fn from_raw(raw: NonZero<u32>) -> Self;
    fn to_raw(self) -> NonZero<u32>;

    fn max_value() -> Self {
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

    /// Returns the index as a `usize` for slice indexing.
    fn idx(self) -> usize {
        self.get() as usize
    }
}

#[macro_export]
macro_rules! newtype_index {
    () => {};
    ($(#[$attr:meta])* $vis:vis struct $name:ident; $($rest:tt)*) => {
        $(#[$attr])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(transparent)]
        #[allow(dead_code)]
        $vis struct $name(::core::num::NonZero<u32>);

        #[allow(dead_code)]
        impl $name {
            /// The zero index (representing logical index 0).
            pub const ZERO: Self = Self(::core::num::NonZero::new(1).unwrap());
            /// The maximum representable index.
            pub const MAX: Self = Self(::core::num::NonZero::new(u32::MAX).unwrap());
            /// Maximum value as usize for bounds checking.
            pub const MAX_USIZE: usize = u32::MAX as usize - 1;

        }

        impl $crate::Idx for $name {
            #[inline]
            fn from_raw(raw: ::core::num::NonZero<u32>) -> $name {
                $name(raw)
            }

            #[inline]
            fn to_raw(self) -> ::core::num::NonZero<u32> {
                self.0
            }
        }

        impl ::core::ops::Add<u32> for $name {
            type Output = Self;

            #[inline]
            fn add(self, rhs: u32) -> Self::Output {
                use $crate::Idx;
                Self::new(self.get().wrapping_add(rhs))
            }
        }

        impl ::core::ops::AddAssign<u32> for $name {
            #[inline]
            fn add_assign(&mut self, other: u32) {
                *self = *self + other;
            }
        }

        impl ::core::ops::Sub<$name> for $name {
            type Output = u32;

            #[inline]
            fn sub(self, rhs: $name) -> Self::Output {
                use $crate::Idx;
                self.get() - rhs.get()
            }
        }

        impl ::core::ops::Sub<u32> for $name {
            type Output = Self;

            #[inline]
            fn sub(self, rhs: u32) -> Self::Output {
                use $crate::Idx;
                Self::new(self.get().wrapping_sub(rhs))
            }
        }

        impl ::core::convert::TryFrom<usize> for $name {
            type Error = ();

            #[inline]
            fn try_from(value: usize) -> Result<Self, Self::Error> {
                if value > Self::MAX_USIZE {
                    return Err(());
                }
                // Safety: We just checked that value <= MAX_USIZE, so value + 1 won't overflow.
                Ok(Self(unsafe {
                    ::core::num::NonZero::new_unchecked((value as u32).wrapping_add(1))
                }))
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                use $crate::Idx;
                write!(f, "{}({})", ::core::stringify!($name), self.idx())
            }
        }

        impl ::core::fmt::Display for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                use $crate::Idx;
                write!(f, "{}", (*self).idx())
            }
        }

        $crate::newtype_index!($($rest)*);
    };
}

impl<I: Idx> IncIterable for I {
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
