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
    + Sub<u32, Output = Self>
    + TryFrom<usize>
    + Debug
{
    const ZERO: Self;
    const MAX: Self;

    fn from_raw(raw: NonZero<u32>) -> Self;
    fn to_raw(self) -> NonZero<u32>;

    fn max_value() -> Self {
        Self::from_raw(NonZero::new(u32::MAX).unwrap())
    }

    fn get(self) -> u32 {
        // Safety: `NonZero<u32>` guarantees `.get()` yields a value that's at least 1.
        unsafe { self.to_raw().get().unchecked_sub(1) }
    }

    /// Returns the index as a `usize` for slice indexing.
    fn idx(self) -> usize {
        self.get() as usize
    }

    fn checked_add(self, b: u32) -> Option<Self> {
        let a = self.to_raw().get();
        // Safety: Successful `checked_add` guarantees `c >= a` and `a > 0` therefore `c > 0`.
        a.checked_add(b).map(|c| Self::from_raw(unsafe { NonZero::new_unchecked(c) }))
    }
}

#[macro_export]
macro_rules! newtype_index {
    () => {};
    ($(#[$attr:meta])* $vis:vis struct $name:ident; $($rest:tt)*) => {
        $(#[$attr])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(transparent)]
        $vis struct $name(::core::num::NonZero<u32>);

        impl $name {
            /// Maximum value as usize for bounds checking.
            $vis const MAX_USIZE: usize = u32::MAX as usize - 1;

            $vis const fn new(x: u32) -> Self {
                use ::core::num::NonZero;
                match NonZero::new(x.wrapping_add(1)) {
                    Some(nz) => Self(nz),
                    None => $crate::index::panic_idx_overflow()
                }
            }

            #[allow(dead_code)]
            $vis const fn try_new(x: u32) -> Option<Self> {
                match ::core::num::NonZero::new(x.wrapping_add(1)) {
                    Some(nz) => Some(Self(nz)),
                    None => None
                }
            }

            #[allow(dead_code)]
            $vis const fn const_get(self) -> u32 {
                // Safety: `NonZero<u32>` guarantees `.get()` yields a value that's at least 1.
                unsafe { self.0.get().unchecked_sub(1) }
            }
        }

        impl $crate::Idx for $name {
            const ZERO: Self = Self::new(0);
            const MAX: Self = Self(::core::num::NonZero::new(u32::MAX).unwrap());

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

        impl ::core::default::Default for $name {
            fn default() -> Self {
                Self::new(0)
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
    use super::*;

    newtype_index! {
        pub struct TestIdx;
    }

    #[test]
    fn test_idx_basic_operations() {
        let idx = TestIdx::new(0);
        assert_eq!(idx.get(), 0);
        assert_eq!(idx.idx(), 0);

        let idx = TestIdx::new(42);
        assert_eq!(idx.get(), 42);
        assert_eq!(idx.idx(), 42);
    }

    #[test]
    fn test_idx_arithmetic() {
        let a = TestIdx::new(10);
        let b = TestIdx::new(3);

        assert_eq!((a - b), 7);
        assert_eq!((a + 5).get(), 15);
        assert_eq!((a - 2).get(), 8);

        let mut c = TestIdx::new(5);
        c += 3;
        assert_eq!(c.get(), 8);
    }

    #[test]
    fn test_idx_ordering() {
        let a = TestIdx::new(5);
        let b = TestIdx::new(10);
        let c = TestIdx::new(5);

        assert!(a < b);
        assert!(b > a);
        assert_eq!(a, c);
    }

    #[test]
    fn test_idx_try_from_usize() {
        let idx: Result<TestIdx, _> = TestIdx::try_from(100usize);
        assert!(idx.is_ok());
        assert_eq!(idx.unwrap().get(), 100);

        let too_large: Result<TestIdx, _> = TestIdx::try_from(usize::MAX);
        assert!(too_large.is_err());
    }

    #[test]
    fn test_idx_try_new() {
        assert!(TestIdx::try_new(0).is_some());
        assert!(TestIdx::try_new(1000).is_some());
        assert!(TestIdx::try_new(u32::MAX - 1).is_some());
        assert!(TestIdx::try_new(u32::MAX).is_none());
    }

    #[test]
    fn test_idx_constants() {
        assert_eq!(TestIdx::ZERO.get(), 0);
        assert_eq!(TestIdx::MAX.get(), u32::MAX - 1);
        assert_eq!(TestIdx::max_value().get(), u32::MAX - 1);
    }

    #[test]
    fn test_idx_from_raw() {
        let raw = NonZero::new(5).unwrap();
        let idx = TestIdx::from_raw(raw);
        assert_eq!(idx.to_raw(), raw);
        assert_eq!(idx.get(), 4);
    }

    #[test]
    fn test_idx_default() {
        let idx = TestIdx::default();
        assert_eq!(idx, TestIdx::ZERO);
        assert_eq!(idx.get(), 0);
    }

    #[test]
    fn test_idx_debug_display() {
        let idx = TestIdx::new(42);
        assert_eq!(format!("{:?}", idx), "TestIdx(42)");
        assert_eq!(format!("{}", idx), "42");
    }

    #[test]
    fn test_idx_inc_iterable() {
        let mut idx = TestIdx::new(5);
        assert_eq!(idx.get_and_inc().get(), 5);
        assert_eq!(idx.const_get(), 6);
        assert_eq!(idx.get_and_inc().get(), 6);
        assert_eq!(idx.const_get(), 7);
    }
}
