use inturn::InternerSymbol;
use std::{hash::Hash, marker::PhantomData, num::NonZero};

#[repr(transparent)]
pub struct X32<M> {
    idx: NonZero<u32>,
    _marker: PhantomData<M>,
}

#[cold]
#[inline(never)]
#[cfg_attr(debug_assertions, track_caller)]
pub const fn panic_x32_overflow() -> ! {
    panic!("Overflowed 32-bits for an X32");
}

impl<M> X32<M> {
    pub const ZERO: X32<M> = X32::new(0);
    pub const MAX: X32<M> = X32::new(u32::MAX - 1);
    pub const MAX_USIZE: usize = Self::MAX.idx();

    #[inline]
    pub const fn try_new(value: u32) -> Option<X32<M>> {
        match NonZero::new(value.wrapping_add(1)) {
            Some(idx) => Some(X32 { idx, _marker: PhantomData }),
            None => None,
        }
    }

    /// Creates a new index by wrapping the `value`.
    ///
    /// # Panics
    /// Panics if `value + 1` overflows 32 bits.
    #[inline]
    pub const fn new(value: u32) -> X32<M> {
        match X32::try_new(value) {
            Some(x) => x,
            None => panic_x32_overflow(),
        }
    }

    /// # Safety
    /// `value + 1` must not overflow 32-bits.
    #[inline(always)]
    pub const unsafe fn new_unchecked(value: u32) -> X32<M> {
        let idx = unsafe {
            let inner = value.unchecked_add(1);
            std::num::NonZero::new_unchecked(inner)
        };
        X32 { idx, _marker: PhantomData }
    }

    #[inline(always)]
    pub const fn idx(self) -> usize {
        self.get() as usize
    }

    /// Gets the underlying index value.
    #[inline(always)]
    pub const fn get(self) -> u32 {
        // Safety: By definition `>= 1`.
        unsafe { self.idx.get().unchecked_sub(1) }
    }
}

impl<M> std::ops::Add<u32> for X32<M> {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        Self::new(self.get() + rhs)
    }
}

impl<M> std::ops::Sub<u32> for X32<M> {
    type Output = Self;

    fn sub(self, rhs: u32) -> Self::Output {
        Self::new(self.get() - rhs)
    }
}

impl<M> TryFrom<usize> for X32<M> {
    type Error = ();

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        unsafe {
            if value > Self::MAX_USIZE {
                return Err(());
            }
            Ok(Self::new_unchecked(value as u32))
        }
    }
}

const _OPTION_X32_SMALL: () = const {
    struct ExampleMarker;
    type Index = X32<ExampleMarker>;
    assert!(std::mem::size_of::<Option<Index>>() == 4);
    assert!(std::mem::size_of::<Index>() == 4);
};

impl<M> Hash for X32<M> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.idx.hash(state);
    }
}

impl<M> std::fmt::Debug for X32<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", std::any::type_name::<M>(), self.get())
    }
}

impl<M> InternerSymbol for X32<M> {
    fn try_from_usize(id: usize) -> Option<X32<M>> {
        u32::try_from(id).ok().and_then(X32::try_new)
    }

    #[inline]
    fn to_usize(self) -> usize {
        self.get() as usize
    }
}

impl<M> Clone for X32<M> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<M> Copy for X32<M> {}

impl<M> PartialEq for X32<M> {
    fn eq(&self, other: &Self) -> bool {
        self.idx == other.idx
    }
}

impl<M> Eq for X32<M> {}

impl<M> PartialOrd for X32<M> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<M> Ord for X32<M> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.idx.cmp(&other.idx)
    }
}
