use crate::index::X32;

pub trait IncIterable: Eq + Ord {
    fn get_and_inc(&mut self) -> Self;
}

impl<M> IncIterable for X32<M> {
    #[inline(always)]
    fn get_and_inc(&mut self) -> Self {
        let current = *self;
        *self = *self + 1;
        current
    }
}

impl IncIterable for u32 {
    fn get_and_inc(&mut self) -> Self {
        let x = *self;
        *self += 1;
        x
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span<T> {
    pub start: T,
    pub end: T,
}

impl<T> Span<T> {
    pub const fn new(start: T, end: T) -> Self {
        Self { start, end }
    }

    pub fn range(self) -> std::ops::Range<T> {
        self.start..self.end
    }
}

impl<M> Span<X32<M>> {
    pub const fn dummy() -> Self {
        Self { start: X32::MAX, end: X32::ZERO }
    }

    pub fn is_dummy(self) -> bool {
        self == Self::dummy()
    }
}

impl<T: IncIterable> Span<T> {
    pub fn iter(self) -> IncIterator<T> {
        let Self { start, end } = self;
        IncIterator { start, end }
    }
}

const _SPAN_OPTION_SIZE: () = const {
    struct ExampleMarker;
    type Index = X32<ExampleMarker>;
    assert!(std::mem::size_of::<Option<Span<Index>>>() == 8);
};

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<M> ToUsize for X32<M> {
    fn to_usize(self) -> usize {
        self.get() as usize
    }
}

impl ToUsize for usize {
    fn to_usize(self) -> usize {
        self
    }
}

impl ToUsize for u32 {
    fn to_usize(self) -> usize {
        self as usize
    }
}

impl ToUsize for u16 {
    fn to_usize(self) -> usize {
        self as usize
    }
}

impl ToUsize for u8 {
    fn to_usize(self) -> usize {
        self as usize
    }
}

impl<T: ToUsize> Span<T> {
    pub fn usize_range(self) -> std::ops::Range<usize> {
        self.start.to_usize()..self.end.to_usize()
    }
}

#[derive(Debug, Clone)]
pub struct IncIterator<T: IncIterable> {
    start: T,
    end: T,
}

impl<T: IncIterable> Iterator for IncIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            return None;
        }
        Some(self.start.get_and_inc())
    }
}
