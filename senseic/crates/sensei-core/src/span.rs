use crate::{Idx, newtype_index};

pub trait IncIterable: Eq + Ord {
    fn get_and_inc(&mut self) -> Self;
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

impl<I: Idx> std::fmt::Display for Span<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start.get(), self.end.get())
    }
}

impl<T> Span<T> {
    pub const fn new(start: T, end: T) -> Self {
        Self { start, end }
    }

    pub fn range(self) -> std::ops::Range<T> {
        self.start..self.end
    }
}

impl<T: Eq> Span<T> {
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

impl<I: Idx> Span<I> {
    pub fn dummy() -> Self {
        Self { start: I::max_value(), end: I::new(0) }
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
    newtype_index! {
        struct ExampleIdx;
    }
    assert!(std::mem::size_of::<Option<Span<ExampleIdx>>>() == 8);
};

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<I: Idx> ToUsize for I {
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

pub trait SpanLike {
    type Idx: Copy;
    fn start(&self) -> Self::Idx;
    fn end(&self) -> Self::Idx;
}

impl<T: Copy> SpanLike for Span<T> {
    type Idx = T;
    fn start(&self) -> T {
        self.start
    }
    fn end(&self) -> T {
        self.end
    }
}

impl<T: Copy> SpanLike for std::ops::Range<T> {
    type Idx = T;
    fn start(&self) -> T {
        self.start
    }
    fn end(&self) -> T {
        self.end
    }
}
