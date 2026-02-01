use std::marker::PhantomData;

use crate::{
    Span,
    index::X32,
    span::{IncIterable, SpanLike, ToUsize},
};
use allocator_api2::{
    alloc::{Allocator, Global},
    vec::Vec,
};

/// A borrowed slice with an associated offset index for absolute indexing.
///
/// This type maintains the original absolute indices from the parent `IndexVec`, allowing
/// indexing with absolute `X32<I>` indices rather than relative offsets.
///
/// Created via `IndexVec::rel_slice()` or `IndexVec::rel_slice_mut()`.
#[derive(Clone, Copy)]
pub struct RelSlice<'a, I, T> {
    offset: u32,
    data: &'a [T],
    _marker: PhantomData<I>,
}

impl<'a, I, T> RelSlice<'a, I, T> {
    /// Creates a new `RelSlice` from an offset and slice reference.
    #[inline]
    pub fn new(offset: X32<I>, data: &'a [T]) -> Self {
        Self { offset: offset.get(), data, _marker: PhantomData }
    }

    /// Returns the starting offset index of this slice in the original `IndexVec`.
    #[inline]
    pub fn start_idx(&self) -> X32<I> {
        X32::new(self.offset)
    }

    /// Returns the number of elements in this slice.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if this slice has no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Returns a reference to the underlying slice.
    #[inline]
    pub fn as_raw_slice(&self) -> &'a [T] {
        self.data
    }

    /// Returns an iterator over references to the elements.
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'a, T> {
        self.data.iter()
    }

    /// Gets a reference to an element by absolute index, or `None` if out of bounds.
    #[inline]
    pub fn get(&self, index: X32<I>) -> Option<&'a T> {
        let relative = index.get().checked_sub(self.offset)?;
        self.data.get(relative as usize)
    }

    /// Returns a `RelSlice` for a given span or range, preserving absolute indices.
    pub fn index(&self, span: impl SpanLike<Idx = X32<I>>) -> RelSlice<'_, I, T> {
        let start = span.start();
        let end = span.end();
        let rel_start = (start.get() - self.offset) as usize;
        let rel_end = (end.get() - self.offset) as usize;
        RelSlice::new(start, &self.data[rel_start..rel_end])
    }
}

impl<I, T> std::ops::Index<X32<I>> for RelSlice<'_, I, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: X32<I>) -> &Self::Output {
        let relative = index.get() - self.offset;
        &self.data[relative as usize]
    }
}

impl<I, T: std::fmt::Debug> std::fmt::Debug for RelSlice<'_, I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RelSlice").field("offset", &self.offset).field("data", &self.data).finish()
    }
}

impl<'a, I, T> IntoIterator for RelSlice<'a, I, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, I, T> IntoIterator for &'a RelSlice<'_, I, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.data.iter()
    }
}

/// A mutably borrowed slice with an associated offset index for absolute indexing.
///
/// This type maintains the original absolute indices from the parent `IndexVec`, allowing
/// indexing with absolute `X32<I>` indices rather than relative offsets.
///
/// Created via `IndexVec::rel_slice_mut()`.
pub struct RelSliceMut<'a, I, T> {
    offset: u32,
    data: &'a mut [T],
    _marker: PhantomData<I>,
}

impl<'a, I, T> RelSliceMut<'a, I, T> {
    /// Creates a new `RelSliceMut` from an offset and mutable slice reference.
    #[inline]
    pub fn new(offset: X32<I>, data: &'a mut [T]) -> Self {
        Self { offset: offset.get(), data, _marker: PhantomData }
    }

    /// Returns the starting offset index of this slice in the original `IndexVec`.
    #[inline]
    pub fn start_idx(&self) -> X32<I> {
        X32::new(self.offset)
    }

    /// Returns the number of elements in this slice.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if this slice has no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Returns a reference to the underlying slice.
    #[inline]
    pub fn as_raw_slice(&self) -> &[T] {
        self.data
    }

    /// Returns a mutable reference to the underlying slice.
    #[inline]
    pub fn as_raw_slice_mut(&mut self) -> &mut [T] {
        self.data
    }

    /// Converts this into the underlying mutable slice.
    #[inline]
    pub fn into_raw_slice(self) -> &'a mut [T] {
        self.data
    }

    /// Returns an iterator over references to the elements.
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.data.iter()
    }

    /// Returns an iterator over mutable references to the elements.
    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.data.iter_mut()
    }

    /// Gets a reference to an element by absolute index, or `None` if out of bounds.
    #[inline]
    pub fn get(&self, index: X32<I>) -> Option<&T> {
        let relative = index.get().checked_sub(self.offset)?;
        self.data.get(relative as usize)
    }

    /// Gets a mutable reference to an element by absolute index, or `None` if out of bounds.
    #[inline]
    pub fn get_mut(&mut self, index: X32<I>) -> Option<&mut T> {
        let relative = index.get().checked_sub(self.offset)?;
        self.data.get_mut(relative as usize)
    }

    /// Reborrows this as an immutable `RelSlice`.
    #[inline]
    pub fn as_rel_slice(&self) -> RelSlice<'_, I, T> {
        RelSlice { offset: self.offset, data: self.data, _marker: PhantomData }
    }

    /// Returns a `RelSlice` for a given span or range, preserving absolute indices.
    pub fn index(&self, span: impl SpanLike<Idx = X32<I>>) -> RelSlice<'_, I, T> {
        let start = span.start();
        let end = span.end();
        let rel_start = (start.get() - self.offset) as usize;
        let rel_end = (end.get() - self.offset) as usize;
        RelSlice::new(start, &self.data[rel_start..rel_end])
    }

    /// Returns a `RelSliceMut` for a given span or range, preserving absolute indices.
    pub fn index_mut(&mut self, span: impl SpanLike<Idx = X32<I>>) -> RelSliceMut<'_, I, T> {
        let start = span.start();
        let end = span.end();
        let rel_start = (start.get() - self.offset) as usize;
        let rel_end = (end.get() - self.offset) as usize;
        RelSliceMut::new(start, &mut self.data[rel_start..rel_end])
    }
}

impl<I, T> std::ops::Index<X32<I>> for RelSliceMut<'_, I, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: X32<I>) -> &Self::Output {
        let relative = index.get() - self.offset;
        &self.data[relative as usize]
    }
}

impl<I, T> std::ops::IndexMut<X32<I>> for RelSliceMut<'_, I, T> {
    #[inline]
    fn index_mut(&mut self, index: X32<I>) -> &mut Self::Output {
        let relative = index.get() - self.offset;
        &mut self.data[relative as usize]
    }
}

impl<I, T: std::fmt::Debug> std::fmt::Debug for RelSliceMut<'_, I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RelSliceMut")
            .field("offset", &self.offset)
            .field("data", &self.data)
            .finish()
    }
}

impl<'a, I, T> IntoIterator for RelSliceMut<'a, I, T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.data.iter_mut()
    }
}

pub struct IndexVec<IdxMarker, T, A: Allocator = Global> {
    pub raw: Vec<T, A>,
    _index: PhantomData<IdxMarker>,
}

impl<I, T> Default for IndexVec<I, T, Global> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I, T> IndexVec<I, T, Global> {
    pub fn new() -> Self {
        Self::from_raw(Vec::new())
    }

    /// Constructs a new, empty `IndexVec` with at least the specified capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::from_raw(Vec::with_capacity(capacity))
    }

    /// Constructs an `IndexVec` from a standard `Vec`.
    #[inline]
    pub fn from_vec(vec: std::vec::Vec<T>) -> Self {
        Self { raw: Vec::from_iter(vec), _index: PhantomData }
    }
}

impl<I, T, A: Allocator> IndexVec<I, T, A> {
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self::from_raw(Vec::with_capacity_in(capacity, alloc))
    }
    pub fn new_in(alloc: A) -> Self {
        Self::from_raw(Vec::new_in(alloc))
    }

    pub fn from_raw(raw: Vec<T, A>) -> Self {
        Self { raw, _index: PhantomData }
    }

    pub fn push(&mut self, element: T) -> X32<I> {
        let new_idx = X32::try_from(self.len()).expect("holds more x32::MAX elements");
        self.raw.push(element);
        new_idx
    }

    pub fn enumerate_idx(&self) -> impl Iterator<Item = (X32<I>, &T)> {
        self.iter().scan(X32::ZERO, |idx, element| Some((idx.get_and_inc(), element)))
    }

    pub fn enumerate_mut_idx(&mut self) -> impl Iterator<Item = (X32<I>, &mut T)> {
        self.iter_mut().scan(X32::ZERO, |idx, element| Some((idx.get_and_inc(), element)))
    }

    pub fn get(&self, index: X32<I>) -> Option<&T> {
        self.raw.get(index.idx())
    }

    pub fn get_mut(&mut self, index: X32<I>) -> Option<&mut T> {
        self.raw.get_mut(index.idx())
    }

    /// Returns the index that will be assigned to the next element pushed.
    #[inline]
    pub fn next_idx(&self) -> X32<I> {
        X32::try_from(self.len()).expect("IndexVec holds more than X32::MAX elements")
    }

    /// Returns the length as a typed index.
    #[inline]
    pub fn len_idx(&self) -> X32<I> {
        self.next_idx()
    }

    /// Returns a `RelSlice` for the given span or range, preserving absolute indices.
    #[inline]
    pub fn rel_slice(&self, span: impl SpanLike<Idx = X32<I>>) -> RelSlice<'_, I, T> {
        let start = span.start();
        let end = span.end();
        RelSlice::new(start, &self.raw[start.to_usize()..end.to_usize()])
    }

    /// Returns a `RelSliceMut` for the given span, preserving absolute indices.
    #[inline]
    pub fn rel_slice_mut(&mut self, span: impl SpanLike<Idx = X32<I>>) -> RelSliceMut<'_, I, T> {
        let start = span.start();
        let end = span.end();
        RelSliceMut::new(start, &mut self.raw[start.to_usize()..end.to_usize()])
    }

    /// Returns a `RelSlice` for the entire Vec, preserving absolute indices.
    #[inline]
    pub fn as_rel_slice(&self) -> RelSlice<'_, I, T> {
        RelSlice::new(X32::new(0), &self.raw)
    }

    /// Returns a `RelSliceMut` for the entire Vec, preserving absolute indices.
    #[inline]
    pub fn as_rel_slice_mut(&mut self) -> RelSliceMut<'_, I, T> {
        RelSliceMut::new(X32::new(0), &mut self.raw)
    }

    /// Returns a reference to the underlying slice.
    #[inline]
    pub fn as_raw_slice(&self) -> &[T] {
        self.raw.as_slice()
    }

    /// Returns a mutable reference to the underlying slice.
    #[inline]
    pub fn as_raw_slice_mut(&mut self) -> &mut [T] {
        self.raw.as_mut_slice()
    }

    /// Returns a mutable reference to the underlying Vec.
    #[inline]
    pub fn as_mut_vec(&mut self) -> &mut Vec<T, A> {
        &mut self.raw
    }
}

impl<I, T: std::fmt::Debug, A: Allocator> std::fmt::Debug for IndexVec<I, T, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.raw.fmt(f)
    }
}

impl<I, T: Clone, A: Allocator + Clone> Clone for IndexVec<I, T, A> {
    fn clone(&self) -> Self {
        Self { raw: self.raw.clone(), _index: PhantomData }
    }
}

impl<I, T> FromIterator<T> for IndexVec<I, T> {
    fn from_iter<IntoIter: IntoIterator<Item = T>>(iter: IntoIter) -> Self {
        Self::from_raw(Vec::from_iter(iter))
    }
}

impl<I, T, A: Allocator> std::ops::Deref for IndexVec<I, T, A> {
    type Target = Vec<T, A>;

    fn deref(&self) -> &Self::Target {
        &self.raw
    }
}

impl<I, T, A: Allocator> std::ops::DerefMut for IndexVec<I, T, A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.raw
    }
}

impl<I, T, A: Allocator> std::ops::Index<X32<I>> for IndexVec<I, T, A> {
    type Output = T;

    fn index(&self, index: X32<I>) -> &Self::Output {
        &self.raw[index.idx()]
    }
}

impl<I, T, A: Allocator> std::ops::IndexMut<X32<I>> for IndexVec<I, T, A> {
    fn index_mut(&mut self, index: X32<I>) -> &mut Self::Output {
        &mut self.raw[index.idx()]
    }
}

impl<I, T, A: Allocator> std::ops::Index<Span<X32<I>>> for IndexVec<I, T, A> {
    type Output = [T];

    fn index(&self, span: Span<X32<I>>) -> &Self::Output {
        &self.raw[span.usize_range()]
    }
}

impl<I, T, A: Allocator> std::ops::IndexMut<Span<X32<I>>> for IndexVec<I, T, A> {
    fn index_mut(&mut self, span: Span<X32<I>>) -> &mut Self::Output {
        &mut self.raw[span.usize_range()]
    }
}

impl<I, T, A: Allocator> std::ops::Index<std::ops::Range<X32<I>>> for IndexVec<I, T, A> {
    type Output = [T];

    fn index(&self, range: std::ops::Range<X32<I>>) -> &Self::Output {
        &self.raw[range.start.idx()..range.end.idx()]
    }
}

impl<I, T, A: Allocator> std::ops::IndexMut<std::ops::Range<X32<I>>> for IndexVec<I, T, A> {
    fn index_mut(&mut self, range: std::ops::Range<X32<I>>) -> &mut Self::Output {
        &mut self.raw[range.start.idx()..range.end.idx()]
    }
}

/// Creates an `IndexVec` containing the given elements.
///
/// `index_vec!` allows `IndexVec`s to be defined with the same syntax as the standard `vec![]`
/// macro.
///
/// # Examples
///
/// ```
/// use sensei_core::{index_vec, IndexVec, X32};
///
/// enum MyIdx {}
///
/// let v: IndexVec<MyIdx, i32> = index_vec![1, 2, 3];
/// assert_eq!(v.len(), 3);
///
/// let v: IndexVec<MyIdx, i32> = index_vec![0; 5];
/// assert_eq!(v.len(), 5);
/// ```
#[macro_export]
macro_rules! index_vec {
    () => {
        $crate::IndexVec::new()
    };
    ($elem:expr; $n:expr) => {
        $crate::IndexVec::from_vec(vec![$elem; $n])
    };
    ($($elem:expr),+ $(,)?) => {
        $crate::IndexVec::from_vec(vec![$($elem),+])
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    enum TestIdx {}

    #[test]
    fn test_index_vec_basic() {
        let mut v: IndexVec<TestIdx, i32> = IndexVec::new();
        assert!(v.is_empty());

        let idx0 = v.push(10);
        let idx1 = v.push(20);
        let idx2 = v.push(30);

        assert_eq!(idx0, X32::new(0));
        assert_eq!(idx1, X32::new(1));
        assert_eq!(idx2, X32::new(2));

        assert_eq!(v[idx0], 10);
        assert_eq!(v[idx1], 20);
        assert_eq!(v[idx2], 30);

        assert_eq!(v.len(), 3);
        assert_eq!(v.next_idx(), X32::new(3));
        assert_eq!(v.len_idx(), X32::new(3));
    }

    #[test]
    fn test_index_vec_macro() {
        let v: IndexVec<TestIdx, i32> = index_vec![1, 2, 3];
        assert_eq!(v.len(), 3);
        assert_eq!(v[X32::new(0)], 1);
        assert_eq!(v[X32::new(1)], 2);
        assert_eq!(v[X32::new(2)], 3);

        let v: IndexVec<TestIdx, i32> = index_vec![42; 5];
        assert_eq!(v.len(), 5);
        for i in 0..5 {
            assert_eq!(v[X32::new(i)], 42);
        }

        let v: IndexVec<TestIdx, i32> = index_vec![];
        assert!(v.is_empty());
    }

    #[test]
    fn test_rel_slice() {
        let v: IndexVec<TestIdx, i32> = index_vec![10, 20, 30, 40, 50];

        let span = Span::new(X32::<TestIdx>::new(1), X32::new(4));
        let rel = v.rel_slice(span);

        assert_eq!(rel.len(), 3);
        assert_eq!(rel.start_idx(), X32::new(1));

        assert_eq!(rel[X32::new(1)], 20);
        assert_eq!(rel[X32::new(2)], 30);
        assert_eq!(rel[X32::new(3)], 40);

        assert_eq!(rel.get(X32::new(0)), None);
        assert_eq!(rel.get(X32::new(1)), Some(&20));
        assert_eq!(rel.get(X32::new(4)), None);

        let raw = rel.as_raw_slice();
        assert_eq!(raw, &[20, 30, 40]);
    }

    #[test]
    fn test_rel_slice_mut() {
        let mut v: IndexVec<TestIdx, i32> = index_vec![10, 20, 30, 40, 50];

        let span = Span::new(X32::<TestIdx>::new(1), X32::new(4));
        let mut rel = v.rel_slice_mut(span);

        rel[X32::new(2)] = 300;
        assert_eq!(rel[X32::new(2)], 300);
        assert_eq!(v[X32::new(2)], 300);
    }

    #[test]
    fn test_enumerate_idx() {
        let v: IndexVec<TestIdx, &str> = index_vec!["a", "b", "c"];

        let collected: Vec<_> = v.enumerate_idx().collect();
        assert_eq!(collected.len(), 3);
        assert_eq!(collected[0], (X32::new(0), &"a"));
        assert_eq!(collected[1], (X32::new(1), &"b"));
        assert_eq!(collected[2], (X32::new(2), &"c"));
    }

    #[test]
    fn test_range_indexing() {
        let v: IndexVec<TestIdx, i32> = index_vec![10, 20, 30, 40, 50];

        let slice = &v[X32::<TestIdx>::new(1)..X32::new(4)];
        assert_eq!(slice, &[20, 30, 40]);
    }
}
