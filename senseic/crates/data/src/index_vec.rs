use std::marker::PhantomData;

use crate::{Span, index::X32, span::IncIterable};
use allocator_api2::{
    alloc::{Allocator, Global},
    vec::Vec,
};

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
