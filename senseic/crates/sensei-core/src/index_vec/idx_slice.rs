use std::marker::PhantomData;

use crate::Idx;

pub struct IndexSlice<I: Idx, T> {
    _idx: PhantomData<I>,
    inner: [T],
}

impl<I: Idx, T> IndexSlice<I, T> {}

impl<I: Idx, T> std::ops::Index<I> for IndexSlice<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        &self.inner[index.idx()]
    }
}

impl<I: Idx, T> std::ops::IndexMut<I> for IndexSlice<I, T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.inner[index.idx()]
    }
}
