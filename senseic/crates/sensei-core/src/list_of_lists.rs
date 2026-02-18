use crate::{Idx, IncIterable, IndexVec};
use allocator_api2::vec::Vec;

// WIP

#[derive(Debug, Clone)]
pub struct ListOfLists<I: Idx, T> {
    starts: IndexVec<I, u32>,
    values: Vec<T>,
}

pub struct ListOfListsPusher<'l, I: Idx, T>(&'l mut ListOfLists<I, T>);

impl<'l, I: Idx, T> ListOfListsPusher<'l, I, T> {
    pub fn push(&mut self, element: T) {
        self.0.values.push(element);
    }
}

impl<I: Idx, T> ListOfLists<I, T> {
    fn values_end(&self, index: I) -> usize {
        index
            .checked_add(1)
            .and_then(|ni| self.starts.get(ni).map(|&end| end as usize))
            .unwrap_or(self.values.len())
    }

    pub const fn new() -> Self {
        Self { starts: IndexVec::new(), values: Vec::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.starts.len() == 0
    }

    pub fn with_capacities(list_capacity: usize, total_values_capacity: usize) -> Self {
        Self {
            starts: IndexVec::with_capacity(list_capacity),
            values: Vec::with_capacity(total_values_capacity),
        }
    }

    pub fn push_with<F, R>(&mut self, f: F) -> (I, R)
    where
        F: FnOnce(ListOfListsPusher<'_, I, T>) -> R,
    {
        let start = u32::try_from(self.values.len()).unwrap();
        let res = f(ListOfListsPusher(self));
        let idx = self.starts.push(start);
        u32::try_from(self.values.len()).expect("exceeding maximum of 2^32-1 values");
        (idx, res)
    }

    pub fn push_iter(&mut self, iter: impl Iterator<Item = T>) -> I {
        let (idx, _) = self.push_with(|mut list| {
            iter.for_each(|element| list.push(element));
        });
        idx
    }

    pub fn iter(&self) -> impl Iterator<Item = &[T]> {
        let starts = self.starts.as_rel_slice();
        let ends =
            starts.iter().skip(1).map(|&end| end as usize).chain([self.values.len()].into_iter());
        starts.iter().copied().zip(ends).map(|(start, end)| &self.values[start as usize..end])
    }

    pub fn enumerate_idx(&self) -> impl Iterator<Item = (I, &[T])> {
        self.iter().scan(I::ZERO, |i, elements| Some((i.get_and_inc(), elements)))
    }

    pub fn len(&self) -> usize {
        self.starts.len()
    }
}

impl<I: Idx, T> std::ops::Index<I> for ListOfLists<I, T> {
    type Output = [T];

    fn index(&self, index: I) -> &Self::Output {
        let start = self.starts[index] as usize;
        let end = self.values_end(index);
        &self.values[start..end]
    }
}

impl<I: Idx, T> std::ops::IndexMut<I> for ListOfLists<I, T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        let start = self.starts[index] as usize;
        let end = self.values_end(index);
        &mut self.values[start..end]
    }
}

impl<I: Idx, T> Default for ListOfLists<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: Idx, T: Copy> ListOfLists<I, T> {
    pub fn push_copy_slice(&mut self, slice: &[T]) -> I {
        self.push_iter(slice.iter().copied())
    }
}
