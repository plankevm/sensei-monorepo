use std::marker::PhantomData;

use crate::X32;

/// A dense bitset for storing sets of typed indices.
///
/// This is an efficient set implementation when indices are densely packed and the maximum
/// index is known or bounded. It uses a bit vector internally, where each bit represents
/// whether an index is present in the set.
#[derive(Debug, Clone)]
pub struct DenseIndexSet<M> {
    inner: Vec<usize>,
    _marker: PhantomData<M>,
}

impl<M> DenseIndexSet<M> {
    /// Creates a new empty `DenseIndexSet`.
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates a new `DenseIndexSet` with capacity for at least `bits` indices.
    #[inline]
    pub fn with_capacity_in_bits(bits: usize) -> Self {
        let words_capacity = bits.div_ceil(usize::BITS as usize);
        Self::with_capacity(words_capacity)
    }

    /// Creates a new `DenseIndexSet` with capacity for `capacity` words.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self { inner: Vec::with_capacity(capacity), _marker: PhantomData }
    }

    /// Clears all elements from the set, retaining the allocated capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.inner.fill(0);
    }

    /// Returns `true` if the set contains the given index.
    #[inline]
    pub fn contains(&self, i: X32<M>) -> bool {
        let idx = i.get();
        let bit = idx % usize::BITS;
        let word = idx / usize::BITS;
        self.inner.get(word as usize).is_some_and(|word| word & (1 << bit) != 0)
    }

    /// Adds an index to the set.
    ///
    /// Returns `true` if the index was newly added, or `false` if it was already present.
    pub fn add(&mut self, i: X32<M>) -> bool {
        let idx = i.get();
        let bit = idx % usize::BITS;
        let word = (idx / usize::BITS) as usize;

        if word >= self.inner.len() {
            let length_to_fit_word = word.checked_add(1).expect("overflow should be impossible");
            let additional = length_to_fit_word.saturating_sub(self.inner.len());
            self.inner.reserve(additional);
            self.inner.resize(self.inner.capacity(), 0);
        }

        // Safety: Just resized to ensure we have at least `word + 1` elements.
        let word = unsafe { self.inner.get_unchecked_mut(word) };
        let added = *word & (1 << bit) == 0;
        *word |= 1 << bit;
        debug_assert!(self.contains(i), "adding failed");
        added
    }

    /// Removes an index from the set.
    ///
    /// Returns `true` if the index was present and removed, or `false` if it wasn't in the set.
    pub fn remove(&mut self, i: X32<M>) -> bool {
        let idx = i.get();
        let bit = idx % usize::BITS;
        let word = (idx / usize::BITS) as usize;

        if word >= self.inner.len() {
            debug_assert!(!self.contains(i), "removing failed");
            return false;
        }

        // Safety: Just checked whether `word` was within bounds.
        let word = unsafe { self.inner.get_unchecked_mut(word) };
        let removing = *word & (1 << bit) != 0;
        *word &= !(1 << bit);
        debug_assert!(!self.contains(i), "removing failed");
        removing
    }
}

impl<M> Default for DenseIndexSet<M> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    enum TestIdx {}

    #[test]
    fn test_new_empty() {
        let set: DenseIndexSet<TestIdx> = DenseIndexSet::new();
        assert!(!set.contains(X32::new(0)));
        assert!(!set.contains(X32::new(100)));
    }

    #[test]
    fn test_add_and_contains() {
        let mut set: DenseIndexSet<TestIdx> = DenseIndexSet::new();

        assert!(set.add(X32::new(5)));
        assert!(set.contains(X32::new(5)));
        assert!(!set.contains(X32::new(4)));
        assert!(!set.contains(X32::new(6)));

        // Adding again should return false
        assert!(!set.add(X32::new(5)));
        assert!(set.contains(X32::new(5)));
    }

    #[test]
    fn test_remove() {
        let mut set: DenseIndexSet<TestIdx> = DenseIndexSet::new();

        set.add(X32::new(10));
        assert!(set.contains(X32::new(10)));

        assert!(set.remove(X32::new(10)));
        assert!(!set.contains(X32::new(10)));

        // Removing non-existent element should return false
        assert!(!set.remove(X32::new(10)));
        assert!(!set.remove(X32::new(999)));
    }

    #[test]
    fn test_clear() {
        let mut set: DenseIndexSet<TestIdx> = DenseIndexSet::new();

        set.add(X32::new(1));
        set.add(X32::new(10));
        set.add(X32::new(100));

        set.clear();

        assert!(!set.contains(X32::new(1)));
        assert!(!set.contains(X32::new(10)));
        assert!(!set.contains(X32::new(100)));
    }

    #[test]
    fn test_large_indices() {
        let mut set: DenseIndexSet<TestIdx> = DenseIndexSet::new();

        // Test indices across word boundaries
        assert!(set.add(X32::new(0)));
        assert!(set.add(X32::new(63)));
        assert!(set.add(X32::new(64)));
        assert!(set.add(X32::new(65)));
        assert!(set.add(X32::new(1000)));

        assert!(set.contains(X32::new(0)));
        assert!(set.contains(X32::new(63)));
        assert!(set.contains(X32::new(64)));
        assert!(set.contains(X32::new(65)));
        assert!(set.contains(X32::new(1000)));

        assert!(!set.contains(X32::new(1)));
        assert!(!set.contains(X32::new(62)));
        assert!(!set.contains(X32::new(66)));
        assert!(!set.contains(X32::new(999)));
    }

    #[test]
    fn test_with_capacity() {
        let set: DenseIndexSet<TestIdx> = DenseIndexSet::with_capacity_in_bits(256);
        assert!(!set.contains(X32::new(0)));
        assert!(!set.contains(X32::new(255)));
    }
}
