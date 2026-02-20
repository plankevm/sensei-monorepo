---
name: data-structure
description: Mandatory use when editing or defining data structures in the compiler.
---

## Design Principles

### Prefer Indices Over References

When referencing elements within arenas/IndexVecs, store typed indices rather
than references. This avoids lifetime complexity and enables mutation.

### Use Spans for Contiguous Ranges

When storing a variable number of children/elements, prefer storing a `Span<I>`
pointing into a shared arena over `Vec<T>` per-parent.

### Never Manually Construct Indices

Never manually construct typed indices (e.g., `MyIdx::new(5)`). Instead, obtain
indices from collection operations:
- `.push()` returns the new element's index
- `.enumerate_idx()` yields `(I, &T)` pairs
- `.iter_idx()` yields indices only

This ensures indices always correspond to valid elements and prevents off-by-one
errors or stale index usage.

## Anti-Patterns

- ❌ Using `Vec<T>` when elements are referenced by index
- ❌ Using `usize` indices across different collections
- ❌ Storing `&T` references instead of typed indices
- ❌ Using `Range<I>` when `Span<I>` would allow `Copy`
- ❌ Manually constructing indices instead of obtaining from iterators/push

## Useful Libraries and Patterns

The `sensei_core` crate houses some foundational data structures & helpers to be
used when defining and structuring data.

### New Typed Indices

Define new indices by importing and using the `newtype_index` macro:

```rust
use sensei_core::{newtype_index};

newtype_index! {
    pub struct ExampleId;
    pub struct StorageIdx;
}
```

Newtyped indices are compact `u32` indices to prevent accidental mixup of
different IDs/indices. They are niche optimized such that `Option<NewtypedId>` &
`NewtypedId` fit into 4-bytes.

### `sensei_core::IndexVec<I, T>`

Similar to Rust's native `Vec` just that element access and iteration is
restricted to the associated index type for type safety. Favor `IndexVec` over
`Vec` unless using for stack/queue type purposes where you're not referencing
specific elements directly.

Use `.enumerate_idx()` to iterate over elements plus indices in a type-safe
manner. `.push` returns the new element's index. Other useful methods:
- `.enumerate_mut_idx`
- `.get`
- `.get_mut`
- `.len_idx`
- `.iter_idx` (iterate over indices only)

### `sensei_core::Span<T>`

More convenient version of `std::ops::Range`. Implements `Copy` if `T` is copy,
allowing containing structs to be `Copy`, but requires `.iter()` to iterate.

Instantiate with `Span::new`

### `sensei_core::DenseIndexSet<I>`

Type safe bit set that's indexed via `I`. Instantiate with `with_capacity`, `new` or `with_capacity_in_bits`.

Core methods:
- `set.contains(i: I) -> bool`
- `set.add(i: I) -> bool` (returns `true` if added, `false` if already present)
- `set.remove(i: I) -> bool` (returns `true` if removed, `false` if not within set)
- `set.clear()` (clears all elements, retains capacity)
