pub use sensei_core::{index_vec, DenseIndexSet, IndexVec, RelSlice, RelSliceMut, Span, X32};

pub enum CasesBasicBlocksIndexMarker {}
pub enum FunctionIdMarker {}
pub enum BasicBlockIdMarker {}
pub enum OperationIndexMarker {}
pub enum DataIdMarker {}
pub enum DataOffsetMarker {}
pub enum LocalIdMarker {}
pub enum LocalIndexMarker {}
pub enum LargeConstIdMarker {}
pub enum CasesIdMarker {}
pub enum StaticAllocIdMarker {}

pub type CasesBasicBlocksIndex = X32<CasesBasicBlocksIndexMarker>;
pub type FunctionId = X32<FunctionIdMarker>;
pub type BasicBlockId = X32<BasicBlockIdMarker>;
pub type OperationIndex = X32<OperationIndexMarker>;
pub type DataId = X32<DataIdMarker>;
pub type DataOffset = X32<DataOffsetMarker>;
pub type LocalId = X32<LocalIdMarker>;
pub type LocalIndex = X32<LocalIndexMarker>;
pub type LargeConstId = X32<LargeConstIdMarker>;
pub type CasesId = X32<CasesIdMarker>;
pub type StaticAllocId = X32<StaticAllocIdMarker>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_index_size() {
        assert_eq!(std::mem::size_of::<BasicBlockId>(), 4);
        assert_eq!(std::mem::size_of::<Option<BasicBlockId>>(), 4);
        assert_eq!(std::mem::size_of::<OperationIndex>(), 4);
        assert_eq!(std::mem::size_of::<Option<OperationIndex>>(), 4);
        assert_eq!(std::mem::size_of::<DataOffset>(), 4);
        assert_eq!(std::mem::size_of::<Option<DataOffset>>(), 4);
        assert_eq!(std::mem::size_of::<LocalId>(), 4);
        assert_eq!(std::mem::size_of::<Option<LocalId>>(), 4);
        assert_eq!(std::mem::size_of::<LocalIndex>(), 4);
    }

    #[test]
    fn test_x32_basic() {
        let idx: BasicBlockId = X32::new(0);
        assert_eq!(idx.get(), 0);

        let idx: BasicBlockId = X32::new(1);
        assert_eq!(idx.get(), 1);

        let idx: BasicBlockId = X32::new(0xFFFF_FF00);
        assert_eq!(idx.get(), 0xFFFF_FF00);
    }

    #[test]
    fn test_dense_index_set() {
        let mut set: DenseIndexSet<BasicBlockIdMarker> = DenseIndexSet::new();
        assert!(!set.contains(X32::new(0)));
        assert!(!set.contains(X32::new(1)));
        assert!(!set.contains(X32::new(2)));
        assert!(!set.contains(X32::new(3)));

        assert!(set.add(X32::new(2)));

        assert!(!set.contains(X32::new(0)));
        assert!(!set.contains(X32::new(1)));
        assert!(set.contains(X32::new(2)));
        assert!(!set.contains(X32::new(3)));

        assert!(!set.add(X32::new(2)));

        assert!(!set.contains(X32::new(0)));
        assert!(!set.contains(X32::new(1)));
        assert!(set.contains(X32::new(2)));
        assert!(!set.contains(X32::new(3)));

        assert!(!set.contains(X32::new(64)));
        assert!(!set.contains(X32::new(65)));
        assert!(set.add(X32::new(64)));
        assert!(set.add(X32::new(65)));
        assert!(set.contains(X32::new(64)));
        assert!(set.contains(X32::new(65)));

        assert!(!set.contains(X32::new(17)));
        assert!(!set.remove(X32::new(17)));
        assert!(!set.contains(X32::new(17)));

        assert!(set.remove(X32::new(2)));
        assert!(!set.contains(X32::new(2)));
        assert!(!set.remove(X32::new(2)));
        assert!(!set.contains(X32::new(2)));
    }
}
