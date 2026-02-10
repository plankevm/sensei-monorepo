pub use sensei_core::{
    DenseIndexSet, Idx, IndexVec, RelSlice, RelSliceMut, Span, index_vec, newtype_index,
};

newtype_index! {
    pub struct CasesBasicBlocksIdx;
    pub struct FunctionId;
    pub struct BasicBlockId;
    pub struct OperationIdx;
    pub struct DataId;
    pub struct DataOffset;
    pub struct LocalId;
    pub struct LocalIdx;
    pub struct LargeConstId;
    pub struct CasesId;
    pub struct StaticAllocId;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_index_size() {
        assert_eq!(std::mem::size_of::<BasicBlockId>(), 4);
        assert_eq!(std::mem::size_of::<Option<BasicBlockId>>(), 4);
        assert_eq!(std::mem::size_of::<OperationIdx>(), 4);
        assert_eq!(std::mem::size_of::<Option<OperationIdx>>(), 4);
        assert_eq!(std::mem::size_of::<DataOffset>(), 4);
        assert_eq!(std::mem::size_of::<Option<DataOffset>>(), 4);
        assert_eq!(std::mem::size_of::<LocalId>(), 4);
        assert_eq!(std::mem::size_of::<Option<LocalId>>(), 4);
        assert_eq!(std::mem::size_of::<LocalIdx>(), 4);
    }

    #[test]
    fn test_basic_block_id() {
        let idx = BasicBlockId::new(0);
        assert_eq!(idx.get(), 0);

        let idx = BasicBlockId::new(1);
        assert_eq!(idx.get(), 1);

        let idx = BasicBlockId::new(0xFFFF_FF00);
        assert_eq!(idx.get(), 0xFFFF_FF00);
    }

    #[test]
    fn test_dense_index_set() {
        let mut set: DenseIndexSet<BasicBlockId> = DenseIndexSet::new();
        assert!(!set.contains(BasicBlockId::new(0)));
        assert!(!set.contains(BasicBlockId::new(1)));
        assert!(!set.contains(BasicBlockId::new(2)));
        assert!(!set.contains(BasicBlockId::new(3)));

        assert!(set.add(BasicBlockId::new(2)));

        assert!(!set.contains(BasicBlockId::new(0)));
        assert!(!set.contains(BasicBlockId::new(1)));
        assert!(set.contains(BasicBlockId::new(2)));
        assert!(!set.contains(BasicBlockId::new(3)));

        assert!(!set.add(BasicBlockId::new(2)));

        assert!(!set.contains(BasicBlockId::new(0)));
        assert!(!set.contains(BasicBlockId::new(1)));
        assert!(set.contains(BasicBlockId::new(2)));
        assert!(!set.contains(BasicBlockId::new(3)));

        assert!(!set.contains(BasicBlockId::new(64)));
        assert!(!set.contains(BasicBlockId::new(65)));
        assert!(set.add(BasicBlockId::new(64)));
        assert!(set.add(BasicBlockId::new(65)));
        assert!(set.contains(BasicBlockId::new(64)));
        assert!(set.contains(BasicBlockId::new(65)));

        assert!(!set.contains(BasicBlockId::new(17)));
        assert!(!set.remove(BasicBlockId::new(17)));
        assert!(!set.contains(BasicBlockId::new(17)));

        assert!(set.remove(BasicBlockId::new(2)));
        assert!(!set.contains(BasicBlockId::new(2)));
        assert!(!set.remove(BasicBlockId::new(2)));
        assert!(!set.contains(BasicBlockId::new(2)));
    }
}
