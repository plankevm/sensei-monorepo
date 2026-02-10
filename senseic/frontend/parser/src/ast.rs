use inturn::Interner;
use sensei_core::{Idx, newtype_index};

newtype_index! {
    pub struct IStr;
}

impl inturn::InternerSymbol for IStr {
    #[inline]
    fn try_from_usize(id: usize) -> Option<Self> {
        <Self as ::core::convert::TryFrom<usize>>::try_from(id).ok()
    }

    #[inline]
    fn to_usize(self) -> usize {
        self.idx()
    }
}

pub type StringInterner = Interner<IStr>;
