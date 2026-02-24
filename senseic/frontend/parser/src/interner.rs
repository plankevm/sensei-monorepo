use sensei_core::{intern::StringInterner, newtype_index};

newtype_index! {
    /// String ID
    pub struct StrId;
}

pub struct PlankInterner {
    inner: StringInterner<StrId>,
}

impl PlankInterner {
    pub const VOID_NAME: StrId = StrId::new(0);
    pub const U256_NAME: StrId = StrId::new(1);
    pub const BOOL_NAME: StrId = StrId::new(2);
    pub const MEMPTR_NAME: StrId = StrId::new(3);
    pub const TYPE_NAME: StrId = StrId::new(4);
    pub const FUNCTION_NAME: StrId = StrId::new(5);

    pub fn new() -> Self {
        let mut inner = StringInterner::new();
        Self::inject_primitives(&mut inner);
        Self { inner }
    }

    pub fn with_capacities(names: usize, bytes: usize) -> Self {
        let mut inner = StringInterner::with_capacity(names, bytes);
        Self::inject_primitives(&mut inner);
        Self { inner }
    }

    fn inject_primitives(interner: &mut StringInterner<StrId>) {
        assert_eq!(interner.intern("void"), Self::VOID_NAME);
        assert_eq!(interner.intern("u256"), Self::U256_NAME);
        assert_eq!(interner.intern("bool"), Self::BOOL_NAME);
        assert_eq!(interner.intern("memptr"), Self::MEMPTR_NAME);
        assert_eq!(interner.intern("type"), Self::TYPE_NAME);
        assert_eq!(interner.intern("function"), Self::FUNCTION_NAME);
    }

    pub fn intern(&mut self, string: &str) -> StrId {
        self.inner.intern(string)
    }
}

impl std::ops::Index<StrId> for PlankInterner {
    type Output = str;

    fn index(&self, index: StrId) -> &Self::Output {
        &self.inner[index]
    }
}

impl Default for PlankInterner {
    fn default() -> Self {
        Self::new()
    }
}
