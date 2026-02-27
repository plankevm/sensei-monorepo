use std::path::PathBuf;

use sensei_core::{IndexVec, newtype_index};

newtype_index! {
    pub struct SourceId;
}

pub struct SourceInfo {
    pub path: PathBuf,
}

pub struct SourceManager {
    sources: IndexVec<SourceId, SourceInfo>,
}

impl SourceManager {
    pub fn new() -> Self {
        Self { sources: IndexVec::new() }
    }

    pub fn add_source(&mut self, path: PathBuf) -> SourceId {
        self.sources.push(SourceInfo { path })
    }
}
