use sensei_core::{IndexVec, newtype_index};
use std::path::PathBuf;

newtype_index! {
    pub struct SourceId;
}

pub struct SourceInfo {
    pub path: PathBuf,
}

pub struct SourceManager {
    sources: IndexVec<SourceId, SourceInfo>,
}

impl Default for SourceManager {
    fn default() -> Self {
        Self { sources: IndexVec::new() }
    }
}

impl SourceManager {
    pub fn add_source(&mut self, path: PathBuf) -> SourceId {
        self.sources.push(SourceInfo { path })
    }
}

impl std::ops::Index<SourceId> for SourceManager {
    type Output = SourceInfo;

    fn index(&self, index: SourceId) -> &Self::Output {
        &self.sources[index]
    }
}
