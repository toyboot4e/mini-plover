//! Dictionary.
//!
//! - No `{plover:deleted}` support.

/// Maps sequences to translations and tracks the length of the longest key.
pub struct StenoDictionary {
    dict: (),
    rev: (),
}

pub struct StenoDictionaryCollection {
    //
    dicts: Vec<StenoDictionary>,
}

impl StenoDictionaryCollection {
    pub fn new(dicts: Vec<StenoDictionary>) -> Self {
        Self { dicts }
    }

    // key??
    pub fn lookup(&self, key: &str) -> Option<&str> {
        None
    }

    pub fn reverse_lookup(&self, translation: &str) -> Option<&str> {
        None
    }
}
