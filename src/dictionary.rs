//! Dictionary.
//!
//! - No `{plover:deleted}` support.

/// Maps sequences to translations and tracks the length of the longest key.
pub struct StenoDictionary {
    /// Reverse dictionary
    rev: (),
    /// Case-intensive reverse dictionary
    case_intensive_rev: (),
}

pub struct StenoDictionaryCollection {
    //
}

impl StenoDictionaryCollection {
    // TODO: What is the type of `key`?
    pub fn lookup(&self, key: string) -> Option<string> {
        None
    }

    pub fn reverse_lookup(&self, translation: string) -> Option<string> {
        None
    }
}
