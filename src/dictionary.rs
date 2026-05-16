//! Dictionary.
//!
//! - No `{plover:deleted}` support.

use rustc_hash::FxHashMap;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Output {
    String(String),
    // Command
}

/// Maps sequences to translations and tracks the length of the longest key.
#[derive(Debug, Clone)]
pub struct StenoDictionary {
    entries: FxHashMap<Vec<String>, Output>,
    rev: FxHashMap<Output, Vec<Vec<String>>>,
}

impl StenoDictionary {
    pub fn new(entries: FxHashMap<Vec<String>, Output>) -> Self {
        let mut rev = FxHashMap::<Output, Vec<Vec<String>>>::default();
        for (outline, output) in &entries {
            if let Some(v) = rev.get_mut(output) {
                v.push(outline.clone());
            } else {
                rev.insert(output.clone(), vec![outline.clone()]);
            }
        }
        Self { entries, rev }
    }

    /// Looks up an output for the outline.
    pub fn get(&self, outline: &[String]) -> Option<&Output> {
        self.entries.get(outline)
    }

    /// Looks up outlines for the output.
    pub fn rev_get(&self, output: &Output) -> Option<&Vec<Vec<String>>> {
        self.rev.get(output)
    }
}

#[derive(Debug, Clone)]
pub struct StenoDictionaryStack {
    //
    dicts: Vec<StenoDictionary>,
}

impl StenoDictionaryStack {
    pub fn new(dicts: Vec<StenoDictionary>) -> Self {
        Self { dicts }
    }

    /// Looks up an output for the outline.
    pub fn get(&self, outline: &[String]) -> Option<&Output> {
        self.dicts.iter().find_map(|d| d.get(outline))
    }

    /// Looks up outlines for the output.
    pub fn rev_get(&self, output: &Output) -> Option<&Vec<Vec<String>>> {
        self.dicts.iter().find_map(|d| d.rev_get(output))
    }
}
