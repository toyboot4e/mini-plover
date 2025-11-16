//! Utilities.

use fxhash::FxHashMap;
use std::hash::Hash;
use std::ops;

pub fn counts<T: Eq + Hash>(xs: impl IntoIterator<Item = T>) -> FxHashMap<T, usize> {
    let mut cnts = FxHashMap::default();
    xs.into_iter()
        .for_each(|x| *cnts.entry(x).or_default() += 1);
    cnts
}

/// _O(n)_
pub fn retain_uniques<T: Eq + Hash + Clone, C>(xs: C) -> Vec<T>
where
    // iterate twice
    for<'a> &'a C: IntoIterator<Item = &'a T>,
{
    let cnts = counts(xs.into_iter());
    xs.into_iter()
        .cloned()
        .filter(|x| cnts.get(x) == Some(&1))
        .collect::<Vec<_>>()
}

/// _O(n)_
pub fn retain_unique_indices<T: Eq + Hash + Clone, C>(xs: C) -> Vec<usize>
where
    // iterate twice
    for<'a> &'a C: IntoIterator<Item = &'a T>,
{
    let cnts = counts(xs.into_iter());
    xs.into_iter()
        .cloned()
        .enumerate()
        .filter(|(_, x)| cnts.get(x) == Some(&1))
        .map(|(i, _)| i)
        .collect::<Vec<_>>()
}

/// _O(1)_
pub fn contains_range<T: PartialOrd>(outer: ops::Range<T>, inner: ops::Range<T>) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}
