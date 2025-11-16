//! Port of [`plover_stroke`](https://github.com/openstenoproject/plover_stroke).
//!
//! # Terms
//!
//! Mask or bitmask represents a set of bits. Bit mask represents a bitmask that filters a single
//! bit.
//!
//! # Notations
//!
//! In this module, we denote the number of keys as _n_.

#[cfg(test)]
mod test;

use std::cmp::Ordering;
use std::fmt;
use thiserror::Error;

/// `None` | `Left` | `Right`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KeySide {
    None,
    Left,
    Right,
}

/// One of `<letter>`, `<letter>-` or `-<letter>`.
///
/// # Examples
///
/// ```
/// use mini_plover::plover_stroke::{KeySide, LetterWithSide};
/// assert_eq!(
///     LetterWithSide::parse("a-"),
///     Some(LetterWithSide {
///         letter: 'a',
///         side: KeySide::Left
///     })
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LetterWithSide {
    pub letter: char,
    pub side: KeySide,
}

impl fmt::Display for LetterWithSide {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.side {
            KeySide::None => write!(f, "{}", self.letter),
            KeySide::Left => write!(f, "{}-", self.letter),
            KeySide::Right => write!(f, "-{}", self.letter),
        }
    }
}

impl LetterWithSide {
    /// Parses `<letter>`, `<letter>-` or `-<letter>`.
    pub fn parse(s: &str) -> Option<Self> {
        if s.len() > 8 {
            // Apparently too long.
            return None;
        }

        if s == "--" {
            return None;
        }

        let cs = s.chars().collect::<Vec<_>>();
        match cs.len() {
            0 => None,
            1 if s == "-" => None,
            1 => Some(Self {
                letter: cs[0],
                side: KeySide::None,
            }),
            2 if s == "--" => None,
            2 if s.ends_with('-') => Some(Self {
                letter: cs[0],
                side: KeySide::Left,
            }),
            2 if s.starts_with('-') => Some(Self {
                letter: cs[1],
                side: KeySide::Right,
            }),
            _ => None,
        }
    }
}

/// Bitmask of characters pressed on a steno keyboard (up to 63 keys).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Stroke {
    /// Bitmask
    pub mask: usize,
}

/// A sequence of stenographic keyboard keys and a set of rules.
///
/// - Key positioning: which keys are on the left or the right side of the keyboard.
/// - Implicit hyphen rules: Which keys automatically include hyphens in their representation,
///   allowing users to omit `-` in their steno stroke notation.
///
/// Different from the original `plover_stroke`, our `StenoSystem` does not have number key
/// layout information, because they should be implemented as dictionary data.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StenoSystem {
    /// 63 (constant), because we want to use bit flags of length `64`.
    n_max_keys: usize,
    /// n_max_keys + 1 (+1 for hyphen).
    n_max_steno: usize,
    /// Index of the first right side key.
    right_keys_index: usize,
    /// Array of length `n_keys` that maps key indeise to letters in normal mode.
    pub keys: Box<[LetterWithSide]>,
}

/// Error found in `StenoSystem::new`.
#[derive(Debug, Error)]
pub enum StenoSystemError {
    #[error("invalid implicit hyphen keys")]
    InvalidImplicitHyphenKeys,
    #[error("given non-continuous implicit hyphen keys")]
    NonContinuousImplicitHyphenKeys,
    #[error("not all implicit hyphen keys are unique")]
    NotAllImplicitHyphenKeysUnique,
    #[error("found left side key in right side: {0}")]
    FoundLeftSideKeyInRightSide(char),
}

impl StenoSystem {
    /// _O(nk)_ Creates a stey system from user-friendly input.
    ///
    /// (_n_: number of keys, _k_: length of the `numbers` map)
    pub fn new(
        letters: &[LetterWithSide],
        implicit_hyphen_letters: &[LetterWithSide],
    ) -> Result<Self, StenoSystemError> {
        // Now, for simplicity, I'll iterate through the `keys_input` multple times.
        let n_keys = letters.len();
        let keys = Vec::<LetterWithSide>::from(letters);

        // Left hand side keys must not appear in the right side.
        // TODO: Refactor with scan-like function for this validation
        // Not known yet.
        let right_keys_index = letters
            .iter()
            .cloned()
            .enumerate()
            .find_map(|(i, LetterWithSide { side, .. })| {
                if side == KeySide::Right {
                    Some(i)
                } else {
                    None
                }
            })
            .unwrap_or(n_keys);

        if let Some(k) = letters
            .iter()
            .skip(right_keys_index + 1)
            .cloned()
            .find(|k| k.side == KeySide::Left)
        {
            return Err(StenoSystemError::FoundLeftSideKeyInRightSide(k.letter));
        }

        // TODO: Use it for validation
        let unique_key_mask = crate::util::retain_unique_indices(
            letters.iter().map(|k| k.letter).collect::<Vec<_>>(),
        )
        .iter()
        .fold(0usize, |mask, i| mask | (1 << i));

        let implicit_hyphen_mask = if !implicit_hyphen_letters.is_empty() {
            // Create implicit hyphen key mask with an assumption that all of the keys are unique
            // (ensured later)
            let implicit_hyphen_mask = letters
                .iter()
                .enumerate()
                .filter(|(_, LetterWithSide { letter, .. })| {
                    implicit_hyphen_letters.iter().any(|l| l.letter == *letter)
                })
                .fold(0usize, |mask, (i, _)| mask | (1 << i));

            // All of the implicit hyphen keys must be used
            let n1 = implicit_hyphen_mask.count_ones();
            if n1 as usize != implicit_hyphen_letters.len() {
                return Err(StenoSystemError::InvalidImplicitHyphenKeys);
            }

            // All of the implicit hyphen keys are in a contiguous block
            let range_size =
                64 - (implicit_hyphen_mask.leading_zeros() + implicit_hyphen_mask.trailing_zeros());
            if range_size != n1 {
                return Err(StenoSystemError::NonContinuousImplicitHyphenKeys);
            }

            // All of the implicit hyphen keys must be unique so that we can insert hyphens
            if (implicit_hyphen_mask & unique_key_mask) != implicit_hyphen_mask {
                return Err(StenoSystemError::NotAllImplicitHyphenKeysUnique);
            }

            implicit_hyphen_mask
        } else {
            // Detect implicit hyphen keys in an automatic way.
            // TODO: Delete this case and force use provide with implicit hyphen keys

            // Find the leftmost unique letter key (inclusive)
            let l: usize = (0..right_keys_index)
                .rev()
                .take_while(|i| (unique_key_mask & (1 << i)) != 0)
                .last()
                .unwrap_or(right_keys_index);

            // Find the right unique letter key (exclusive)
            let r: usize = (right_keys_index + 1..n_keys)
                .take_while(|i| (unique_key_mask & (1 << i)) != 0)
                .last()
                .unwrap_or(right_keys_index);

            // FIXME: Create bitmask in [l, r)
            ((1 << l) - 1) & ((1 << r) - 1)
        };

        Ok(Self {
            n_max_keys: 63,
            n_max_steno: 64,
            right_keys_index,
            keys: keys.into_boxed_slice(),
        })
    }

    /// _O(min(64, n))_ Creates a `Stroke` from a `String` notation of it. This function is strict
    /// about steno order, meaning that the stroke notation is basically a subsequence of
    /// `StenoSystem` keys.
    ///
    /// Say `ABCDE` is our `StenoSystem` keys and `AE` is the input stroke notation. `AE` is clearly
    /// a subsequence:
    ///
    /// ```txt
    /// A B C D E
    /// A       E
    /// ```
    ///
    /// ```
    /// use mini_plover::plover_stroke::{LetterWithSide, StenoSystem, Stroke};
    /// let keys = "A- B- C -D -E"
    ///     .split_whitespace()
    ///     .map(LetterWithSide::parse)
    ///     .collect::<Option<Vec<_>>>()
    ///     .unwrap();
    /// let keys = StenoSystem::new(&keys, &[]).unwrap();
    /// assert_eq!(keys.parse_stroke("AE"), Some(Stroke { mask: 17 }));
    /// ```
    pub fn parse_stroke(self, stroke_notation: &str) -> Option<Stroke> {
        // Bitmask of keys  the `stroke` presses.
        let mut mask = 0;

        let mut current_key_index = 0;

        for c in stroke_notation.chars() {
            // Meta key handling
            match c {
                '-' => match current_key_index.cmp(&self.right_keys_index) {
                    Ordering::Greater => return None,
                    // Equal: consecutive heyphens are allowed, right?
                    Ordering::Equal | Ordering::Less => {
                        current_key_index = self.right_keys_index;
                        continue;
                    }
                },
                _ => {}
            }

            // Find next character that matches to the input, in steno order.
            while let Some(key) = self.keys.get(current_key_index)
                && key.letter != c
            {
                current_key_index += 1;
            }

            if current_key_index == self.keys.len() {
                // Failed to find the next key.
                return None;
            }

            // This key is pressed.
            mask |= 1 << current_key_index
        }

        // We could remove this check, but let's prefer safety:
        Some(
            self.stroke_from_bitmask(mask)
                .unwrap_or_else(|| unreachable!()),
        )
    }

    /// _O(1)_ Creates a `Stroke` from a bitmask, performing boundary check.
    pub fn stroke_from_bitmask(&self, mask: usize) -> Option<Stroke> {
        if mask >> self.keys.len() == 0 {
            Some(Stroke { mask })
        } else {
            None
        }
    }

    /// _O(kn)_ Creates `Stroke` from a slice of `LetterWithSide`. The function is
    /// not strict about steno order and just sums up the given keys to the
    /// resulting `Stroke`.
    pub fn stroke_from_keys(&self, keys: &[LetterWithSide]) -> Option<Stroke> {
        let mut mask = 0;

        // TODO: rev?
        for LetterWithSide { letter, side } in keys.iter().rev().cloned() {
            let (start, end) = match side {
                KeySide::None => (0, self.keys.len()),
                KeySide::Left => (0, self.right_keys_index),
                KeySide::Right => (self.right_keys_index, self.keys.len()),
            };

            // TODO: It should be more strict about steno order, e.g., it accepts `A- -A
            // A-`? It is the design of original `plover_stroke` though.
            if let Some(k) = self.keys[start..end]
                .iter()
                .position(|steno_key| steno_key.letter == letter && steno_key.side == side)
                .map(|i| i + start)
            {
                mask |= 1 << k;
            } else {
                return None;
            }
        }

        Some(Stroke { mask })
    }
}
