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

/// Allow the number key letter `#` to appear anywhere of stroke notation if enabled.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FeralNumberKey {
    Enabled,
    Disabled,
}

/// A sequence of stenographic keyboard keys and a set of rules.
///
/// - Key positioning: which keys are on the left or the right side of the keyboard.
/// - Number system: how normal keys are mapped to number keys when a number key (typically `#`) is
///   pressed.
/// - Implicit hyphen rules: Which keys automatically include hyphens in their representation,
///   allowing users to omit `-` in their steno stroke notation.
// TODO: Name it propertly.
pub struct StenoSystem {
    /// 63, because we want to use bit flags of length `64`.
    n_max_keys: usize,
    /// n_max_keys + 1 (+1 for hyphen).
    n_max_steno: usize,
    /// Represents a feral number key. TODO: different from number_key_mask?
    feral_number_key: Option<char>,
    /// Represents the bit of a number key if there any.
    // TODO: use Option<usize> and store the index instead.
    number_key_bit_mask: usize,
    /// Index of the first right side key.
    right_keys_index: usize,
    /// Array of length `n_keys` that maps key index to letters in normal mode.
    pub keys: Box<[StenoKey]>,
}

/// A key on a [`StenoSystem`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StenoKey {
    /// Letter in normal layer.
    pub normal: char,
    /// Letter in number layer.
    pub number: char,
    /// Side of the key.
    pub side: KeySide,
}

/// `Normal` | `Number`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KeyLayer {
    Normal,
    Number,
}

impl StenoKey {
    pub fn key_in_layer(&self, ty: KeyLayer) -> char {
        match ty {
            KeyLayer::Normal => self.normal,
            KeyLayer::Number => self.number,
        }
    }
}

/// Error found in `StenoSystem::new`.
#[derive(Debug, Error)]
pub enum StenoSystemError {
    #[error("invalid number key input combination")]
    InvalidNumberKeyInputCombination,
    #[error("feran number key must be disabled if number key is `None`")]
    FeralNumberKeyMustBeDisabled,
    #[error("`{0}` is not a number key")]
    NotANumberKey(char),
    #[error("invalid implicit hyphen keys")]
    InvalidImplicitHyphenKeys,
    #[error("invalid non-continuous implicit hyphen keys")]
    NonContinuousImplicitHyphenKeys,
    #[error("not all implicit hyphen keys are unique")]
    NotAllImplicitHyphenKeysUnique,
    #[error("found left side key in right side: {0}")]
    FoundLeftSideKeyInRightSide(char),
    #[error("expected number keys, but found none")]
    NotFoundNumberKeys,
    #[error("number key count is not equal to 10: {0}")]
    NumberKeyCountNot10(u32),
    #[error("cannot have both feral number key and implicit hyphen key")]
    CannotHaveBothFeralNumberKeyAndImplicitHyphenKey,
}

impl StenoSystem {
    /// _O(nk)_ Creates a stey system from user-friendly input.
    ///
    /// (_n_: number of keys, _k_: length of the `numbers` map)
    pub fn new(
        letters: &[LetterWithSide],
        implicit_hyphen_letters: &[LetterWithSide],
        number_key: Option<char>,
        // TODO: use HashMap
        numbers: &[(LetterWithSide, char)],
        feral_number_keys_enabled: bool,
    ) -> Result<Self, StenoSystemError> {
        // Input validation (TODO: Forbit invalid input with types)
        if number_key.is_none() && !numbers.is_empty() || number_key.is_some() && numbers.is_empty()
        {
            // Incompatible `number_key` and `numbers` setup.
            // TODO: return error instead
            return Err(StenoSystemError::InvalidNumberKeyInputCombination);
        }

        if number_key.is_none() && feral_number_keys_enabled {
            return Err(StenoSystemError::FeralNumberKeyMustBeDisabled);
        }

        if let Some((_, v)) = numbers.iter().find(|(_, v)| !matches!(v, '0'..'9')) {
            // Note a number key.
            return Err(StenoSystemError::NotANumberKey(*v));
        }

        // Now, for simplicity, I'll iterate through the `keys_input` multple times.
        let n_keys = letters.len();
        let keys = letters
            .iter()
            .cloned()
            .map(|key| {
                let number = number_key
                    .and_then(|_| {
                        numbers.iter().cloned().find_map(
                            |(k, v)| {
                                if k == key {
                                    Some(v)
                                } else {
                                    None
                                }
                            },
                        )
                    })
                    .unwrap_or(key.letter);

                StenoKey {
                    normal: key.letter,
                    number,
                    side: key.side,
                }
            })
            .collect::<Vec<_>>();

        // TODO: What if there are emultiple number keys in the input?
        let number_key_bit_mask = if let Some(number_letter) = number_key {
            letters
                .iter()
                .enumerate()
                .find(|(i, LetterWithSide { letter, .. })| *letter == number_letter)
                .map(|(i, _)| 1 << i)
                // TODO: warn or error if no number key is found?
                .unwrap_or(0)
        } else {
            0
        };

        let numbers_mask = if numbers.is_empty() {
            0
        } else {
            letters
                .iter()
                .enumerate()
                .filter(|(_, LetterWithSide { letter, .. })| {
                    numbers
                        .iter()
                        .cloned()
                        .any(|(number_key, _)| number_key.letter == *letter)
                })
                .fold(0usize, |mask, (i, _)| mask | (1 << i))
        };

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

        // Constraint 1: Number key count must be 10
        if number_key.is_some() {
            if number_key_bit_mask == 0 {
                return Err(StenoSystemError::NotFoundNumberKeys);
            }

            let n_numbers = numbers_mask.count_ones();
            if n_numbers != 10 {
                return Err(StenoSystemError::NumberKeyCountNot10(n_numbers));
            }
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
                implicit_hyphen_mask.leading_zeros() - implicit_hyphen_mask.trailing_zeros();
            if range_size != n1 {
                return Err(StenoSystemError::NonContinuousImplicitHyphenKeys);
            }

            // All of the implicit hyphen keys must be unique so that we can insert hyphens
            if (implicit_hyphen_mask & unique_key_mask) != right_keys_index {
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

        if feral_number_keys_enabled {
            if (number_key_bit_mask & implicit_hyphen_mask) != 0 {
                return Err(StenoSystemError::CannotHaveBothFeralNumberKeyAndImplicitHyphenKey);
            }
        }

        Ok(Self {
            n_max_keys: 63,
            n_max_steno: 64,
            feral_number_key: if feral_number_keys_enabled {
                number_key
            } else {
                None
            },
            number_key_bit_mask,
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
    /// let keys = StenoSystem::new(&keys, &[], None, &[], false).unwrap();
    /// assert_eq!(keys.parse_stroke("AE"), Some(Stroke { mask: 17 }));
    /// ```
    pub fn parse_stroke(self, stroke_notation: &str) -> Option<Stroke> {
        // FIXME: Is this correct? (All number keys are feral number keys)
        if stroke_notation
            .chars()
            .filter(|&c| Some(c) == self.feral_number_key)
            .count()
            > 1
        {
            // Number key must not appear twice in stroke notation.
            return None;
        }

        // Bitmask of keys  the `stroke` presses.
        let mut mask = 0;

        let mut current_key_index = 0;

        for c in stroke_notation.chars() {
            // Meta key handling
            match c {
                _ if Some(c) == self.feral_number_key => {
                    mask |= self.number_key_bit_mask;
                    continue;
                }

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
                && if matches!(c, '0'..'9') {
                    key.number
                } else {
                    key.normal
                } != c
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

        // If any number key appears, turn of number key, if if the input does not
        // contain `#` (implicit number key).
        if (mask & self.number_key_bit_mask) == 0
            && stroke_notation.chars().any(|c| matches!(c, '0'..'9'))
        {
            mask |= self.number_key_bit_mask;
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

    /// _O(kn)_ Creates `Stroke` from a slice of `KeyWithSide`. The function is
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
                .position(|steno_key| {
                    let c = if matches!(letter, '0'..'9') {
                        steno_key.number
                    } else {
                        steno_key.normal
                    };
                    (c, steno_key.side) == (letter, side)
                })
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
