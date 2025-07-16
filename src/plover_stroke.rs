//! Port of [`plover_stroke`](https://github.com/openstenoproject/plover_stroke).
//!
//! In this module, we denote the number of keys as _n_.

use std::cmp::Ordering;
use std::fmt;
use std::iter::zip;
use thiserror::Error;

/// `None` | `Left` | `Right`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KeySide {
    None,
    Left,
    Right,
}

/// One of `k`, `l-` or `-r`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KeyWithSide {
    pub key: char,
    pub side: KeySide,
}

impl fmt::Display for KeyWithSide {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.side {
            KeySide::None => write!(f, "{}", self.key),
            KeySide::Left => write!(f, "{}-", self.key),
            KeySide::Right => write!(f, "-{}", self.key),
        }
    }
}

impl KeyWithSide {
    /// Parses `<key>`, `<key>-` or `-<key>`.
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
                key: cs[0],
                side: KeySide::None,
            }),
            2 if s == "--" => None,
            2 if s.ends_with('-') => Some(Self {
                key: cs[0],
                side: KeySide::Left,
            }),
            2 if s.starts_with('-') => Some(Self {
                key: cs[1],
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

/// Steno keyboard keys in order.
// TODO: Name it propertly.
pub struct StenoKeys {
    /// 63, because we want to use bit flags of length `64`.
    n_max_keys: usize,
    /// n_max_keys + 1 (+1 for hyphen).
    n_max_steno: usize,
    /// Represents a feral number key. TODO: different from number_key_mask?
    feral_number_key: Option<char>,
    /// Represents the bit of a number key if there any.
    // TODO: use Option<usize> and store the index instead.
    number_key_bit_mask: usize,
    /// Delimits left and right side keys. TODO: Is this correct?
    hyphen_index: usize,
    /// Array of length `n_keys` that maps key index to letters in normal mode.
    pub keys: Box<[Key]>,
}

// TODO: Name it StenoKey.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Key {
    pub normal: char,
    pub number: char,
    pub side: KeySide,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KeyLayer {
    Normal,
    Number,
}

impl Key {
    pub fn key_in_layer(&self, ty: KeyLayer) -> char {
        match ty {
            KeyLayer::Normal => self.normal,
            KeyLayer::Number => self.number,
        }
    }
}

/// Error found in `StenoKeys::new`.
#[derive(Debug, Error)]
pub enum StenoKeysError {
    #[error("invalid number key input combination")]
    InvalidNumberKeyInputCombination,
    #[error("feran number key must be disabled if number key is `None`")]
    FeralNumberKeyMustBeDisabled,
    #[error("`{0}` is not a number key")]
    NotANumberKey(char),
    #[error("invalid implicit hyphen keys")]
    InvalidImplicitHyphenKeys,
    #[error("found left side key in right side: {0}")]
    FoundLeftSideKeyInRightSide(char),
    #[error("expected number keys, but found none")]
    NotFoundNumberKeys,
    #[error("number key count is not equal to 10: {0}")]
    NumberKeyCountNot10(u32),
}

impl StenoKeys {
    /// _O(nk)_ Creates
    ///
    /// (_n_: number of keys, _k_: length of the `numbers` map)
    ///
    /// Bit mask represents a bitmask that filters a single bit. Mask or bitmask represents a
    /// set of bits.
    ///
    /// ## Constraints
    /// -
    ///
    /// ## Invariants
    /// -
    // TODO: report all the errors at once
    pub fn new(
        keys_input: &[KeyWithSide],
        implicit_hyphen_keys: &[char],
        number_key: Option<char>,
        numbers: &[(char, char)],
        feral_number_keys_enabled: bool,
    ) -> Result<Self, StenoKeysError> {
        // Input validation (TODO: Forbit invalid input with types)
        if number_key.is_none() && !numbers.is_empty() || number_key.is_some() && numbers.is_empty()
        {
            // Incompatible `number_key` and `numbers` setup.
            // TODO: return error instead
            return Err(StenoKeysError::InvalidNumberKeyInputCombination);
        }

        if number_key.is_none() && feral_number_keys_enabled {
            return Err(StenoKeysError::FeralNumberKeyMustBeDisabled);
        }

        if let Some((_, v)) = numbers.iter().find(|(_, v)| !matches!(v, '0'..'9')) {
            // Note a number key.
            return Err(StenoKeysError::NotANumberKey(*v));
        }

        // Now, for simplicity, I'll iterate through the `keys_input` multple times.
        let n_keys = keys_input.len();
        let keys = keys_input
            .iter()
            .cloned()
            .map(|KeyWithSide { key, side }| {
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
                    .unwrap_or(key);

                Key {
                    normal: key,
                    number,
                    side,
                }
            })
            .collect::<Vec<_>>();

        // Not known yet.
        let mut hyphen_index = n_keys;

        let mut implicit_hyphen_mask = keys_input
            .iter()
            .enumerate()
            .filter(|(_, KeyWithSide { key, .. })| implicit_hyphen_keys.contains(&key))
            .fold(0usize, |mask, (i, _)| mask | (1 << i));

        // TODO: What if there are emultiple number keys in the input?
        let mut number_key_bit_mask = if let Some(number_key) = number_key {
            keys_input
                .iter()
                .enumerate()
                .find(|(i, KeyWithSide { key, .. })| *key == number_key)
                .map(|(i, _)| 1 << i)
                // TODO: warn or error if no number key is found?
                .unwrap_or(0)
        } else {
            0
        };

        let mut numbers_mask = if numbers.is_empty() {
            0
        } else {
            keys_input
                .iter()
                .enumerate()
                .filter(|(i, KeyWithSide { key, .. })| {
                    numbers.iter().cloned().any(|(nk, _)| nk == *key)
                })
                .fold(0usize, |mask, (i, _)| mask | (1 << i))
        };

        // Left hand side keys must not appear in the right side.
        // TODO: Refactor with scan-like function for this validation
        for (i, KeyWithSide { key, side }) in keys_input.iter().cloned().enumerate() {
            let key_bit_mask: usize = 1 << i;

            // TODO: validate with other loop
            match side {
                KeySide::Left if hyphen_index != n_keys => {
                    return Err(StenoKeysError::FoundLeftSideKeyInRightSide(key))
                }
                KeySide::Right if hyphen_index == n_keys => hyphen_index = i,
                _ => {}
            }

            if number_key.is_some() && numbers.iter().cloned().any(|(nk, _)| nk == key) {
                numbers_mask |= key_bit_mask;
            };
        }

        // Check 1: Number key count must be 10
        if number_key.is_some() {
            if number_key_bit_mask == 0 {
                return Err(StenoKeysError::NotFoundNumberKeys);
            }

            let n_numbers = numbers_mask.count_ones();
            if n_numbers != 10 {
                return Err(StenoKeysError::NumberKeyCountNot10(n_numbers));
            }
        }

        // Check 2: Find unique letters
        let unique_key_mask = crate::util::retain_unique_indices(
            keys_input.iter().map(|k| k.key).collect::<Vec<_>>(),
        )
        .iter()
        .fold(0usize, |mask, i| mask | (1 << i));

        if !implicit_hyphen_keys.is_empty() {
            // Check 3: Implicit hyphen keys all used
            if implicit_hyphen_mask.count_ones() as usize != implicit_hyphen_keys.len() {
                return Err(StenoKeysError::InvalidImplicitHyphenKeys);
            }

            // TODO: test that they're in a continuous block
            // TODO: test uniqueness of implicit_hyphen_keys
        } else {
            // Check 4
            // TODO: Detect hyphen
        }

        if feral_number_keys_enabled {
            //
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
            hyphen_index,
            keys: keys.into_boxed_slice(),
        })
    }

    /// _O(min(64, n))_ Creates `Stroke` from a `String` notation of it. This function is strict
    /// about steno order, meaning that the input string is basically a subsequence of `StenoKeys`.
    ///
    /// Say `ABCDE` is our `StenoKeys` and `AE` is the input. `AE` is clearly
    ///
    /// ```txt
    /// A B C D E
    /// A       E
    /// ```
    ///
    /// ```
    /// use mini_plover::plover_stroke::{KeyWithSide, StenoKeys, Stroke};
    /// let keys = "A- B- C -D -E"
    ///     .split_whitespace()
    ///     .map(KeyWithSide::parse)
    ///     .collect::<Option<Vec<_>>>()
    ///     .unwrap();
    /// let keys = StenoKeys::new(&keys, &[], None, &[], false).unwrap();
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

                '-' => match current_key_index.cmp(&self.hyphen_index) {
                    Ordering::Greater => return None,
                    // Equal: consecutive heyphens are allowed, right?
                    Ordering::Equal | Ordering::Less => {
                        current_key_index = self.hyphen_index;
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

        // If any number key appears, turn of number key, if if the input does not contain `#`
        // (implicit number key).
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

    /// _O(kn)_ Creates `Stroke` from a slice of `KeyWithSide`. The function is not strict about
    /// steno order and just sums up the given keys to the resulting `Stroke`.
    pub fn stroke_from_keys(&self, keys: &[KeyWithSide]) -> Option<Stroke> {
        let mut mask = 0;

        // TODO: rev?
        for KeyWithSide { key, side } in keys.iter().rev().cloned() {
            let (start, end) = match side {
                KeySide::None => (0, self.keys.len()),
                KeySide::Left => (0, self.hyphen_index),
                KeySide::Right => (self.hyphen_index, self.keys.len()),
            };

            // TODO: It should be more strict about steno order, e.g., it accepts `A- -A A-`?
            // It is the design of original `plover_stroke` though.
            if let Some(k) = self.keys[start..end]
                .iter()
                .position(|steno_key| {
                    let k = if matches!(key, '0'..'9') {
                        steno_key.number
                    } else {
                        steno_key.normal
                    };
                    (k, steno_key.side) == (key, side)
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
