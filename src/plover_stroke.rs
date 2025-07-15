//! Port of [`plover_stroke`](https://github.com/openstenoproject/plover_stroke).
//!
//! In this module, we denote the number of keys as _n_.

use std::cmp::Ordering;
use std::fmt;
use std::iter::zip;

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
pub struct StenoKeys {
    /// 63, because we want to use bit flags of length `64`.
    n_max_keys: usize,
    /// n_max_keys + 1 (+1 for hyphen).
    n_max_steno: usize,
    /// Represents a feral number key. TODO: different from number_key_mask?
    feral_number_key_char: Option<char>,
    /// The number of keys in this steno keyboard.
    n_keys: usize,
    /// Represents all number key indices.
    number_key_mask: usize,
    /// Delimits left and right side keys. TODO: Is this correct?
    hyphen_index: usize,
    /// Array of length `n_keys` that maps key index to letters in normal mode.
    letter_keys: Box<[char]>,
    /// Array of length `n_keys` that maps key index to numbers in number mode.
    number_keys: Box<[char]>,
    /// Array of length `n_keys` that maps key index to side of the keyboard.
    key_side: Box<[KeySide]>,
}

impl StenoKeys {
    pub fn new(
        keys: &[KeyWithSide],
        implicit_hyphe_keys: &[char],
        // TODO: Option(char, &[char])?
        number_key: Option<char>,
        numbers: &[char],
        feral_number_key_char: Option<char>,
    ) -> Option<Self> {
        if number_key.is_none() && !numbers.is_empty() || number_key.is_some() && numbers.is_empty()
        {
            // TODO: return error instead
            return None;
        }

        Some(Self {
            n_max_keys: 63,
            n_max_steno: 64,
            feral_number_key_char,
            n_keys: keys.len(),
            number_key_mask: todo!(),
            hyphen_index: todo!(),
            letter_keys: todo!(),
            number_keys: todo!(),
            key_side: todo!(),
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
    /// let keys = StenoKeys::new(&keys, &[], None, &[], None).unwrap();
    /// assert_eq!(keys.parse_stroke("AE"), Some(Stroke { mask: 9 }));
    /// ```
    pub fn parse_stroke(self, stroke_notation: &str) -> Option<Stroke> {
        // FIXME: Is this correct? (All number keys are feral number keys)
        if stroke_notation
            .chars()
            .filter(|&c| Some(c) == self.feral_number_key_char)
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
                _ if Some(c) == self.feral_number_key_char => {
                    mask |= self.number_key_mask;
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

            // Actual key handling
            let current_keys = if matches!(c, '0'..'9') {
                &self.number_keys
            } else {
                // TODO: This does not contain `#`, right? Otherwise the first loop in this
                // function is wrong.
                &self.letter_keys
            };

            // Find next character that matches to the input, in steno order.
            while let Some(&next_c) = current_keys.get(current_key_index)
                && c != next_c
            {
                current_key_index += 1;
            }

            if current_key_index == self.n_keys {
                // Failed to find the next key.
                return None;
            }

            // This key is pressed.
            mask |= 1 << current_key_index
        }

        // If any number key appears, turn of number key, if if the input does not contain `#`
        // (implicit number key).
        if (mask & self.number_key_mask) == 0
            && stroke_notation.chars().any(|c| matches!(c, '0'..'9'))
        {
            mask |= self.number_key_mask;
        }

        // We could remove this check, but let's prefer safety:
        Some(
            self.stroke_from_bitmask(mask)
                .unwrap_or_else(|| unreachable!()),
        )
    }

    /// _O(1)_ Creates a `Stroke` from a bitmask, performing boundary check.
    pub fn stroke_from_bitmask(&self, mask: usize) -> Option<Stroke> {
        if mask >> self.n_keys == 0 {
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
            let current_keys = if matches!(key, '0'..'9') {
                mask |= self.number_key_mask;
                &self.number_keys
            } else {
                &self.letter_keys
            };

            let (start, end) = match side {
                KeySide::None => (0, self.n_keys),
                KeySide::Left => (0, self.hyphen_index),
                KeySide::Right => (self.hyphen_index, self.n_keys),
            };

            // TODO: It should be more strict about steno order, e.g., it accepts `A- -A A-`?
            if let Some(k) = zip(
                current_keys[start..end].iter(),
                self.key_side[start..end].iter(),
            )
            .position(|(&k, &s)| (k, s) == (key, side))
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
