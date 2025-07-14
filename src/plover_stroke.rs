//! `plover_stroke`

use std::fmt;

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

/// Bitmask of characters pressed on a steno keyboard (up to 63 keys).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Stroke {
    /// Bitmask
    pub mask: usize,
}

/// Allow the number key letter `# to appear anywhere of steno if enabled.
pub enum FeralNumberKey {
    Enabled,
    Disabled,
}

/// Context for processing keys (up to 63) in steno order.
pub struct Context {
    /// 63, because we want to use bit flags of length `64`.
    n_max_keys: usize,
    /// n_max_keys + 1 (one hyphen).
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
}

impl Context {
    /// Creates `Stroke` from a `String` notation of it.
    pub fn parse_stroke_notation(self, stroke_notation: String) -> Option<Stroke> {
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

        // Bitmask of keys the `stroke` presses.
        let mut mask = 0;

        let mut current_key_index = 0;

        for c in stroke_notation.chars() {
            // Meta key handling
            match c {
                _ if Some(c) == self.feral_number_key_char => {
                    mask |= self.number_key_mask;
                    continue;
                }

                '-' if current_key_index > self.hyphen_index => {
                    // `-` must not appear after right side key.
                    return None;
                }
                '-' => {
                    current_key_index = self.hyphen_index;
                    continue;
                }
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

        // We could remove this check:
        self.stroke_from_bitmask(mask)
    }

    /// Creates a `Stroke` from a bitmask, performing boundary check.
    pub fn stroke_from_bitmask(&self, mask: usize) -> Option<Stroke> {
        if mask >> self.n_keys == 0 {
            Some(Stroke { mask })
        } else {
            None
        }
    }

    pub fn create_stroke_from_keys(&self, keys: &[char]) -> Option<Stroke> {
        todo!()
    }
}
