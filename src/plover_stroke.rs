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
