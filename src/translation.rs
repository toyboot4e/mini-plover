//! Translation: converts an [`Outline`] into output strings or commands.
//!
//! - undoable

use crate::stroke::Outline;

pub struct Translation {
    translated: string,
}

pub struct Translator {
    //
}

impl Translator {
    pub fn translate(&mut self, outline: &Outline) -> Translation {
        Translation {
            translated: "dummy".to_string(),
        }
    }
}
