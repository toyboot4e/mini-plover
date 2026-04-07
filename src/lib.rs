//! A minimal implementation of [Plover], the stenography engine.
//!
//! Throughout this library, we denote time complexity of functions with [big O notation].
//!
//! [Plover]: https://github.com/openstenoproject/plover
//! [big O notation]: https://en.wikipedia.org/wiki/Big_O_notation

pub mod dictionary;
pub mod engine;
pub mod plover_stroke;
pub mod translation;
pub mod util;
