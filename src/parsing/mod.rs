mod error;
mod lexer;
mod parser;

pub use self::error::{ParseError, ParseErrorKind};

#[derive(Clone, Copy, Debug)]
pub struct Info {
  pub line: u64,
  pub col: u64,
  pub boundary_col: u64, // last non-value column
}

