#[derive(Debug)]
pub enum LexErrorKind {
  DotInNonDecimalNumeric,
  IllegalCharacter(char),
  InvalidNumber,
  NonBinCharInBin,
  NonDecCharInDec,
  NonHexCharInHex,
}

#[derive(Debug)]
pub struct LexError {
  pub error: LexErrorKind,
  pub line: u64,
  pub col: u64,
  pub boundary_col: u64, // last non-value column
}

