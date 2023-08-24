use super::LexemeInfo;

#[derive(Debug, PartialEq)]
pub enum LexErrorKind {
  DotInNonDecimalNumeric,
  IllegalCharacter(char),
  InvalidNumber,
  NonBinCharInBin,
  NonDecCharInDec,
  NonHexCharInHex,
}

#[derive(Debug)]
pub struct LexError(pub LexErrorKind, pub LexemeInfo);

