use super::Info;

#[derive(Debug, PartialEq)]
pub enum LexErrorKind {
  DotInNonDecimalNumeric,
  IllegalCharacter(char),
  InvalidNumber,
  NonBinCharInBin,
  NonDecCharInDec,
  NonHexCharInHex,
}

#[derive(Debug, PartialEq)]
pub enum ParseErrorKind {
  MismatchedLParen,
  MismatchedRParen,
  OrphanedLexeme,
  QuotedRParen,
}

#[derive(Debug)]
pub struct LexError(pub LexErrorKind, pub Info);

#[derive(Debug)]
pub struct ParseError(pub ParseErrorKind, pub Info);

