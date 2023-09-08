use super::Info;

#[derive(Debug, PartialEq)]
pub enum ParseErrorKind {
  // lexer errors
  DotInNonDecimalNumeric,
  IllegalCharacter(char),
  InvalidNumber,
  NonBinCharInBin,
  NonDecCharInDec,
  NonHexCharInHex,
  // parser errors
  MismatchedLParen,
  MismatchedRParen,
  QuotedRParen,
  WronglyDottedList,
}

#[derive(Debug)]
pub struct ParseError(pub ParseErrorKind, pub Info);

