use crate::data::Data;
use gc::{Finalize, Trace};
use std::{error::Error, fmt, io, rc::Rc};
use thiserror::Error;

#[derive(Debug, Error)]
#[error("Error {1} {0}")]
pub struct VMError(pub Box<dyn Error>, pub SourceInfo);

impl VMError {
  pub fn new<E: Error + 'static>(error: E, info: SourceInfo) -> Self {
    Self(Box::new(error), info)
  }
}

#[derive(Clone, Debug, Finalize, Trace)]
pub struct SourceInfo {
  pub line: u32,
  pub col: u32,
  pub boundary_col: u32, // last non-value column
}

impl SourceInfo {
  pub fn new(line: u32, col: u32, boundary_col: u32) -> Self {
    Self {
      line,
      col,
      boundary_col,
    }
  }

  pub fn blank() -> Self {
    Self {
      line: 0,
      col: 0,
      boundary_col: 0,
    }
  }
}

impl fmt::Display for SourceInfo {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "on line {}:", self.line + 1)
  }
}

#[derive(Debug, Error, PartialEq)]
pub enum LexError {
  DotInNonDecimalNumeric,
  IllegalCharacter(char),
  InvalidNumber,
  MalformedComplex,
  MalformedRational,
  NonBinCharInBin,
  NonDecCharInDec,
  NonHexCharInHex,
}

impl fmt::Display for LexError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use LexError::*;

    match *self {
      DotInNonDecimalNumeric => {
        write!(f, "\".\" cannot appear in a non-decimal number")
      },
      IllegalCharacter(c) => write!(f, "\"{}\" is not allowed in source", c),
      InvalidNumber => write!(f, "invalid number"),
      MalformedComplex => write!(f, "malformed complex number"),
      MalformedRational => write!(f, "malformed rational number"),
      NonBinCharInBin => {
        write!(f, "non-binary (0-1) character in binary number")
      },
      NonDecCharInDec => {
        write!(f, "non-decimal (0-9) character in decimal number")
      },
      NonHexCharInHex => write!(
        f,
        "non-hexadecimal (0-9 + a-f) character in hexadecimal number"
      ),
    }
  }
}

#[derive(Debug, Error, PartialEq)]
pub enum ParseError {
  MismatchedLParen,
  MismatchedRParen,
  QuotedRParen,
  WronglyDottedList,
}

impl fmt::Display for ParseError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ParseError::*;

    match *self {
      MismatchedLParen => write!(f, "mismatched \"(\" left parenthesis"),
      MismatchedRParen => write!(f, "mismatched \")\" right parenthesis"),
      QuotedRParen => {
        write!(f, "quoted \")\" right parentheses are not allowed")
      },
      WronglyDottedList => {
        write!(f, "dot must occur before last element of list")
      },
    }
  }
}

#[derive(Debug, Error)]
pub enum ArithmeticError {
  NonNumericArgument(Data),
}

impl fmt::Display for ArithmeticError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ArithmeticError::*;

    match *self {
      NonNumericArgument(ref arg) => {
        write!(f, "{:?} given where a number was expected", arg)
      },
    }
  }
}

#[derive(Debug, Error)]
pub enum EvalError {
  IllegalPlaceholder,
  InvalidSpecialForm,
  InvalidLambdaName,
  InvalidParameter,
  InvalidParameterList,
  InvalidArgumentList,
  IOError(io::Error),
  NilEvaluation,
  NonBooleanTest,
  NonFunctionApplication(Data),
  NonSymbolInParameterList,
  PlaceholderInParameterList,
  PlaceholderInVarargs,
  TooManyArguments,
  UnboundSymbol(Rc<str>),
}

impl fmt::Display for EvalError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use EvalError::*;

    match *self {
      InvalidSpecialForm => {
        write!(f, "incorrect number of arguments given for special form")
      },
      InvalidLambdaName => write!(f, "lambda name must be a symbol"),
      InvalidParameter => write!(f, "parameters must be symbols"),
      InvalidParameterList => {
        write!(f, "expression must be a formal parameter list")
      },
      InvalidArgumentList => {
        write!(f, "expression must be a list of arguments")
      },
      IOError(ref e) => write!(f, "{}", e),
      NilEvaluation => write!(f, "empty list (nil) is not evaluable"),
      NonBooleanTest => write!(f, "non-boolean expression in conditional"),
      NonFunctionApplication(_) => {
        write!(f, "non-function values cannot be applied")
      },
      NonSymbolInParameterList => {
        write!(f, "parameter lists must only contain symbols")
      },
      PlaceholderInParameterList => {
        write!(f, "parameter lists cannot contain placeholders")
      },
      PlaceholderInVarargs => write!(f, concat!(
        "variable-length section of argument list",
        " must not contain placeholders",
      )),
      TooManyArguments => write!(f, "too many arguments given"),
      UnboundSymbol(ref name) => {
        write!(
          f,
          "attempted to evaluate or set an unbound symbol {}",
          *name
        )
      },
    }
  }
}

#[derive(Debug, Error)]
pub struct UnspecifiedError;

impl fmt::Display for UnspecifiedError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "???")
  }
}
