use crate::data::{Data, SymbolTable};

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

pub fn parse<I>(source: I) -> Result<(Vec<Data>, SymbolTable), ParseError>
where
  I: IntoIterator<Item = char>,
{
  let (lexemes, mut symbols) = lexer::lex(source)?;
  let data = parser::build_ast(lexemes, &mut symbols)?;
  Ok((data, symbols))
}

