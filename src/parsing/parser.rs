use std::{
  iter::Peekable,
  rc::Rc,
};
use crate::{
  data::Data,
  parsing::{
    Info,
    Lexeme, LexItem,
    ParseError, ParseErrorKind,
  },
};

fn parse_list<I: Iterator<Item = LexItem>>(
  lexemes: &mut Peekable<I>,
  head_info: Info,
) -> Result<Data, ParseError> {
  let mut list: Vec<Rc<Data>> = Vec::new();

  loop {
    match lexemes.peek() {
      None => {
        return Err(ParseError(ParseErrorKind::MismatchedLParen, head_info));
      },
      Some(&LexItem(Lexeme::RParen, _)) => {
        return Ok(Data::List(list));
      },
      _ => {
        let next_data = parse_rec(lexemes)?;
        list.push(Rc::new(next_data));
      },
    }
  }
}

fn parse_rec<I: Iterator<Item = LexItem>>(
  lexemes: &mut Peekable<I>,
) -> Result<Data, ParseError> {
  let data = match lexemes.next() {
    Some(LexItem(Lexeme::Identifier(x), _)) => Data::Symbol(x),
    Some(LexItem(Lexeme::Boolean(x), _)) => Data::Boolean(x),
    Some(LexItem(Lexeme::String(x), _)) => Data::String(x),
    Some(LexItem(Lexeme::Integer(x), _)) => Data::Integer(x),
    Some(LexItem(Lexeme::Float(x), _)) => Data::Float(x),

    Some(LexItem(Lexeme::LParen, info)) => parse_list(lexemes, info)?,
    Some(LexItem(Lexeme::RParen, info)) => {
      return Err(ParseError(ParseErrorKind::MismatchedRParen, info));
    },
    Some(LexItem(Lexeme::Quote, _)) => {
      let list = vec![
        Rc::new(Data::Symbol("quote".to_owned())),
        Rc::new(parse_rec(lexemes)?),
      ];
      Data::List(list)
    },

    None => panic!("Tried to parse nothing"),
  };

  Ok(data)
}

pub fn parse<I>(sequence: I) -> Result<Vec<Data>, ParseError>
where
  I: IntoIterator<Item = LexItem>,
{
  let mut lexemes = sequence.into_iter().peekable();
  let mut data = Vec::new();

  while let Some(_) = lexemes.peek() {
    data.push(parse_rec(&mut lexemes)?);
  }

  Ok(data)
}

#[cfg(test)]
mod tests {
  use super::*;
  /*
  use crate::{
    data::Data,
    parsing::ParseErrorKind::*,
  };
  */

  #[test]
  fn parse_empty() {
    let result = parse([]);
    assert!(result.is_ok());
    assert!(result.unwrap().0.is_empty());
  }
}

