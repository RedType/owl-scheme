use std::{
  cell::RefCell,
  iter::Peekable,
  rc::Rc,
};
use crate::{
  data::{Data, IdTable},
  parsing::{
    Info,
    Lexeme, LexItem,
    ParseError, ParseErrorKind,
  },
};

fn parse_list<I: Iterator<Item = LexItem>>(
  lexemes: Rc<RefCell<Peekable<I>>>,
  identifiers: Rc<RefCell<IdTable>>,
  head_info: Info,
) -> Result<Data, ParseError> {
  let mut list: Vec<Rc<Data>> = Vec::new();

  loop {
    match lexemes.borrow_mut().peek() {
      None => {
        return Err(ParseError(ParseErrorKind::MismatchedLParen, head_info));
      },
      Some(&LexItem(Lexeme::RParen, _)) => {
        return Ok(Data::List(list));
      },
      _ => {
        let next_data = parse_rec(Rc::clone(&lexemes), Rc::clone(&identifiers))?;
        list.push(Rc::new(next_data));
      },
    }
  }
}

fn parse_rec<I: Iterator<Item = LexItem>>(
  lexemes: Rc<RefCell<Peekable<I>>>,
  identifiers: Rc<RefCell<IdTable>>,
) -> Result<Data, ParseError> {
  let data = match lexemes.borrow_mut().next() {
    Some(LexItem(Lexeme::Identifier(x), _)) => Data::Symbol(identifiers.borrow_mut().get(&x)),
    Some(LexItem(Lexeme::Boolean(x), _)) => Data::Boolean(x),
    Some(LexItem(Lexeme::String(x), _)) => Data::String(x),
    Some(LexItem(Lexeme::Integer(x), _)) => Data::Integer(x),
    Some(LexItem(Lexeme::Float(x), _)) => Data::Float(x),

    Some(LexItem(Lexeme::LParen, info)) =>
      parse_list(Rc::clone(&lexemes), Rc::clone(&identifiers), info)?,
    Some(LexItem(Lexeme::RParen, info)) => {
      return Err(ParseError(ParseErrorKind::MismatchedRParen, info));
    },
    Some(LexItem(Lexeme::Quote, _)) => {
      let list = vec![
        Rc::new(Data::Symbol(identifiers.borrow_mut().get("quote"))),
        Rc::new(parse_rec(Rc::clone(&lexemes), Rc::clone(&identifiers))?),
      ];
      Data::List(list)
    },

    None => panic!("Tried to parse nothing"),
  };

  Ok(data)
}

pub fn parse<I>(sequence: I) -> Result<(Vec<Data>, IdTable), ParseError>
where
  I: IntoIterator<Item = LexItem>,
{
  let lexemes = Rc::new(RefCell::new(sequence.into_iter().peekable()));
  let identifiers = Rc::new(RefCell::new(IdTable::new()));
  let mut data = Vec::new();

  while let Some(_) = lexemes.borrow_mut().peek() {
    data.push(parse_rec(Rc::clone(&lexemes), Rc::clone(&identifiers))?);
  }

  Ok((data, Rc::try_unwrap(identifiers).unwrap().take()))
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

