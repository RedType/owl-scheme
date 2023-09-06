use std::{
  iter::Peekable,
  rc::Rc,
};
use crate::{
  data::{Data, SymbolTable},
  parsing::{
    Info,
    lexer::{Lexeme, LexItem},
    error::{ParseError, ParseErrorKind},
  },
};

fn parse_list<I: Iterator<Item = LexItem>>(
  lexemes: &mut Peekable<I>,
  symbols: &mut SymbolTable,
  head_info: Info,
) -> Result<Data, ParseError> {
  let mut list: Vec<Rc<Data>> = Vec::new();

  loop {
    match lexemes.peek() {
      None => {
        return Err(ParseError(ParseErrorKind::MismatchedLParen, head_info));
      },
      Some(LexItem(Lexeme::RParen, _)) => {
        lexemes.next();
        return Ok(Data::List(list));
      },
      _ => {
        let next_data = parse_rec(lexemes, symbols)?;
        list.push(Rc::new(next_data));
      },
    }
  }
}

fn parse_rec<I: Iterator<Item = LexItem>>(
  lexemes: &mut Peekable<I>,
  symbols: &mut SymbolTable,
) -> Result<Data, ParseError> {
  let data = match lexemes.next() {
    Some(LexItem(Lexeme::Symbol(x), _)) => x,
    Some(LexItem(Lexeme::Boolean(x), _)) => Data::Boolean(x),
    Some(LexItem(Lexeme::String(x), _)) => Data::String(x),
    Some(LexItem(Lexeme::Integer(x), _)) => Data::Integer(x),
    Some(LexItem(Lexeme::Float(x), _)) => Data::Float(x),

    Some(LexItem(Lexeme::LParen, info)) => parse_list(lexemes, symbols, info)?,
    Some(LexItem(Lexeme::RParen, info)) => {
      return Err(ParseError(ParseErrorKind::MismatchedRParen, info));
    },
    Some(LexItem(Lexeme::Quote, _)) => {
      if let Some(LexItem(Lexeme::RParen, info)) = lexemes.peek() {
        return Err(ParseError(ParseErrorKind::QuotedRParen, *info));
      }
      let list = vec![
        Rc::new(symbols.add("quote")),
        Rc::new(parse_rec(lexemes, symbols)?),
      ];
      Data::List(list)
    },

    None => panic!("Tried to parse nothing"),
  };

  Ok(data)
}

pub fn build_ast<I>(sequence: I, symbols: &mut SymbolTable) -> Result<Vec<Data>, ParseError>
where
  I: IntoIterator<Item = LexItem>,
{
  let mut lexemes = sequence.into_iter().peekable();
  let mut data = Vec::new();

  while let Some(_) = lexemes.peek() {
    data.push(parse_rec(&mut lexemes, symbols)?);
  }

  Ok(data)
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use crate::{
    data::{Data, SymbolTable},
    parsing::{
      lexer::lex,
      parser::build_ast,
      error::ParseErrorKind,
    },
  };

  #[test]
  fn parse_empty() {
    let mut symbols = SymbolTable::new();
    let result = build_ast([], &mut symbols);
    assert!(result.unwrap().is_empty());
  }

  #[test]
  fn parse_empty_list() {
    let (lexemes, mut symbols) = lex("()()".chars()).unwrap();
    let actual = build_ast(lexemes, &mut symbols).unwrap();
    let expected = vec![Data::List(Vec::new()), Data::List(Vec::new())];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_list() {
    let (lexemes, mut symbols) = lex("(a b c d)".chars()).unwrap();
    let actual = build_ast(lexemes, &mut symbols).unwrap();
    let expected = vec![Data::List(vec![
      Rc::new(symbols.get("a").unwrap()),
      Rc::new(symbols.get("b").unwrap()),
      Rc::new(symbols.get("c").unwrap()),
      Rc::new(symbols.get("d").unwrap()),
    ])];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_lists() {
    let (lexemes, mut symbols) = lex("(a)(b) 5.5 (c d)".chars()).unwrap();
    let actual = build_ast(lexemes, &mut symbols).unwrap();
    let expected = vec![
      Data::List(vec![Rc::new(symbols.get("a").unwrap())]),
      Data::List(vec![Rc::new(symbols.get("b").unwrap())]),
      Data::Float(5.5),
      Data::List(vec![
        Rc::new(symbols.get("c").unwrap()),
        Rc::new(symbols.get("d").unwrap()),
      ]),
    ];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_deep_list() {
    let (lexemes, mut symbols) = lex("(a (b c) d)".chars()).unwrap();
    let actual = build_ast(lexemes, &mut symbols).unwrap();
    let expected = vec![Data::List(vec![
      Rc::new(symbols.get("a").unwrap()),
      Rc::new(Data::List(vec![
        Rc::new(symbols.get("b").unwrap()),
        Rc::new(symbols.get("c").unwrap()),
      ])),
      Rc::new(symbols.get("d").unwrap()),
    ])];
    assert_eq!(expected, actual);
  }

  #[test]
  fn quote() {
    let (lexemes, mut symbols) = lex("(a 'b '('c d))".chars()).unwrap();
    let actual = build_ast(lexemes, &mut symbols).unwrap();
    let expected = vec![Data::List(vec![
      Rc::new(symbols.get("a").unwrap()),
      Rc::new(Data::List(vec![
        Rc::new(symbols.get("quote").unwrap()),
        Rc::new(symbols.get("b").unwrap()),
      ])),
      Rc::new(Data::List(vec![
        Rc::new(symbols.get("quote").unwrap()),
        Rc::new(Data::List(vec![
          Rc::new(Data::List(vec![
            Rc::new(symbols.get("quote").unwrap()),
            Rc::new(symbols.get("c").unwrap()),
          ])),
          Rc::new(symbols.get("d").unwrap()),
        ])),
      ])),
    ])];
    assert_eq!(expected, actual);
  }

  #[test]
  fn err_mismatched_l_paren() {
    let (lexemes, mut symbols) = lex("(a 'b '('c d)".chars()).unwrap();
    let result = build_ast(lexemes, &mut symbols).unwrap_err();
    assert_eq!(ParseErrorKind::MismatchedLParen, result.0);
  }

  #[test]
  fn err_mismatched_r_paren() {
    let (lexemes, mut symbols) = lex("(a 'b '()'c d))".chars()).unwrap();
    let result = build_ast(lexemes, &mut symbols).unwrap_err();
    assert_eq!(ParseErrorKind::MismatchedRParen, result.0);
  }

  #[test]
  fn err_quoted_r_paren() {
    let (lexemes, mut symbols) = lex("(a 'b (')'c d)".chars()).unwrap();
    let result = build_ast(lexemes, &mut symbols).unwrap_err();
    assert_eq!(ParseErrorKind::QuotedRParen, result.0);
  }
}

