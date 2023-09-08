use std::{
  collections::VecDeque,
  iter::Peekable,
};
use crate::{
  data::{Data, SymbolTable},
  parsing::{
    Info,
    lexer::{Lexeme, LexItem},
    error::{ParseError, ParseErrorKind},
  },
};
use gc::GcCell;

fn parse_list<I: Iterator<Item = LexItem>>(
  lexemes: &mut Peekable<I>,
  symbols: &mut SymbolTable,
  head_info: Info,
) -> Result<Data, ParseError> {
  let mut list: VecDeque<GcCell<Data>> = VecDeque::new();
  let mut dotted = false;

  loop {
    match lexemes.peek() {
      None => {
        return Err(ParseError(ParseErrorKind::MismatchedLParen, head_info));
      },
      Some(LexItem(Lexeme::Dot, _)) => {
        dotted = true;
        lexemes.next();
      },
      Some(LexItem(Lexeme::RParen, _)) => {
        // end list with nil (if it isn't already nil)
        if !dotted && !list.is_empty() {
          list.push_back(GcCell::new(Data::nil()));
        }
        lexemes.next();
        return Ok(Data::List(list));
      },
      _ => {
        let next_data = parse_rec(lexemes, symbols)?;

        // check for end of list if dotted
        if dotted {
          if let Some(LexItem(lexeme, info)) = lexemes.peek() {
            if *lexeme != Lexeme::RParen {
              return Err(ParseError(ParseErrorKind::WronglyDottedList, *info));
            }
          }
        }

        list.push_back(GcCell::new(next_data));
      },
    }
  }
}

fn parse_rec<I: Iterator<Item = LexItem>>(
  lexemes: &mut Peekable<I>,
  symbols: &mut SymbolTable,
) -> Result<Data, ParseError> {
  let data = match lexemes.next() {
    Some(LexItem(Lexeme::Dot, info)) => panic!("Illegal dot location {:?}", info),
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
      Data::List([
        GcCell::new(symbols.add("quote")),
        GcCell::new(parse_rec(lexemes, symbols)?),
        GcCell::new(Data::nil())
      ].into())
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
  use crate::{
    data::{Data, SymbolTable},
    parsing::{
      lexer::lex,
      parser::build_ast,
      error::ParseErrorKind,
    },
  };
  use gc::GcCell;

  macro_rules! l {
    [$($x:expr),+$(,)?] => {
      Data::List([$(GcCell::new($x)),+].into())
    }
  }

  macro_rules! parse_str {
    ($s:expr) => {{
      let (lexemes, mut symbols) = lex($s.chars()).unwrap();
      (build_ast(lexemes, &mut symbols).unwrap(), symbols)
    }}
  }

  #[test]
  fn parse_empty() {
    let mut symbols = SymbolTable::new();
    let result = build_ast([], &mut symbols);
    assert!(result.unwrap().is_empty());
  }

  #[test]
  fn parse_empty_list() {
    let (actual, _) = parse_str!("()()");
    let expected = vec![Data::nil(), Data::nil()];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_funny_list() {
    let (actual, _) = parse_str!("(())");
    let expected = vec![l![Data::nil(), Data::nil()]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_list() {
    let (actual, symbols) = parse_str!("(a b c d)");
    let expected = vec![l![
      symbols.get("a").unwrap(),
      symbols.get("b").unwrap(),
      symbols.get("c").unwrap(),
      symbols.get("d").unwrap(),
      Data::nil(),
    ]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_lists() {
    let (actual, symbols) = parse_str!("(a)(b) 5.5 (c d)");
    let expected = vec![
      l![symbols.get("a").unwrap(), Data::nil()],
      l![symbols.get("b").unwrap(), Data::nil()],
      Data::Float(5.5),
      l![
        symbols.get("c").unwrap(),
        symbols.get("d").unwrap(),
        Data::nil(),
      ],
    ];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_deep_list() {
    let (actual, symbols) = parse_str!("(a (b c) . d)");
    let expected = vec![l![
      symbols.get("a").unwrap(),
      l![
        symbols.get("b").unwrap(),
        symbols.get("c").unwrap(),
        Data::nil(),
      ],
      symbols.get("d").unwrap(),
    ]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn quote() {
    let (actual, symbols) = parse_str!("(a 'b '('c d))");
    let expected = vec![l![
      symbols.get("a").unwrap(),
      l![
        symbols.get("quote").unwrap(),
        symbols.get("b").unwrap(),
        Data::nil(),
      ],
      l![
        symbols.get("quote").unwrap(),
        l![
          l![
            symbols.get("quote").unwrap(),
            symbols.get("c").unwrap(),
            Data::nil(),
          ],
          symbols.get("d").unwrap(),
          Data::nil(),
        ],
        Data::nil(),
      ],
      Data::nil(),
    ]];
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

  #[test]
  fn err_wrongly_dotted_list() {
    let (lexemes, mut symbols) = lex("(a . b c)".chars()).unwrap();
    let result = build_ast(lexemes, &mut symbols).unwrap_err();
    assert_eq!(ParseErrorKind::WronglyDottedList, result.0);
  }
}

