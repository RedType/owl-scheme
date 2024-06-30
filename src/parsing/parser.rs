use std::{
  collections::VecDeque,
  iter::Peekable,
};
use crate::{
  data::{Data, GcData, SymbolTable},
  parsing::{
    Info,
    lexer::{Lexeme, LexItem},
    error::{ParseError, ParseErrorKind},
  },
  vm::VM,
};
use gc::{Gc, GcCell};

fn parse_list<I: Iterator<Item = LexItem>>(
  lexemes: &mut Peekable<I>,
  symbols: &mut SymbolTable,
  head_info: Info,
) -> Result<Data, ParseError> {
  let mut list: VecDeque<GcData> = VecDeque::new();
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
        /* no longer ending lists with nil -- assume its presence
         * this means that the dot lexeme is now meaningless,
         * which is fine
         *
        // end list with nil (if it isn't already nil)
        if !dotted && !list.is_empty() {
          list.push_back(Gc::new(GcCell::new(Data::nil())));
        }
        */
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

        list.push_back(Gc::new(GcCell::new(next_data)));
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
    Some(LexItem(Lexeme::Float(x), _)) => Data::Real(x),

    Some(LexItem(Lexeme::LParen, info)) => parse_list(lexemes, symbols, info)?,
    Some(LexItem(Lexeme::RParen, info)) => {
      return Err(ParseError(ParseErrorKind::MismatchedRParen, info));
    },
    Some(LexItem(Lexeme::Quote, _)) => {
      if let Some(LexItem(Lexeme::RParen, info)) = lexemes.peek() {
        return Err(ParseError(ParseErrorKind::QuotedRParen, *info));
      }
      Data::List([
        Gc::new(GcCell::new(symbols.add("quote"))),
        Gc::new(GcCell::new(parse_rec(lexemes, symbols)?)),
        // no longer ending lists with nil
        //Gc::new(GcCell::new(Data::nil())),
      ].into())
    },

    None => panic!("Tried to parse nothing"),
  };

  Ok(data)
}

impl VM {
  pub fn build_ast<I>(&mut self, sequence: I) -> Result<Vec<Data>, ParseError>
  where
    I: IntoIterator<Item = LexItem>,
  {
    let mut lexemes = sequence.into_iter().peekable();
    let mut data = Vec::new();

    while let Some(_) = lexemes.peek() {
      data.push(parse_rec(&mut lexemes, &mut self.symbols)?);
    }

    Ok(data)
  }
}

#[cfg(test)]
mod tests {
  use crate::{
    data::Data,
    parsing::error::ParseErrorKind,
    vm::VM,
  };
  use gc::{Gc, GcCell};

  macro_rules! l {
    [$($x:expr),+$(,)?] => {
      Data::List([$(Gc::new(GcCell::new($x))),+].into())
    }
  }

  macro_rules! parse_str {
    ($vm:expr, $s:expr) => {{
      let lexemes = $vm.lex($s.chars()).unwrap();
      $vm.build_ast(lexemes).unwrap()
    }}
  }

  #[test]
  fn parse_empty() {
    let mut vm = VM::new();
    let result = vm.build_ast([]);
    assert!(result.unwrap().is_empty());
  }

  #[test]
  fn parse_empty_list() {
    let mut vm = VM::new();
    let actual = parse_str!(vm, "()()");
    let expected = vec![Data::nil(), Data::nil()];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_funny_list() {
    let mut vm = VM::new();
    let actual = parse_str!(vm, "(())");
    let expected = vec![l![Data::nil(), /*Data::nil()*/]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_list() {
    let mut vm = VM::new();
    let actual = parse_str!(vm, "(a b c d)");
    let expected = vec![l![
      vm.symbols.get("a").unwrap(),
      vm.symbols.get("b").unwrap(),
      vm.symbols.get("c").unwrap(),
      vm.symbols.get("d").unwrap(),
      //Data::nil(),
    ]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_lists() {
    let mut vm = VM::new();
    let actual = parse_str!(vm, "(a)(b) 5.5 (c d)");
    let expected = vec![
      l![vm.symbols.get("a").unwrap(), /*Data::nil()*/],
      l![vm.symbols.get("b").unwrap(), /*Data::nil()*/],
      Data::Real(5.5),
      l![
        vm.symbols.get("c").unwrap(),
        vm.symbols.get("d").unwrap(),
        //Data::nil(),
      ],
    ];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_deep_list() {
    let mut vm = VM::new();
    let actual = parse_str!(vm, "(a (b c) . d)");
    let expected = vec![l![
      vm.symbols.get("a").unwrap(),
      l![
        vm.symbols.get("b").unwrap(),
        vm.symbols.get("c").unwrap(),
        //Data::nil(),
      ],
      vm.symbols.get("d").unwrap(),
    ]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn quote() {
    let mut vm = VM::new();
    let actual = parse_str!(vm, "(a 'b '('c d))");
    let expected = vec![l![
      vm.symbols.get("a").unwrap(),
      l![
        vm.symbols.get("quote").unwrap(),
        vm.symbols.get("b").unwrap(),
        //Data::nil(),
      ],
      l![
        vm.symbols.get("quote").unwrap(),
        l![
          l![
            vm.symbols.get("quote").unwrap(),
            vm.symbols.get("c").unwrap(),
            //Data::nil(),
          ],
          vm.symbols.get("d").unwrap(),
          //Data::nil(),
        ],
        //Data::nil(),
      ],
      //Data::nil(),
    ]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn err_mismatched_l_paren() {
    let mut vm = VM::new();
    let lexemes = vm.lex("(a 'b '('c d)".chars()).unwrap();
    let result = vm.build_ast(lexemes).unwrap_err();
    assert_eq!(ParseErrorKind::MismatchedLParen, result.0);
  }

  #[test]
  fn err_mismatched_r_paren() {
    let mut vm = VM::new();
    let lexemes = vm.lex("(a 'b '()'c d))".chars()).unwrap();
    let result = vm.build_ast(lexemes).unwrap_err();
    assert_eq!(ParseErrorKind::MismatchedRParen, result.0);
  }

  #[test]
  fn err_quoted_r_paren() {
    let mut vm = VM::new();
    let lexemes = vm.lex("(a 'b (')'c d)".chars()).unwrap();
    let result = vm.build_ast(lexemes).unwrap_err();
    assert_eq!(ParseErrorKind::QuotedRParen, result.0);
  }

  #[test]
  fn err_wrongly_dotted_list() {
    let mut vm = VM::new();
    let lexemes = vm.lex("(a . b c)".chars()).unwrap();
    let result = vm.build_ast(lexemes).unwrap_err();
    assert_eq!(ParseErrorKind::WronglyDottedList, result.0);
  }
}

