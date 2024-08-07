use crate::{
  data::{Data, DataCell},
  error::{ParseError, SourceInfo, VMError},
  parsing::lexer::{LexItem, Lexeme},
  vm::VM,
};
use gc::{Gc, GcCell};
use std::{collections::VecDeque, iter::Peekable};

impl VM {
  pub fn build_ast<I>(
    &mut self,
    sequence: I,
  ) -> Result<Vec<Gc<DataCell>>, VMError>
  where
    I: IntoIterator<Item = LexItem>,
  {
    let mut lexemes = sequence.into_iter().peekable();
    let mut data = Vec::new();

    while let Some(_) = lexemes.peek() {
      data.push(self.parse_rec(&mut lexemes)?);
    }

    Ok(data)
  }

  fn parse_list<I: Iterator<Item = LexItem>>(
    &mut self,
    lexemes: &mut Peekable<I>,
    head_info: SourceInfo,
  ) -> Result<Gc<DataCell>, VMError> {
    let mut list: VecDeque<Gc<DataCell>> = VecDeque::new();
    let mut dotted = false;

    loop {
      match lexemes.peek() {
        None => {
          return Err(VMError(
            Box::new(ParseError::MismatchedLParen),
            head_info,
          ));
        },
        Some(LexItem(Lexeme::Dot, _)) => {
          dotted = true;
          lexemes.next();
        },
        Some(LexItem(Lexeme::RParen, _)) => {
          lexemes.next();
          if list.is_empty() {
            return Ok(DataCell::new_info(Data::nil(), head_info));
          } else {
            let data = if dotted {
              // unroll dotted list ending with another list (or nil)
              if list.back().map(|e| e.has_nil()).unwrap_or(false) {
                let _ = list.pop_back();
                Data::list(list)
              } else if list.back().map(|e| e.has_list()).unwrap_or(false) {
                let last = list.pop_back().unwrap();
                let Data::List {
                  list: ref inner_list,
                  ..
                } = last.data
                else {
                  unreachable!();
                };
                for elem in inner_list.borrow().iter().cloned() {
                  list.push_back(elem)
                }
                Data::list(list)
              } else {
                Data::dotted_list(list)
              }
            } else {
              Data::list(list)
            };
            return Ok(DataCell::new_info(data, head_info));
          }
        },
        _ => {
          let next_data = self.parse_rec(lexemes)?;

          // check for end of list if dotted
          if dotted {
            if let Some(LexItem(lexeme, info)) = lexemes.peek() {
              if *lexeme != Lexeme::RParen {
                return Err(VMError(
                  Box::new(ParseError::WronglyDottedList),
                  info.clone(),
                ));
              }
            }
          }

          list.push_back(next_data);
        },
      }
    }
  }

  fn parse_rec<I: Iterator<Item = LexItem>>(
    &mut self,
    lexemes: &mut Peekable<I>,
  ) -> Result<Gc<DataCell>, VMError> {
    let data = match lexemes.next() {
      Some(LexItem(Lexeme::Dot, info)) => {
        panic!("Illegal dot location {:?}", info)
      },
      Some(LexItem(Lexeme::Placeholder, info)) => {
        DataCell::new_info(Data::Placeholder, info)
      },
      Some(LexItem(Lexeme::Symbol(x), info)) => DataCell::new_info(x, info),
      Some(LexItem(Lexeme::Boolean(x), info)) => {
        DataCell::new_info(Data::Boolean(x), info)
      },
      Some(LexItem(Lexeme::String(x), info)) => {
        DataCell::new_info(Data::String(GcCell::new(x)), info)
      },
      Some(LexItem(Lexeme::Integer(x), info)) => {
        DataCell::new_info(Data::Integer(x), info)
      },
      Some(LexItem(Lexeme::Float(x), info)) => {
        DataCell::new_info(Data::Real(x), info)
      },
      Some(LexItem(Lexeme::Rational(n, d), info)) => {
        DataCell::new_info(self.rational(n, d), info)
      },
      Some(LexItem(Lexeme::Complex(r, i), info)) => {
        DataCell::new_info(Data::Complex(r, i), info)
      },

      Some(LexItem(Lexeme::LParen, info)) => self.parse_list(lexemes, info)?,
      Some(LexItem(Lexeme::RParen, info)) => {
        return Err(VMError(Box::new(ParseError::MismatchedRParen), info));
      },
      Some(LexItem(Lexeme::Quote, info)) => {
        if let Some(LexItem(Lexeme::RParen, info)) = lexemes.peek() {
          return Err(VMError(
            Box::new(ParseError::QuotedRParen),
            info.clone(),
          ));
        }
        DataCell::new_info(
          Data::list([
            DataCell::new_info(self.symbols.add("quote"), info.clone()),
            self.parse_rec(lexemes)?,
          ]),
          info,
        )
      },

      None => panic!("Tried to parse nothing"),
    };

    Ok(data)
  }
}

#[cfg(test)]
mod tests {
  use crate::{
    data::{Data, DataCell},
    error::{ParseError, SourceInfo},
    vm::VM,
  };

  macro_rules! l {
    [$($x:expr),+$(,)?] => {
      Data::list([$(DataCell::new_info($x, SourceInfo::blank())),+])
    }
  }

  macro_rules! dl {
    [$($x:expr),+$(,)?] => {
      Data::dotted_list([$(DataCell::new_info($x, SourceInfo::blank())),+])
    }
  }

  macro_rules! parse_str {
    ($vm:expr, $s:expr) => {{
      let lexemes = $vm.lex($s.chars()).unwrap();
      let results = $vm.build_ast(lexemes).unwrap();
      results
        .into_iter()
        .map(|r| r.data.clone())
        .collect::<Vec<_>>()
    }};
  }

  #[test]
  fn parse_empty() {
    let mut vm = VM::no_std();
    let result = vm.build_ast([]);
    assert!(result.unwrap().is_empty());
  }

  #[test]
  fn parse_empty_list() {
    let mut vm = VM::no_std();
    let actual = parse_str!(vm, "()()");
    let expected = vec![Data::nil(), Data::nil()];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_funny_list() {
    let mut vm = VM::no_std();
    let actual = parse_str!(vm, "(())");
    let expected = vec![l![Data::nil() /*Data::nil()*/,]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_list() {
    let mut vm = VM::no_std();
    let actual = parse_str!(vm, "(a b c d)");
    let expected = vec![l![
      vm.symbols.get("a").unwrap(),
      vm.symbols.get("b").unwrap(),
      vm.symbols.get("c").unwrap(),
      vm.symbols.get("d").unwrap(),
    ]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_lists() {
    let mut vm = VM::no_std();
    let actual = parse_str!(vm, "(a)(b) 5 (c d)");
    let expected = vec![
      l![vm.symbols.get("a").unwrap() /*Data::nil()*/,],
      l![vm.symbols.get("b").unwrap() /*Data::nil()*/,],
      Data::Integer(5),
      l![vm.symbols.get("c").unwrap(), vm.symbols.get("d").unwrap(),],
    ];
    assert_eq!(expected, actual);
  }

  #[test]
  fn parse_deep_list() {
    let mut vm = VM::no_std();
    let actual = parse_str!(vm, "(a (b c) . d)");
    let expected = vec![dl![
      vm.symbols.get("a").unwrap(),
      l![vm.symbols.get("b").unwrap(), vm.symbols.get("c").unwrap(),],
      vm.symbols.get("d").unwrap(),
    ]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn quote() {
    let mut vm = VM::no_std();
    let actual = parse_str!(vm, "(a 'b '('c d))");
    let expected = vec![l![
      vm.symbols.get("a").unwrap(),
      l![
        vm.symbols.get("quote").unwrap(),
        vm.symbols.get("b").unwrap(),
      ],
      l![
        vm.symbols.get("quote").unwrap(),
        l![
          l![
            vm.symbols.get("quote").unwrap(),
            vm.symbols.get("c").unwrap(),
          ],
          vm.symbols.get("d").unwrap(),
        ],
      ],
    ]];
    assert_eq!(expected, actual);
  }

  #[test]
  fn err_mismatched_l_paren() {
    let mut vm = VM::no_std();
    let lexemes = vm.lex("(a 'b '('c d)".chars()).unwrap();
    let result = vm.build_ast(lexemes).unwrap_err();
    assert_eq!(
      ParseError::MismatchedLParen,
      *result.0.downcast::<ParseError>().unwrap()
    );
  }

  #[test]
  fn err_mismatched_r_paren() {
    let mut vm = VM::no_std();
    let lexemes = vm.lex("(a 'b '()'c d))".chars()).unwrap();
    let result = vm.build_ast(lexemes).unwrap_err();
    assert_eq!(
      ParseError::MismatchedRParen,
      *result.0.downcast::<ParseError>().unwrap()
    );
  }

  #[test]
  fn err_quoted_r_paren() {
    let mut vm = VM::no_std();
    let lexemes = vm.lex("(a 'b (')'c d)".chars()).unwrap();
    let result = vm.build_ast(lexemes).unwrap_err();
    assert_eq!(
      ParseError::QuotedRParen,
      *result.0.downcast::<ParseError>().unwrap()
    );
  }

  #[test]
  fn err_wrongly_dotted_list() {
    let mut vm = VM::no_std();
    let lexemes = vm.lex("(a . b c)".chars()).unwrap();
    let result = vm.build_ast(lexemes).unwrap_err();
    assert_eq!(
      ParseError::WronglyDottedList,
      *result.0.downcast::<ParseError>().unwrap()
    );
  }
}
