use std::{
  rc::Rc,
  str::FromStr,
};

use crate::{
  data::Data,
  parsing::{Info, ParseError, ParseErrorKind},
  vm::VM,
};

#[derive(Debug)]
pub enum Lexeme {
  LParen,
  RParen,
  Quote,
  Dot,
  Symbol(Data),
  Boolean(bool),
  String(String),
  Integer(i64),
  Float(f64),
}

impl PartialEq for Lexeme {
  fn eq(&self, other: &Self) -> bool {
    use Lexeme::*;
    match (self, other) {
      (LParen, LParen) => true,
      (RParen, RParen) => true,
      (Quote, Quote) => true,
      (Dot, Dot) => true,
      (Symbol(Data::Symbol(l)), Symbol(Data::Symbol(r))) => Rc::ptr_eq(l, r),
      (Boolean(l), Boolean(r)) => l == r,
      (String(l), String(r)) => l == r,
      (Integer(l), Integer(r)) => l == r,
      (Float(l), Float(r)) => l == r,
      _ => false,
    }
  }
}
impl Eq for Lexeme {}

#[derive(Debug)]
pub struct LexItem(pub Lexeme, pub Info);

#[derive(Clone, Copy)]
enum State {
  Start,
  Comment,
  BoolOrIdent,
  String,
  NegativeOrIdent,
  ZeroPrefixNumeric, // for non-decimal literals
  FloatOrDotIdent,
  Hexadecimal,
  Decimal,
  Binary,
}

impl VM {
  pub fn lex<I>(&mut self, source: I) -> Result<Vec<LexItem>, ParseError>
  where
    I: IntoIterator<Item = char>,
  {
    let mut items = Vec::new();
    let mut state = State::Start;
    // append a " " to end of input so that lexer can finish up
    let mut chars = source.into_iter().chain(" ".chars()).peekable();
    let mut line  = 0u64;
    let mut col   = 0u64;
    let mut boundary_col = 0u64;
    let mut scratch_pad = String::new();
    // for unshift
    let mut prev_line: u64;
    let mut prev_col: u64;
    let mut prev_boundary_col = 0u64;
    // for numerics
    let mut negative = false;

    // help us enforce that either shift or unshift are called
    // every iteration
    let mut shifted = true;

    // iterate over all characters in input. only peek, because
    // some state transitions may not want to consume the character
    while let Some(&ch) = chars.peek() {
      // check shifted
      assert!(shifted);
      #[allow(unused_assignments)]
      { shifted = false; }

      // update counters
      prev_line = line;
      prev_col = col;
      match ch {
        '\n' => {
          line += 1;
          col = 0;
          boundary_col = 0;
        },
        c @ '(' | c @ ')' | c if c.is_whitespace() => {
          col += 1;
          prev_boundary_col = boundary_col;
          boundary_col = col;
        },
        c if c.is_control() => {},
        _ => col += 1,
      }

      // consume current char
      macro_rules! shift {
        () => {
          shifted = true;
          chars.next();
        };
      }

      // reset line info when ch is not consumed
      macro_rules! unshift {
        () => {
          shifted = true;
          line = prev_line;
          col = prev_col;
          boundary_col = prev_boundary_col;
        };
      }

      // pushes a lexeme into the result list, along with all the metadata
      macro_rules! push_lex {
        ($x:expr) => {
          items.push(LexItem($x, Info {
            line,
            col,
            boundary_col,
          }))
        };
      }

      // creates and wraps an error
      macro_rules! err {
        ($x:expr) => {
          Err(ParseError($x, Info {
            line,
            col,
            boundary_col,
          }))
        };
      }

      // execute state machine for this iteration
      match state {
        State::Start => {
          match ch {
            ';'  => state = State::Comment,
            '('  => push_lex!(Lexeme::LParen),
            ')'  => push_lex!(Lexeme::RParen),
            '\'' => push_lex!(Lexeme::Quote),
            '"'  => state = State::String,
            '0'  => state = State::ZeroPrefixNumeric,
            '-'  => state = State::NegativeOrIdent,
            '.'  => {
              scratch_pad.push('.');
              state = State::FloatOrDotIdent;
            }
            c if c.is_whitespace() => {},
            c if c.is_digit(10) => {
              state = State::Decimal;
              scratch_pad.push(c);
            },
            c if c.is_control() =>
              return err!(ParseErrorKind::IllegalCharacter(c)),
            c => {
              state = State::BoolOrIdent;
              scratch_pad.push(c);
            }
          }

          // everything in this state consumes ch
          shift!();
        },

        State::Comment => {
          if ch == '\n' {
            state = State::Start;
          }

          shift!();
        },

        State::BoolOrIdent => {
          if ch.is_alphanumeric() {
            scratch_pad.push(ch);
            shift!();
          } else {
            match scratch_pad.as_str() {
              "#t" | "#true"  => push_lex!(Lexeme::Boolean(true)),
              "#f" | "#false" => push_lex!(Lexeme::Boolean(false)),
              _ => push_lex!(Lexeme::Symbol(self.symbols.add(&scratch_pad))),
            }
            scratch_pad = String::new();
            state = State::Start;
            unshift!();
          }
        },

        State::String => {
          match ch {
            '\\' => {
              //TODO do escapes
              todo!();
            },
            '"' => {
              push_lex!(Lexeme::String(scratch_pad));
              scratch_pad = String::new();
              state = State::Start;
            },
            c => scratch_pad.push(c),
          }

          shift!();
        },

        State::NegativeOrIdent => {
          match ch {
            '0' => {
              negative = true;
              state = State::ZeroPrefixNumeric;
            },
            c if c.is_numeric() => {
              negative = true;
              scratch_pad.push(c);
              state = State::Decimal;
            },
            _ => {
              negative = false;
              scratch_pad.push('-');
              state = State::BoolOrIdent;
            },
          }

          shift!();
        },

        State::ZeroPrefixNumeric => {
          match ch {
            'x' => state = State::Hexadecimal,
            'b' => state = State::Binary,
            '.' => {
              scratch_pad.push_str("0.");
              state = State::Decimal;
            },
            c if c.is_numeric() => {
              scratch_pad.push(c);
              state = State::Decimal;
            },
            c if c.is_alphabetic() =>
              return err!(ParseErrorKind::InvalidNumber),
            _ => {
              negative = false;
              push_lex!(Lexeme::Integer(0));
              state = State::Start;
              unshift!();
              continue; // so we don't shift later
            },
          }

          shift!();
        },

        State::FloatOrDotIdent => {
          state = match ch {
            ch@'(' | ch@')' | ch if ch.is_whitespace() => {
              scratch_pad = String::new();
              push_lex!(Lexeme::Dot);
              State::Start
            },
            ch if ch.is_numeric() => {
              scratch_pad.push(ch);
              State::Decimal
            },
            ch => {
              scratch_pad.push(ch);
              State::BoolOrIdent
            }
          };

          shift!();
        },

        State::Hexadecimal => {
          match ch {
            '.' => return err!(ParseErrorKind::DotInNonDecimalNumeric),
            '_' => (),
            c @ '(' | c @ ')' | c if c.is_whitespace() => {
              if let Ok(n) = i64::from_str_radix(&scratch_pad, 16) {
                let final_n = if negative { -1 } else { 1 } * n;
                push_lex!(Lexeme::Integer(final_n));
              } else {
                return err!(ParseErrorKind::InvalidNumber);
              }

              negative = false;
              scratch_pad = String::new();
              state = State::Start;
              unshift!();
              continue;
            },
            c if c.is_digit(16) => scratch_pad.push(ch),
            _ => return err!(ParseErrorKind::NonHexCharInHex),
          }

          shift!();
        },

        State::Binary => {
          match ch {
            '.' => return err!(ParseErrorKind::DotInNonDecimalNumeric),
            '_' => (),
            c @ '(' | c @ ')' | c if c.is_whitespace() => {
              if let Ok(n) = i64::from_str_radix(&scratch_pad, 2) {
                let final_n = if negative { -1 } else { 1 } * n;
                push_lex!(Lexeme::Integer(final_n));
              } else {
                return err!(ParseErrorKind::InvalidNumber);
              }

              negative = false;
              scratch_pad = String::new();
              state = State::Start;
              unshift!();
              continue;
            },
            c if c.is_digit(2) => scratch_pad.push(ch),
            _ => return err!(ParseErrorKind::NonBinCharInBin),
          }

          shift!();
        },

        State::Decimal => {
          let mut do_conversion = false;
          match ch {
            '_' => (),
            '.' => scratch_pad.push('.'),
            '(' | ')' => do_conversion = true,
            c if c.is_whitespace() => do_conversion = true,
            c if c.is_digit(10) => scratch_pad.push(c),
            _ => return err!(ParseErrorKind::NonDecCharInDec),
          }

          if do_conversion {
            if scratch_pad.contains('.') {
              // if there's a . then it's a float
              if let Ok(n) = f64::from_str(&scratch_pad) {
                let final_n = if negative { -1.0 } else { 1.0 } * n;
                push_lex!(Lexeme::Float(final_n));
              } else {
                return err!(ParseErrorKind::InvalidNumber);
              }
            } else {
              // if there's no . then it's an integer
              if let Ok(n) = i64::from_str_radix(&scratch_pad, 10) {
                let final_n = if negative { -1 } else { 1 } * n;
                push_lex!(Lexeme::Integer(final_n));
              } else {
                return err!(ParseErrorKind::InvalidNumber);
              }
            }

            negative = false;
            scratch_pad = String::new();
            state = State::Start;
            unshift!();
          } else {
            shift!();
          }
        },
      }
    }

    Ok(items)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    parsing::ParseErrorKind::*,
    vm::VM,
  };

  macro_rules! lex_str {
    ($vm:expr, $s:expr) => {
      $vm
        .lex($s.chars())
        .unwrap()
        .into_iter()
        .map(|li| li.0)
        .collect::<Vec<_>>()
    };
  }

  macro_rules! lex_err {
    ($vm:expr, $s:expr) => {
      $vm.lex($s.chars()).unwrap_err()
    };
  }

  #[test]
  fn empty_string_produces_no_lexemes() {
    let mut vm = VM::new();

    let expected: Vec<Lexeme> = Vec::new();
    let actual = lex_str!(vm, "");
    assert_eq!(expected, actual);
  }

  #[test]
  fn lexeme_lparen() {
    let mut vm = VM::new();

    let expected = vec![Lexeme::LParen];
    let actual = lex_str!(vm, "(");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::LParen, Lexeme::LParen];
    let actual_double = lex_str!(vm, "((");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_rparen() {
    let mut vm = VM::new();

    let expected = vec![Lexeme::RParen];
    let actual = lex_str!(vm, ")");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::RParen, Lexeme::RParen];
    let actual_double = lex_str!(vm, "))");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_quote() {
    let mut vm = VM::new();

    let expected = vec![Lexeme::Quote];
    let actual = lex_str!(vm, "'");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::Quote, Lexeme::Quote];
    let actual_double = lex_str!(vm, "''");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_dot() {
    let mut vm = VM::new();

    let expected = vec![Lexeme::Dot];
    let actual = lex_str!(vm, ".");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::Dot, Lexeme::Dot];
    let actual_double = lex_str!(vm, ". .");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_symbol() {
    let mut vm = VM::new();

    let actual = lex_str!(vm, "test");
    let expected = vec![Lexeme::Symbol(vm.symbols.get("test").unwrap())];
    assert_eq!(expected, actual);

    let actual_double = lex_str!(vm, "test toast");
    let expected_double = vec![
      Lexeme::Symbol(vm.symbols.get("test").unwrap()),
      Lexeme::Symbol(vm.symbols.get("toast").unwrap()),
    ];
    assert_eq!(expected_double, actual_double);

    let actual_pound = lex_str!(vm, "#");
    let expected_pound = vec![Lexeme::Symbol(vm.symbols.get("#").unwrap())];
    assert_eq!(expected_pound, actual_pound);

    let actual_dot_prefix = lex_str!(vm, ".e");
    let expected_dot_prefix = vec![Lexeme::Symbol(vm.symbols.get(".e").unwrap())];
    assert_eq!(expected_dot_prefix, actual_dot_prefix);

    let actual_sym_with_number = lex_str!(vm, ":3");
    let expected_sym_with_number = vec![Lexeme::Symbol(vm.symbols.get(":3").unwrap())];
    assert_eq!(expected_sym_with_number, actual_sym_with_number);

    // should these produce an error?
    let actual_fake_true = lex_str!(vm, "#tr");
    let expected_fake_true = vec![Lexeme::Symbol(vm.symbols.get("#tr").unwrap())];
    assert_eq!(expected_fake_true, actual_fake_true);
  }

  #[test]
  fn lexeme_string() {
    let mut vm = VM::new();

    let expected = vec![Lexeme::String("test".into())];
    let actual = lex_str!(vm, "\"test\"");
    assert_eq!(expected, actual);

    let expected_empty = vec![Lexeme::String("".into())];
    let actual_empty = lex_str!(vm, "\"\"");
    assert_eq!(expected_empty, actual_empty);
  }

  #[test]
  fn lexeme_boolean() {
    let mut vm = VM::new();

    let expected_true = vec![Lexeme::Boolean(true)];
    let actual_true = lex_str!(vm, "#t");
    assert_eq!(expected_true, actual_true);

    let actual_long_true = lex_str!(vm, "#true");
    assert_eq!(expected_true, actual_long_true);

    let expected_false = vec![Lexeme::Boolean(false)];
    let actual_false = lex_str!(vm, "#f");
    assert_eq!(expected_false, actual_false);

    let actual_long_false = lex_str!(vm, "#false");
    assert_eq!(expected_false, actual_long_false);
  }

  #[test]
  fn lexeme_integer_from_decimal() {
    let mut vm = VM::new();

    let expected_int = vec![Lexeme::Integer(420)];
    let actual_int = lex_str!(vm, "420");
    assert_eq!(expected_int, actual_int);

    let expected_negative_int = vec![Lexeme::Integer(-420)];
    let actual_negative_int = lex_str!(vm, "-420");
    assert_eq!(expected_negative_int, actual_negative_int);

    let expected_zero_prefix_int = vec![Lexeme::Integer(420)];
    let actual_zero_prefix_int = lex_str!(vm, "0420");
    assert_eq!(expected_zero_prefix_int, actual_zero_prefix_int);

    let expected_zero_prefix_negative_int = vec![Lexeme::Integer(-420)];
    let actual_zero_prefix_negative_int = lex_str!(vm, "-0420");
    assert_eq!(
      expected_zero_prefix_negative_int,
      actual_zero_prefix_negative_int,
    );

    let expected_underscored_int = vec![Lexeme::Integer(1_000_000)];
    let actual_underscored_int = lex_str!(vm, "1_000_000");
    assert_eq!(expected_underscored_int, actual_underscored_int);

    let illegal_decimal = lex_err!(vm, "35a7");
    assert_eq!(NonDecCharInDec, illegal_decimal.0);
  }

  #[test]
  fn lexeme_integer_from_hexadecimal() {
    let mut vm = VM::new();

    let expected_hex = vec![Lexeme::Integer(255)];
    let actual_hex = lex_str!(vm, "0xff");
    assert_eq!(expected_hex, actual_hex);

    let actual_underscored_hex = lex_str!(vm, "0xf_f");
    assert_eq!(expected_hex, actual_underscored_hex);

    let not_hex = lex_err!(vm, "0x");
    assert_eq!(InvalidNumber, not_hex.0);

    let illegal_hex = lex_err!(vm, "0xg");
    assert_eq!(NonHexCharInHex, illegal_hex.0);
  }

  #[test]
  fn lexeme_integer_from_binary() {
    let mut vm = VM::new();

    let expected_bin = vec![Lexeme::Integer(6)];
    let actual_bin = lex_str!(vm, "0b0110");
    assert_eq!(expected_bin, actual_bin);

    let actual_underscored_bin = lex_str!(vm, "0b0000_0110");
    assert_eq!(expected_bin, actual_underscored_bin);

    let not_bin = lex_err!(vm, "0b");
    assert_eq!(InvalidNumber, not_bin.0);

    let illegal_bin = lex_err!(vm, "0b37");
    assert_eq!(NonBinCharInBin, illegal_bin.0);
  }

  #[test]
  fn lexeme_float() {
    let mut vm = VM::new();

    let expected_float = vec![Lexeme::Float(0.5)];
    let actual_float = lex_str!(vm, "0.5");
    assert_eq!(expected_float, actual_float);

    let actual_float_dot_prefix = lex_str!(vm, ".5");
    assert_eq!(expected_float, actual_float_dot_prefix);

    let expected_float_dot_postfix = vec![Lexeme::Float(5.0)];
    let actual_float_dot_postfix = lex_str!(vm, "5.");
    assert_eq!(expected_float_dot_postfix, actual_float_dot_postfix);

    let not_float = lex_err!(vm, "0.3.4");
    assert_eq!(InvalidNumber, not_float.0);
  }

  #[test]
  fn list_of_everything() {
    let mut vm = VM::new();

    let actual_list = lex_str!(vm, "'(print #f \"hello!!\" 0xff . 10.)");
    let expected_list = vec![
      Lexeme::Quote,
      Lexeme::LParen,
      Lexeme::Symbol(vm.symbols.get("print").unwrap()),
      Lexeme::Boolean(false),
      Lexeme::String("hello!!".into()),
      Lexeme::Integer(255),
      Lexeme::Dot,
      Lexeme::Float(10.0),
      Lexeme::RParen,
    ];
    assert_eq!(expected_list, actual_list);
  }

  #[test]
  fn list_of_anything() {
    let mut vm = VM::new();

    let expected_nil = vec![
      Lexeme::LParen,
      Lexeme::RParen,
    ];
    let actual_nil = lex_str!(vm, "()");
    assert_eq!(expected_nil, actual_nil);

    let actual_sym = lex_str!(vm, "(uwu)");
    let expected_sym = vec![
      Lexeme::LParen,
      Lexeme::Symbol(vm.symbols.get("uwu").unwrap()),
      Lexeme::RParen,
    ];
    assert_eq!(expected_sym, actual_sym);

    let expected_bool = vec![
      Lexeme::LParen,
      Lexeme::Boolean(true),
      Lexeme::RParen,
    ];
    let actual_bool = lex_str!(vm, "(#t)");
    assert_eq!(expected_bool, actual_bool);

    let expected_str = vec![
      Lexeme::LParen,
      Lexeme::String("owo".into()),
      Lexeme::RParen,
    ];
    let actual_str = lex_str!(vm, "(\"owo\")");
    assert_eq!(expected_str, actual_str);

    let expected_int = vec![
      Lexeme::LParen,
      Lexeme::Integer(300),
      Lexeme::RParen,
    ];
    let actual_int = lex_str!(vm, "(300)");
    assert_eq!(expected_int, actual_int);

    let expected_float = vec![
      Lexeme::LParen,
      Lexeme::Float(0.15),
      Lexeme::RParen,
    ];
    let actual_float = lex_str!(vm, "(.15)");
    assert_eq!(expected_float, actual_float);
  }
}

