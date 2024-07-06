use std::{rc::Rc, str::FromStr};

use crate::{
  data::Data,
  error::{LexError, SourceInfo, VMError},
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
  Complex(f64, f64),
  Rational(i64, u64),
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
      (Float(l), Float(r)) => (l - r).abs() < 0.0000001,
      (Rational(ln, ld), Rational(rn, rd)) => {
        *ln * *rd as i64 == *rn * *ld as i64
      },
      (Complex(lr, li), Complex(rr, ri)) => {
        (lr - rr).abs() < 0.0000001 && (li - ri).abs() < 0.0000001
      },
      _ => false,
    }
  }
}
impl Eq for Lexeme {}

#[derive(Debug)]
pub struct LexItem(pub Lexeme, pub SourceInfo);

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
  Decimal {
    complex: bool,
    real_part: f64,
    complex_complete: bool,
    rational: bool,
    numerator: i64,
  },
  Binary,
}

impl State {
  fn decimal() -> Self {
    Self::Decimal {
      complex: false,
      real_part: 0.0,
      complex_complete: false,
      rational: false,
      numerator: 0,
    }
  }
}

impl VM {
  pub fn lex<I>(&mut self, source: I) -> Result<Vec<LexItem>, VMError>
  where
    I: IntoIterator<Item = char>,
  {
    let mut items = Vec::new();
    let mut state = State::Start;
    // append a " " to end of input so that lexer can finish up
    let mut chars = source.into_iter().chain(" ".chars()).peekable();
    let mut line = 0u32;
    let mut col = 0u32;
    let mut boundary_col = 0u32;
    let mut scratch_pad = String::new();
    // for unshift
    let mut prev_line: u32;
    let mut prev_col: u32;
    let mut prev_boundary_col = 0u32;
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
      {
        shifted = false;
      }

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
          #[allow(unused_assignments)]
          {
            shifted = true;
          }
          line = prev_line;
          col = prev_col;
          boundary_col = prev_boundary_col;
        };
      }

      // pushes a lexeme into the result list, along with all the metadata
      macro_rules! push_lex {
        ($x:expr) => {
          items.push(LexItem(
            $x,
            SourceInfo {
              line,
              col,
              boundary_col,
            },
          ))
        };
      }

      // creates and wraps an error
      macro_rules! err {
        ($x:expr) => {
          Err(VMError(
            Box::new($x),
            SourceInfo {
              line,
              col,
              boundary_col,
            },
          ))
        };
      }

      // execute state machine for this iteration
      match state {
        State::Start => {
          match ch {
            ';' => state = State::Comment,
            '(' => push_lex!(Lexeme::LParen),
            ')' => push_lex!(Lexeme::RParen),
            '\'' => push_lex!(Lexeme::Quote),
            '"' => state = State::String,
            '0' => state = State::ZeroPrefixNumeric,
            '-' => state = State::NegativeOrIdent,
            '.' => {
              scratch_pad.push('.');
              state = State::FloatOrDotIdent;
            },
            c if c.is_whitespace() => {},
            c if c.is_digit(10) => {
              state = State::decimal();
              scratch_pad.push(c);
            },
            c if is_identifier_char(c) => {
              state = State::BoolOrIdent;
              scratch_pad.push(c);
            },
            c => {
              return err!(LexError::IllegalCharacter(c));
            },
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
          if is_identifier_char(ch) {
            scratch_pad.push(ch);
            shift!();
          } else {
            match scratch_pad.as_str() {
              "#t" | "#true" => push_lex!(Lexeme::Boolean(true)),
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
              state = State::decimal();
            },
            c => {
              negative = false;
              scratch_pad.push('-');
              scratch_pad.push(c);
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
              state = State::decimal();
            },
            'i' => {
              push_lex!(Lexeme::Complex(0.0, 0.0));
              negative = false;
              state = State::Start;
            },
            '/' => {
              negative = false;
              state = State::Decimal {
                complex: false,
                real_part: 0.0,
                complex_complete: false,
                rational: true,
                numerator: 0,
              };
            },
            c if c.is_numeric() => {
              scratch_pad.push(c);
              state = State::decimal();
            },
            c if c.is_alphabetic() => return err!(LexError::InvalidNumber),
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
            ch @ '(' | ch @ ')' | ch if ch.is_whitespace() => {
              scratch_pad = String::new();
              push_lex!(Lexeme::Dot);
              State::Start
            },
            ch if ch.is_numeric() => {
              scratch_pad.push(ch);
              State::decimal()
            },
            ch => {
              scratch_pad.push(ch);
              State::BoolOrIdent
            },
          };

          shift!();
        },

        State::Hexadecimal => {
          match ch {
            '.' => return err!(LexError::DotInNonDecimalNumeric),
            '_' => (),
            c @ '(' | c @ ')' | c if c.is_whitespace() => {
              if let Ok(n) = i64::from_str_radix(&scratch_pad, 16) {
                let final_n = if negative { -1 } else { 1 } * n;
                push_lex!(Lexeme::Integer(final_n));
              } else {
                return err!(LexError::InvalidNumber);
              }

              negative = false;
              scratch_pad = String::new();
              state = State::Start;
              unshift!();
              continue;
            },
            c if c.is_digit(16) => scratch_pad.push(ch),
            _ => return err!(LexError::NonHexCharInHex),
          }

          shift!();
        },

        State::Binary => {
          match ch {
            '.' => return err!(LexError::DotInNonDecimalNumeric),
            '_' => (),
            c @ '(' | c @ ')' | c if c.is_whitespace() => {
              if let Ok(n) = i64::from_str_radix(&scratch_pad, 2) {
                let final_n = if negative { -1 } else { 1 } * n;
                push_lex!(Lexeme::Integer(final_n));
              } else {
                return err!(LexError::InvalidNumber);
              }

              negative = false;
              scratch_pad = String::new();
              state = State::Start;
              unshift!();
              continue;
            },
            c if c.is_digit(2) => scratch_pad.push(ch),
            _ => return err!(LexError::NonBinCharInBin),
          }

          shift!();
        },

        State::Decimal {
          ref mut complex,
          ref mut real_part,
          ref mut complex_complete,
          ref mut rational,
          ref mut numerator,
        } => {
          let conv_int = || {
            i64::from_str_radix(&scratch_pad, 10)
              .map(|n| if negative { -1 } else { 1 } * n)
              .or_else(|_| err!(LexError::InvalidNumber))
          };

          let conv_float = || {
            f64::from_str(&scratch_pad)
              .map(|n| if negative { -1.0 } else { 1.0 } * n)
              .or_else(|_| err!(LexError::InvalidNumber))
          };

          match ch {
            '_' => (),
            '.' => scratch_pad.push('.'),
            c @ '+' | c @ '-' => {
              if *complex {
                return err!(LexError::MalformedComplex);
              } else if *rational {
                return err!(LexError::MalformedRational);
              } else {
                *complex = true;
                *real_part = conv_float()?;
                negative = c == '-';
                scratch_pad = String::new();
              }
            },
            '/' => {
              if *complex {
                return err!(LexError::MalformedComplex);
              } else if *rational {
                return err!(LexError::MalformedRational);
              } else {
                *rational = true;
                *numerator = conv_int()?;
                negative = false;
                scratch_pad = String::new();
              }
            },
            'i' => {
              if !*complex_complete {
                *complex = true;
                *complex_complete = true;
              } else {
                return err!(LexError::NonDecCharInDec);
              }
            },
            c if c.is_whitespace() || c == ')' => {
              if *complex && !*complex_complete {
                return err!(LexError::MalformedComplex);
              } else if *complex {
                let imag_part = conv_float()?;
                push_lex!(Lexeme::Complex(*real_part, imag_part));
              } else if *rational {
                let denominator = conv_int()?;
                push_lex!(Lexeme::Rational(*numerator, denominator as u64));
              } else if let Ok(int) = conv_int() {
                push_lex!(Lexeme::Integer(int));
              } else {
                let float = conv_float()?;
                push_lex!(Lexeme::Float(float));
              }

              // reset state
              negative = false;
              scratch_pad = String::new();
              state = State::Start;
              unshift!();
              continue;
            },
            c if c.is_digit(10) => scratch_pad.push(c),
            _ => return err!(LexError::NonDecCharInDec),
          }

          shift!();
        },
      }
    }

    Ok(items)
  }
}

fn is_identifier_char(ch: char) -> bool {
  match ch {
    '\'' | '+' | '=' | '/' | '|' | ':' | '<' | '>' | ',' | '.' | '?' | '!'
    | '@' | '#' | '$' | '%' | '^' | '&' | '*' | '-' | '_' => true,
    ch if ch.is_alphanumeric() => true,
    _ => false,
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{error::LexError::*, vm::VM};

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
    let mut vm = VM::no_std();

    let expected: Vec<Lexeme> = Vec::new();
    let actual = lex_str!(vm, "");
    assert_eq!(expected, actual);
  }

  #[test]
  fn lexeme_lparen() {
    let mut vm = VM::no_std();

    let expected = vec![Lexeme::LParen];
    let actual = lex_str!(vm, "(");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::LParen, Lexeme::LParen];
    let actual_double = lex_str!(vm, "((");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_rparen() {
    let mut vm = VM::no_std();

    let expected = vec![Lexeme::RParen];
    let actual = lex_str!(vm, ")");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::RParen, Lexeme::RParen];
    let actual_double = lex_str!(vm, "))");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_quote() {
    let mut vm = VM::no_std();

    let expected = vec![Lexeme::Quote];
    let actual = lex_str!(vm, "'");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::Quote, Lexeme::Quote];
    let actual_double = lex_str!(vm, "''");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_dot() {
    let mut vm = VM::no_std();

    let expected = vec![Lexeme::Dot];
    let actual = lex_str!(vm, ".");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::Dot, Lexeme::Dot];
    let actual_double = lex_str!(vm, ". .");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_symbol() {
    let mut vm = VM::no_std();

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
    let expected_dot_prefix =
      vec![Lexeme::Symbol(vm.symbols.get(".e").unwrap())];
    assert_eq!(expected_dot_prefix, actual_dot_prefix);

    let actual_sym_with_number = lex_str!(vm, ":3");
    let expected_sym_with_number =
      vec![Lexeme::Symbol(vm.symbols.get(":3").unwrap())];
    assert_eq!(expected_sym_with_number, actual_sym_with_number);

    let actual_qmark = lex_str!(vm, "huh?");
    let expected_qmark = vec![Lexeme::Symbol(vm.symbols.get("huh?").unwrap())];
    assert_eq!(expected_qmark, actual_qmark);

    let actual_dashed = lex_str!(vm, "my-symbol");
    let expected_dashed =
      vec![Lexeme::Symbol(vm.symbols.get("my-symbol").unwrap())];
    assert_eq!(expected_dashed, actual_dashed);

    let actual_start_dashed = lex_str!(vm, "-Inf");
    println!("{:?}", actual_start_dashed);
    let expected_start_dashed =
      vec![Lexeme::Symbol(vm.symbols.get("-Inf").unwrap())];
    assert_eq!(expected_start_dashed, actual_start_dashed);

    // should these produce an error?
    let actual_fake_true = lex_str!(vm, "#tr");
    let expected_fake_true =
      vec![Lexeme::Symbol(vm.symbols.get("#tr").unwrap())];
    assert_eq!(expected_fake_true, actual_fake_true);
  }

  #[test]
  fn lexeme_string() {
    let mut vm = VM::no_std();

    let expected = vec![Lexeme::String("test".into())];
    let actual = lex_str!(vm, "\"test\"");
    assert_eq!(expected, actual);

    let expected_empty = vec![Lexeme::String("".into())];
    let actual_empty = lex_str!(vm, "\"\"");
    assert_eq!(expected_empty, actual_empty);
  }

  #[test]
  fn lexeme_boolean() {
    let mut vm = VM::no_std();

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
    let mut vm = VM::no_std();

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
    assert_eq!(
      NonDecCharInDec,
      *illegal_decimal.0.downcast::<LexError>().unwrap()
    );
  }

  #[test]
  fn lexeme_integer_from_hexadecimal() {
    let mut vm = VM::no_std();

    let expected_hex = vec![Lexeme::Integer(255)];
    let actual_hex = lex_str!(vm, "0xff");
    assert_eq!(expected_hex, actual_hex);

    let actual_underscored_hex = lex_str!(vm, "0xf_f");
    assert_eq!(expected_hex, actual_underscored_hex);

    let not_hex = lex_err!(vm, "0x");
    assert_eq!(InvalidNumber, *not_hex.0.downcast::<LexError>().unwrap());

    let illegal_hex = lex_err!(vm, "0xg");
    assert_eq!(
      NonHexCharInHex,
      *illegal_hex.0.downcast::<LexError>().unwrap()
    );
  }

  #[test]
  fn lexeme_integer_from_binary() {
    let mut vm = VM::no_std();

    let expected_bin = vec![Lexeme::Integer(6)];
    let actual_bin = lex_str!(vm, "0b0110");
    assert_eq!(expected_bin, actual_bin);

    let actual_underscored_bin = lex_str!(vm, "0b0000_0110");
    assert_eq!(expected_bin, actual_underscored_bin);

    let not_bin = lex_err!(vm, "0b");
    assert_eq!(InvalidNumber, *not_bin.0.downcast::<LexError>().unwrap());

    let illegal_bin = lex_err!(vm, "0b37");
    assert_eq!(
      NonBinCharInBin,
      *illegal_bin.0.downcast::<LexError>().unwrap()
    );
  }

  #[test]
  fn lexeme_float() {
    let mut vm = VM::no_std();

    let expected_float = vec![Lexeme::Float(0.5)];
    let actual_float = lex_str!(vm, "0.5");
    assert_eq!(expected_float, actual_float);

    let actual_float_dot_prefix = lex_str!(vm, ".5");
    assert_eq!(expected_float, actual_float_dot_prefix);

    let expected_float_dot_postfix = vec![Lexeme::Float(5.0)];
    let actual_float_dot_postfix = lex_str!(vm, "5.");
    assert_eq!(expected_float_dot_postfix, actual_float_dot_postfix);

    let not_float = lex_err!(vm, "0.3.4");
    assert_eq!(InvalidNumber, *not_float.0.downcast::<LexError>().unwrap());
  }

  #[test]
  fn lexeme_rational() {
    let mut vm = VM::no_std();

    let expected_rat = vec![Lexeme::Rational(1, 5)];
    let actual_rat = lex_str!(vm, "1/5");
    assert_eq!(expected_rat, actual_rat);

    let expected_zrat = vec![Lexeme::Rational(0, 10)];
    let actual_zrat = lex_str!(vm, "0/10");
    assert_eq!(expected_zrat, actual_zrat);

    let expected_neg_rat = vec![Lexeme::Rational(-3, 10)];
    let actual_neg_rat = lex_str!(vm, "-3/10");
    assert_eq!(expected_neg_rat, actual_neg_rat);
  }

  #[test]
  fn lexeme_complex() {
    let mut vm = VM::no_std();

    let expected_comp = vec![Lexeme::Complex(1.3, 5.5)];
    let actual_comp = lex_str!(vm, "1.3+5.5i");
    assert_eq!(expected_comp, actual_comp);

    let expected_comp2 = vec![Lexeme::Complex(-1.3, -5.5)];
    let actual_comp2 = lex_str!(vm, "-1.3-5.5i");
    assert_eq!(expected_comp2, actual_comp2);

    let expected_comp3 = vec![Lexeme::Complex(0.0, -5.5)];
    let actual_comp3 = lex_str!(vm, "-5.5i");
    assert_eq!(expected_comp3, actual_comp3);
  }

  #[test]
  fn list_of_everything() {
    let mut vm = VM::no_std();

    let actual_list = lex_str!(vm, "'(print? #f \"hello!!\" 0xff . 10.)");
    let expected_list = vec![
      Lexeme::Quote,
      Lexeme::LParen,
      Lexeme::Symbol(vm.symbols.get("print?").unwrap()),
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
    let mut vm = VM::no_std();

    let expected_nil = vec![Lexeme::LParen, Lexeme::RParen];
    let actual_nil = lex_str!(vm, "()");
    assert_eq!(expected_nil, actual_nil);

    let actual_sym = lex_str!(vm, "(uwu)");
    let expected_sym = vec![
      Lexeme::LParen,
      Lexeme::Symbol(vm.symbols.get("uwu").unwrap()),
      Lexeme::RParen,
    ];
    assert_eq!(expected_sym, actual_sym);

    let expected_bool =
      vec![Lexeme::LParen, Lexeme::Boolean(true), Lexeme::RParen];
    let actual_bool = lex_str!(vm, "(#t)");
    assert_eq!(expected_bool, actual_bool);

    let expected_str =
      vec![Lexeme::LParen, Lexeme::String("owo".into()), Lexeme::RParen];
    let actual_str = lex_str!(vm, "(\"owo\")");
    assert_eq!(expected_str, actual_str);

    let expected_int =
      vec![Lexeme::LParen, Lexeme::Integer(300), Lexeme::RParen];
    let actual_int = lex_str!(vm, "(300)");
    assert_eq!(expected_int, actual_int);

    let expected_float =
      vec![Lexeme::LParen, Lexeme::Float(0.15), Lexeme::RParen];
    let actual_float = lex_str!(vm, "(.15)");
    assert_eq!(expected_float, actual_float);
  }
}
