use regex_automata::{
  Anchored,
  dfa::{Automaton, dense::DFA},
  util::{
    lazy::Lazy,
    primitives::{PatternID, StateID},
    wire::AlignAs,
  },
};
use crate::{
  data::{Data, SymbolTable},
  parsing::{Info, /*ParseError, ParseErrorKind*/},
};

#[derive(Debug)]
pub enum Lexeme {
  LParen,
  RParen,
  Quote,
  Dot,
  Data(Data),
}

#[derive(Debug)]
pub struct LexItem(pub Lexeme, pub Info);

// precompiled regex
static RE: Lazy<DFA<&'static [u32]>> = Lazy::new(|| {
  static ALIGNED: &AlignAs<[u8], u32> = &AlignAs {
    _align: [],
    bytes: *include_bytes!(concat!(env!("OUT_DIR"), "/dfa.bin")),
  };

  DFA::from_bytes(&ALIGNED.bytes).unwrap().0
});

pub struct StreamLexer<'a> {
  symbol_table: &'a mut SymbolTable,
  start_state: StateID,
  state: StateID,
  scratch_pad: String,
  strongest_match: Option<(PatternID, usize)>, // pattern and length of the match
  consumed_chars: usize,
}

impl<'a> StreamLexer<'a> {
  pub fn new(symbol_table: &'a mut SymbolTable) -> Self {
    let start_state = RE.universal_start_state(Anchored::Yes)
      .expect("DFA patterns must not start with look-around");
    Self {
      symbol_table,
      start_state,
      state: start_state,
      scratch_pad: String::new(),
      strongest_match: None,
      consumed_chars: 0,
    }
  }

  pub fn reset(&mut self) {
    self.state = self.start_state;
    self.scratch_pad.clear();
    self.strongest_match = None;
    self.consumed_chars = 0;
  }

  pub fn push<T: AsRef<str>>(
    &mut self,
    lexeme_store: &mut Vec<LexItem>,
    tokens: T,
  ) -> Result<(), ()> {
    //self.scratch_pad.push(token);
    //self.state = RE.next_state(self.state, )
    //self.lex()
    todo!()
  }

  pub fn end(
    &mut self,
    lexeme_store: &mut Vec<LexItem>,
  ) -> Result<(), ()> {
    self.state = RE.next_eoi_state(self.state);
    let res = self.lex(lexeme_store);
    self.reset();
    res
  }

  fn lex(&mut self, target: &mut Vec<LexItem>) -> Result<(), ()> {
    if !RE.is_special_state(self.state) {
      return Ok(());
    } else if RE.is_quit_state(self.state) {
      unreachable!();
    } else if RE.is_match_state(self.state) {
      // one or more matches have been found (but not necessarily the best one)
      for i in 0..RE.match_len(self.state) {
        let pattern = (RE.match_pattern(self.state, i), self.consumed_chars);
        self.strongest_match = Some(self.strongest_match
          .map_or(pattern, |old| if pattern.0 < old.0 { pattern } else { old }));
      }
    } else if RE.is_dead_state(self.state) {
      // no more matches can be made, so lex the best one
      if self.strongest_match.is_none() {
        return Err(());
      }
      let (matched_pattern, matched_chars) = self.strongest_match.unwrap();

      macro_rules! push_lex {
        ($lex:expr) => {
          target.push(LexItem($lex, Info {
            line: 0, //NYI
            col: 0, //NYI
            boundary_col: 0, //NYI
          }))
        };
      }

      match matched_pattern.as_usize() {
      /*        Comment */  0 => (),
      /*     Whitespace */  1 => (),
      /*         LParen */  2 => { push_lex!(Lexeme::LParen); }
      /*         RParen */  3 => { push_lex!(Lexeme::RParen); }
      /*          Quote */  4 => { push_lex!(Lexeme::Quote); }
      /*  Boolean(true) */  5 => { push_lex!(Lexeme::Data(Data::Boolean(true))); }
      /* Boolean(false) */  6 => { push_lex!(Lexeme::Data(Data::Boolean(false))); }
      /*            Dot */  7 => { push_lex!(Lexeme::Dot); },
      /*     Identifier */  8 => todo!(),
      /* Extended Ident */  9 => todo!(),
      /*         String */ 10 => todo!(),
      /*          Float */ 11 => todo!(),
      /*    Hexadecimal */ 12 => todo!(),
      /*         Binary */ 13 => todo!(),
      /*        Decimal */ 14 => todo!(),
                            _ => unreachable!(),
      }

      // check if we need to re-consume any bytes
      if self.scratch_pad.len() > matched_chars {
        let reuse_pad = Box::from(&self.scratch_pad[matched_chars..]);
        self.reset();
        self.push(target, &reuse_pad)?;
      }

      self.reset();
    }

    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::parsing::ParseErrorKind::*;

  macro_rules! lex_str {
    ($s:expr) => {{
      let (infos, syms) = lex($s.chars()).unwrap();
      let lexs = infos
        .into_iter()
        .map(|li| li.0)
        .collect::<Vec<_>>();
      (lexs, syms)
    }};
  }

  macro_rules! lex_err {
    ($s:expr) => {
      lex($s.chars()).unwrap_err()
    };
  }

  #[test]
  fn empty_string_produces_no_lexemes() {
    let expected: Vec<Lexeme> = Vec::new();
    let (actual, _) = lex_str!("");
    assert_eq!(expected, actual);
  }

  #[test]
  fn lexeme_lparen() {
    let expected = vec![Lexeme::LParen];
    let (actual, _) = lex_str!("(");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::LParen, Lexeme::LParen];
    let (actual_double, _) = lex_str!("((");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_rparen() {
    let expected = vec![Lexeme::RParen];
    let (actual, _) = lex_str!(")");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::RParen, Lexeme::RParen];
    let (actual_double, _) = lex_str!("))");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_quote() {
    let expected = vec![Lexeme::Quote];
    let (actual, _) = lex_str!("'");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::Quote, Lexeme::Quote];
    let (actual_double, _) = lex_str!("''");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_dot() {
    let expected = vec![Lexeme::Dot];
    let (actual, _) = lex_str!(".");
    assert_eq!(expected, actual);

    let expected_double = vec![Lexeme::Dot, Lexeme::Dot];
    let (actual_double, _) = lex_str!(". .");
    assert_eq!(expected_double, actual_double);
  }

  #[test]
  fn lexeme_symbol() {
    let (actual, symbols) = lex_str!("test");
    let expected = vec![Lexeme::Symbol(symbols.get("test").unwrap())];
    assert_eq!(expected, actual);

    let (actual_double, symbols_double) = lex_str!("test toast");
    let expected_double = vec![
      Lexeme::Symbol(symbols_double.get("test").unwrap()),
      Lexeme::Symbol(symbols_double.get("toast").unwrap()),
    ];
    assert_eq!(expected_double, actual_double);

    let (actual_pound, symbols_pound) = lex_str!("#");
    let expected_pound = vec![Lexeme::Symbol(symbols_pound.get("#").unwrap())];
    assert_eq!(expected_pound, actual_pound);

    let (actual_dot_prefix, symbols_dot_prefix) = lex_str!(".e");
    let expected_dot_prefix = vec![Lexeme::Symbol(symbols_dot_prefix.get(".e").unwrap())];
    assert_eq!(expected_dot_prefix, actual_dot_prefix);

    let (actual_sym_with_number, symbols_sym_w_n) = lex_str!(":3");
    let expected_sym_with_number = vec![Lexeme::Symbol(symbols_sym_w_n.get(":3").unwrap())];
    assert_eq!(expected_sym_with_number, actual_sym_with_number);

    // should these produce an error?
    let (actual_fake_true, symbols_fake_true) = lex_str!("#tr");
    let expected_fake_true = vec![Lexeme::Symbol(symbols_fake_true.get("#tr").unwrap())];
    assert_eq!(expected_fake_true, actual_fake_true);
  }

  #[test]
  fn lexeme_string() {
    let expected = vec![Lexeme::String("test".into())];
    let (actual, _) = lex_str!("\"test\"");
    assert_eq!(expected, actual);

    let expected_empty = vec![Lexeme::String("".into())];
    let (actual_empty, _) = lex_str!("\"\"");
    assert_eq!(expected_empty, actual_empty);
  }

  #[test]
  fn lexeme_boolean() {
    let expected_true = vec![Lexeme::Boolean(true)];
    let (actual_true, _) = lex_str!("#t");
    assert_eq!(expected_true, actual_true);

    let (actual_long_true, _) = lex_str!("#true");
    assert_eq!(expected_true, actual_long_true);

    let expected_false = vec![Lexeme::Boolean(false)];
    let (actual_false, _) = lex_str!("#f");
    assert_eq!(expected_false, actual_false);

    let (actual_long_false, _) = lex_str!("#false");
    assert_eq!(expected_false, actual_long_false);
  }

  #[test]
  fn lexeme_integer_from_decimal() {
    let expected_int = vec![Lexeme::Integer(420)];
    let (actual_int, _) = lex_str!("420");
    assert_eq!(expected_int, actual_int);

    let expected_negative_int = vec![Lexeme::Integer(-420)];
    let (actual_negative_int, _) = lex_str!("-420");
    assert_eq!(expected_negative_int, actual_negative_int);

    let expected_zero_prefix_int = vec![Lexeme::Integer(420)];
    let (actual_zero_prefix_int, _) = lex_str!("0420");
    assert_eq!(expected_zero_prefix_int, actual_zero_prefix_int);

    let expected_zero_prefix_negative_int = vec![Lexeme::Integer(-420)];
    let (actual_zero_prefix_negative_int , _)= lex_str!("-0420");
    assert_eq!(
      expected_zero_prefix_negative_int,
      actual_zero_prefix_negative_int,
    );

    let expected_underscored_int = vec![Lexeme::Integer(1_000_000)];
    let (actual_underscored_int, _) = lex_str!("1_000_000");
    assert_eq!(expected_underscored_int, actual_underscored_int);

    let illegal_decimal = lex_err!("35a7");
    assert_eq!(NonDecCharInDec, illegal_decimal.0);
  }

  #[test]
  fn lexeme_integer_from_hexadecimal() {
    let expected_hex = vec![Lexeme::Integer(255)];
    let (actual_hex, _) = lex_str!("0xff");
    assert_eq!(expected_hex, actual_hex);

    let (actual_underscored_hex, _) = lex_str!("0xf_f");
    assert_eq!(expected_hex, actual_underscored_hex);

    let not_hex = lex_err!("0x");
    assert_eq!(InvalidNumber, not_hex.0);

    let illegal_hex = lex_err!("0xg");
    assert_eq!(NonHexCharInHex, illegal_hex.0);
  }

  #[test]
  fn lexeme_integer_from_binary() {
    let expected_bin = vec![Lexeme::Integer(6)];
    let (actual_bin, _) = lex_str!("0b0110");
    assert_eq!(expected_bin, actual_bin);

    let (actual_underscored_bin, _) = lex_str!("0b0000_0110");
    assert_eq!(expected_bin, actual_underscored_bin);

    let not_bin = lex_err!("0b");
    assert_eq!(InvalidNumber, not_bin.0);

    let illegal_bin = lex_err!("0b37");
    assert_eq!(NonBinCharInBin, illegal_bin.0);
  }

  #[test]
  fn lexeme_float() {
    let expected_float = vec![Lexeme::Float(0.5)];
    let (actual_float, _) = lex_str!("0.5");
    assert_eq!(expected_float, actual_float);

    let (actual_float_dot_prefix, _) = lex_str!(".5");
    assert_eq!(expected_float, actual_float_dot_prefix);

    let expected_float_dot_postfix = vec![Lexeme::Float(5.0)];
    let (actual_float_dot_postfix, _) = lex_str!("5.");
    assert_eq!(expected_float_dot_postfix, actual_float_dot_postfix);

    let not_float = lex_err!("0.3.4");
    assert_eq!(InvalidNumber, not_float.0);
  }

  #[test]
  fn list_of_everything() {
    let (actual_list, symbols) = lex_str!("'(print #f \"hello!!\" 0xff . 10.)");
    let expected_list = vec![
      Lexeme::Quote,
      Lexeme::LParen,
      Lexeme::Symbol(symbols.get("print").unwrap()),
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
    let expected_nil = vec![
      Lexeme::LParen,
      Lexeme::RParen,
    ];
    let (actual_nil, _) = lex_str!("()");
    assert_eq!(expected_nil, actual_nil);

    let (actual_sym, symbols_sym) = lex_str!("(uwu)");
    let expected_sym = vec![
      Lexeme::LParen,
      Lexeme::Symbol(symbols_sym.get("uwu").unwrap()),
      Lexeme::RParen,
    ];
    assert_eq!(expected_sym, actual_sym);

    let expected_bool = vec![
      Lexeme::LParen,
      Lexeme::Boolean(true),
      Lexeme::RParen,
    ];
    let (actual_bool, _) = lex_str!("(#t)");
    assert_eq!(expected_bool, actual_bool);

    let expected_str = vec![
      Lexeme::LParen,
      Lexeme::String("owo".into()),
      Lexeme::RParen,
    ];
    let (actual_str, _) = lex_str!("(\"owo\")");
    assert_eq!(expected_str, actual_str);

    let expected_int = vec![
      Lexeme::LParen,
      Lexeme::Integer(300),
      Lexeme::RParen,
    ];
    let (actual_int, _) = lex_str!("(300)");
    assert_eq!(expected_int, actual_int);

    let expected_float = vec![
      Lexeme::LParen,
      Lexeme::Float(0.15),
      Lexeme::RParen,
    ];
    let (actual_float, _) = lex_str!("(.15)");
    assert_eq!(expected_float, actual_float);
  }
}

