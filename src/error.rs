use thiserror::Error;

#[derive(Debug, Error)]
pub enum ArithmeticError {
  #[error("non-numeric data given where a number was expected")]
  NonNumericArgument,
}

#[derive(Debug, Error)]
#[error("???")]
pub struct UnspecifiedError;

#[derive(Debug, Error)]
pub enum EvalError {
  #[error("non-function values cannot be applied")]
  NonFunctionApplication,
  #[error("attempted to evaluate an unbound symbol")]
  UnboundSymbol,
  #[error("incorrect number of arguments given for special form")]
  InvalidSpecialForm,
  #[error("lambda name must be a symbol")]
  InvalidLambdaName,
  #[error("parameters must be symbols")]
  InvalidParameter,
  #[error("expression must be a formal parameter list")]
  InvalidParameterList,
}

