use thiserror::Error;

#[derive(Debug, Error)]
pub enum ArithmeticError {
  #[error("non-numeric data given where a number was expected")]
  NonNumericArgument,
}


#[derive(Debug, Error)]
#[error("???")]
pub struct UnspecifiedError;

