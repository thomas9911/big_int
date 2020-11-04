use crate::Sign;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, PartialEq)]
pub enum Error {
    IntegerError(IntegerError),
    ParseError(ParseError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Error::*;

        match self {
            ParseError(e) => write!(f, "{}", e),
            IntegerError(e) => write!(f, "{}", e),
        }
    }
}

impl From<ParseError> for Error {
    fn from(err: ParseError) -> Error {
        Error::ParseError(err)
    }
}

#[derive(Debug, PartialEq)]
pub enum ParseError {
    InvalidPart,
    NotExponent,
    InvalidFormat,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ParseError::*;

        match self {
            InvalidPart => write!(f, "first part not a float"),
            NotExponent => write!(f, "exponent part not a integer"),
            InvalidFormat => write!(f, "invalid format"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum IntegerError {
    Infinity(Sign),
    Nan,
}

impl std::fmt::Display for IntegerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use IntegerError::*;

        match self {
            Infinity(Sign::Pos) => write!(f, "Infinity does not fit into an integer"),
            Infinity(Sign::Neg) => write!(f, "Negative infinity does not fit into an integer"),
            Nan => write!(f, "Not an Number cannot fit into an integer"),
        }
    }
}

impl std::error::Error for IntegerError {}
impl std::error::Error for ParseError {}
impl std::error::Error for Error {}
