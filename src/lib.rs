#![deny(clippy::all)]
// #![deny(clippy::pedantic)]

use std::convert::TryFrom;
use std::num::FpCategory;
use std::ops::{Mul, Neg};

#[derive(Debug, PartialEq)]
/// container for special values used in `BigInt`
///
/// ```rust
/// use big_int::{BigInt, Special};
///
/// assert_eq!("Infinity", BigInt::from(Special::Inf).to_string());
/// assert_eq!("NaN", BigInt::from(Special::Nan).to_string());
/// assert_eq!("0", BigInt::from(Special::Zero).to_string());
/// ```
pub enum Special {
    Inf,
    Nan,
    Zero,
}

#[derive(Debug, PartialEq)]
pub enum Sign {
    Pos,
    Neg,
}

impl Neg for Sign {
    type Output = Sign;

    fn neg(self) -> Self {
        match self {
            Sign::Pos => Sign::Neg,
            Sign::Neg => Sign::Pos,
        }
    }
}

#[derive(Debug, PartialEq)]
/// Struct to store large numbers
///
/// ```rust
/// use big_int::BigInt;
///
/// let number = "1.25*10^15".parse::<BigInt>();
/// let the_same_number = BigInt::from_parts(1.25, 15);
/// let also_the_same_number: BigInt = 1250_000_000_000_000.0.into();
///  
/// assert_eq!(the_same_number, also_the_same_number);
/// assert_eq!(number, Ok(the_same_number));
/// assert_eq!(number, Ok(also_the_same_number));
/// ```
pub struct BigInt {
    // coefficient: 9.9999999999 -> 1.0
    coefficient: u64,
    sign: Sign,
    exponent: i32,
    special: Option<Special>,
    exponent_style: Option<String>,
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

impl std::error::Error for ParseError {}

const U64_STEP: f64 = 4.878_909_776_184_77e-19;
const U64_MAX: u64 = std::u64::MAX;
const DEFAULT_EXPONENT_STYLE: &str = "*10^";

impl BigInt {
    /// Creates a BigInt with the value 0
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("0", BigInt::zero().to_string())
    /// ```
    pub fn zero() -> BigInt {
        BigInt {
            special: Some(Special::Zero),
            ..Default::default()
        }
    }

    /// Creates a BigInt with the value 1
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("1", BigInt::one().to_string())
    /// ```
    pub fn one() -> BigInt {
        BigInt {
            coefficient: 0,
            sign: Sign::Pos,
            exponent: 0,
            special: None,
            exponent_style: None,
        }
    }

    /// Creates a BigInt containing `f64::INFINITY`
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("Infinity", BigInt::infinity().to_string())
    /// ```
    pub fn infinity() -> BigInt {
        BigInt {
            special: Some(Special::Inf),
            ..Default::default()
        }
    }

    /// Creates a BigInt containing `f64::NAN`
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("NaN", BigInt::nan().to_string())
    /// ```
    pub fn nan() -> BigInt {
        BigInt {
            special: Some(Special::Nan),
            ..Default::default()
        }
    }

    fn convert(input: f64) -> u64 {
        ((input - 1.0) / U64_STEP) as u64
    }

    fn convert_back(input: u64) -> f64 {
        (input as f64 * U64_STEP) + 1.0
    }

    /// Creates BigInt from a float and exponent part
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("3.14*10^20", BigInt::from_parts(3.14, 20).to_string())
    /// ```
    pub fn from_parts(coefficient: f64, exponent: i32) -> BigInt {
        let mut big_int = BigInt::from_float(coefficient);
        big_int.exponent += exponent;

        big_int
    }

    /// Creates BigInt from a float
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("3.14", BigInt::from_float(3.14).to_string())
    /// ```
    pub fn from_float(input: f64) -> BigInt {
        match input.classify() {
            FpCategory::Infinite => {
                if input.is_sign_positive() {
                    return Self::infinity();
                } else {
                    return -Self::infinity();
                };
            }
            FpCategory::Nan => return Self::nan(),
            FpCategory::Zero => return Self::zero(),
            _ => (),
        };

        if (input < 10.0) && (input >= 1.0) {
            let coefficient = Self::convert(input);
            return BigInt {
                coefficient,
                ..Default::default()
            };
        }

        if (input > -10.0) && (input <= -1.0) {
            let coefficient = Self::convert(-input);

            return BigInt {
                coefficient,
                sign: Sign::Neg,
                ..Default::default()
            };
        }

        if (input >= 10.0) || (input < -10.0) {
            let exponent = i32::try_from(input.abs().log10() as u64).expect("Too large exponent");
            let remainder = input / 10_f64.powi(exponent);

            let (coefficient, sign) = if remainder.is_sign_positive() {
                (Self::convert(remainder), Sign::Pos)
            } else {
                (Self::convert(-remainder), Sign::Neg)
            };

            return BigInt {
                coefficient,
                sign,
                exponent,
                ..Default::default()
            };
        }

        if input.abs() < 1.0 {
            let exponent = input.abs().log10().floor() as i32;
            let remainder = input / (10_f64.powi(exponent));

            return Self::from_parts(remainder, exponent);
        }

        unreachable!()
    }

    /// Casts `BigInt` to float.
    ///
    /// Large numbers that don't fit into f64 will turn into `f64::INFINITY`.
    /// Small numbers that don't fit into f64 will turn into 0.0.
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!(2.43, BigInt::from_parts(24.3, -1).to_float());
    /// assert_eq!(f64::INFINITY, BigInt::from_parts(4.3, 984512542).to_float());
    /// ```
    pub fn to_float(&self) -> f64 {
        match self {
            BigInt {
                special: Some(Special::Inf),
                sign: Sign::Pos,
                ..
            } => return f64::INFINITY,
            BigInt {
                special: Some(Special::Inf),
                sign: Sign::Neg,
                ..
            } => return -f64::INFINITY,
            BigInt {
                special: Some(Special::Nan),
                ..
            } => return f64::NAN,
            BigInt {
                special: Some(Special::Zero),
                ..
            } => return 0.0,
            _ => (),
        };

        let nmbr = Self::convert_back(self.coefficient);
        let power = 10_f64.powi(self.exponent);

        nmbr * power
    }

    /// extracts `BigInt` to parts.
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!((2.43, 0), BigInt::from_parts(24.3, -1).to_parts());
    ///
    /// let big_int = BigInt::parse("4.3*10^984512542").expect("invalid format");
    /// assert_eq!((4.3, 984512542), big_int.to_parts());
    /// ```
    pub fn to_parts(&self) -> (f64, i32) {
        match self {
            BigInt {
                special: Some(Special::Inf),
                sign: Sign::Pos,
                ..
            } => (f64::INFINITY, 0),
            BigInt {
                special: Some(Special::Inf),
                sign: Sign::Neg,
                ..
            } => (-f64::INFINITY, 0),
            BigInt {
                special: Some(Special::Nan),
                ..
            } => (f64::NAN, 0),
            BigInt {
                special: Some(Special::Zero),
                ..
            } => (0.0, 0),
            BigInt {
                coefficient,
                exponent,
                ..
            } => (Self::convert_back(*coefficient), *exponent),
        }
    }

    /// parses a `String` to a `BigInt`
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// let big_int = BigInt::parse("2.6*10^4").expect("invalid format");
    /// assert_eq!(26000.0, big_int.to_float());
    ///
    /// // can also be just a float.
    /// let big_int = BigInt::parse("15.51").expect("invalid format");
    /// assert_eq!(15.51, big_int.to_float());
    /// ```
    pub fn parse(input: &str) -> Result<BigInt, ParseError> {
        if let Ok(x) = input.parse::<f64>() {
            return Ok(Self::from_float(x));
        };

        let parts: Vec<_> = input.split(DEFAULT_EXPONENT_STYLE).collect();
        if parts.len() != 2 {
            return Err(ParseError::InvalidFormat);
        }

        let first = match parts[0].parse::<f64>() {
            Ok(x) => x,
            Err(_) => return Err(ParseError::InvalidPart),
        };

        let second = match parts[1].parse::<i32>() {
            Ok(x) => x,
            Err(_) => return Err(ParseError::NotExponent),
        };

        let big_int = Self::from_parts(first, second);

        Ok(big_int)
    }

    // operations

    /// The same as the `mul` function only can take a `Into<BigInt>` as its argument
    pub fn multiply<RHS: Into<BigInt>>(self, rhs: RHS) -> BigInt {
        let other: BigInt = rhs.into();
        self * other
    }

    /// Calculates the difference between the exponents
    ///
    /// This operation is fast because it is just a subtraction of two i32s
    pub fn power_difference<RHS: Into<BigInt>>(&self, rhs: RHS) -> i32 {
        self.exponent - rhs.into().exponent
    }
}

impl From<f64> for BigInt {
    fn from(input: f64) -> BigInt {
        Self::from_float(input)
    }
}

impl From<f32> for BigInt {
    fn from(input: f32) -> BigInt {
        Self::from_float(f64::from(input))
    }
}

impl From<(f64, i32)> for BigInt {
    fn from(input: (f64, i32)) -> BigInt {
        Self::from_parts(input.0, input.1)
    }
}

impl From<BigInt> for f64 {
    fn from(input: BigInt) -> f64 {
        input.to_float()
    }
}

impl From<BigInt> for f32 {
    fn from(input: BigInt) -> f32 {
        input.to_float() as f32
    }
}

impl std::convert::TryFrom<String> for BigInt {
    type Error = ParseError;

    fn try_from(input: String) -> Result<Self, Self::Error> {
        Self::try_from(input.as_str())
    }
}

impl std::convert::TryFrom<&str> for BigInt {
    type Error = ParseError;

    fn try_from(input: &str) -> Result<Self, Self::Error> {
        BigInt::parse(input)
    }
}

impl std::str::FromStr for BigInt {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        BigInt::parse(s)
    }
}

impl From<Special> for BigInt {
    fn from(input: Special) -> BigInt {
        BigInt {
            special: Some(input),
            ..Default::default()
        }
    }
}

impl Default for BigInt {
    fn default() -> BigInt {
        Self::one()
    }
}

impl Neg for BigInt {
    type Output = BigInt;

    fn neg(self) -> BigInt {
        let mut me = self;
        me.sign = -me.sign;

        me
    }
}

impl Mul for BigInt {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn mul(self, rhs: Self) -> Self::Output {
        let a = Self::convert_back(self.coefficient);
        let b = Self::convert_back(rhs.coefficient);

        Self::from_parts(a * b, self.exponent + rhs.exponent)
    }
}

impl std::fmt::Display for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let style = if let Some(style) = self.exponent_style.as_ref() {
            style
        } else {
            DEFAULT_EXPONENT_STYLE
        };

        match self {
            BigInt {
                special: Some(Special::Zero),
                ..
            } => write!(f, "0"),
            BigInt {
                special: Some(Special::Nan),
                ..
            } => write!(f, "NaN"),
            BigInt {
                special: Some(Special::Inf),
                sign: Sign::Pos,
                ..
            } => write!(f, "Infinity"),
            BigInt {
                special: Some(Special::Inf),
                sign: Sign::Neg,
                ..
            } => write!(f, "-Infinity"),
            BigInt {
                special: None,
                sign: Sign::Pos,
                exponent: 0,
                coefficient,
                ..
            } => write!(f, "{}", BigInt::convert_back(*coefficient)),
            BigInt {
                special: None,
                sign: Sign::Neg,
                exponent: 0,
                coefficient,
                ..
            } => write!(f, "-{}", BigInt::convert_back(*coefficient)),
            BigInt {
                special: None,
                sign: Sign::Pos,
                exponent,
                coefficient,
                ..
            } => write!(
                f,
                "{}{}{}",
                BigInt::convert_back(*coefficient),
                style,
                exponent
            ),
            BigInt {
                special: None,
                sign: Sign::Neg,
                exponent,
                coefficient,
                ..
            } => write!(
                f,
                "-{}{}{}",
                BigInt::convert_back(*coefficient),
                style,
                exponent
            ),
        }
    }
}

// #[test]
// fn xd() {
//     assert!(false)
// }

// 0 -> 18446744073709551615
// 1.0 -> 9.99999999999999

#[cfg(test)]
mod print {
    use crate::BigInt;

    #[test]
    fn zero() {
        assert_eq!(BigInt::zero().to_string(), "0")
    }

    #[test]
    fn one() {
        assert_eq!(BigInt::one().to_string(), "1")
    }

    #[test]
    fn three_point_four() {
        assert_eq!(BigInt::from(3.4).to_string(), "3.4")
    }

    #[test]
    #[allow(clippy::approx_constant)]
    fn negative_three_point_fourteen_fifteen() {
        assert_eq!(BigInt::from(-3.1415).to_string(), "-3.1415")
    }

    #[test]
    fn ten_point_four() {
        assert_eq!(BigInt::from(10.4).to_string(), "1.04*10^1")
    }

    #[test]
    fn zero_point_twenty_five() {
        assert_eq!(BigInt::from(0.25).to_string(), "2.5*10^-1")
    }

    #[test]
    fn zero_point_zero_zero_zero_zero_ninty_eight() {
        assert_eq!(
            BigInt::from(0.000_098).to_string(),
            "9.799999999999999*10^-5"
        )
    }

    #[test]
    fn negative_zero_point_sixty_nine() {
        assert_eq!(BigInt::from(-0.69).to_string(), "-6.899999999999999*10^-1")
    }

    #[test]
    fn ten_million_point_four() {
        assert_eq!(BigInt::from(10_000_000.4).to_string(), "1.00000004*10^7")
    }

    #[test]
    fn negative_ten_point_four() {
        assert_eq!(BigInt::from(-10.4).to_string(), "-1.04*10^1")
    }

    #[test]
    fn negative_twenty_five_point_fourty_five() {
        assert_eq!(BigInt::from(-25.45).to_string(), "-2.545*10^1")
    }

    #[test]
    fn fifteen_times_pi() {
        assert_eq!(
            BigInt::from(15.0 * std::f64::consts::PI).to_string(),
            "4.71238898038469*10^1"
        )
    }

    #[test]
    fn negative_infinity() {
        assert_eq!(BigInt::from(-f64::INFINITY).to_string(), "-Infinity")
    }

    #[test]
    fn infinity() {
        assert_eq!(BigInt::from(f64::INFINITY).to_string(), "Infinity")
    }

    #[test]
    fn nan() {
        assert_eq!(BigInt::from(f64::NAN).to_string(), "NaN")
    }
}

#[cfg(test)]
mod parse {
    use crate::{BigInt, ParseError, Sign};
    use std::convert::TryFrom;

    #[test]
    #[allow(clippy::approx_constant)]
    fn float() {
        assert_eq!(
            BigInt::try_from("3.1415".to_string()).unwrap(),
            BigInt::from(3.1415)
        )
    }

    #[test]
    fn ten() {
        assert_eq!(
            BigInt::try_from("1*10^1".to_string()).unwrap(),
            BigInt::from(10.0)
        )
    }

    #[test]
    fn eighty_five_million() {
        assert_eq!(
            BigInt::try_from("0.85*10^8".to_string()).unwrap(),
            BigInt::from(85_000_000.0)
        )
    }

    #[test]
    fn error_first_part() {
        assert_eq!(
            BigInt::try_from("test*10^8".to_string()),
            Err(ParseError::InvalidPart)
        )
    }

    #[test]
    fn error_exponent() {
        assert_eq!(
            BigInt::try_from("1.23*10^1.123".to_string()),
            Err(ParseError::NotExponent)
        )
    }

    #[test]
    fn error_format() {
        assert_eq!(
            BigInt::try_from("testing".to_string()),
            Err(ParseError::InvalidFormat)
        )
    }

    #[test]
    fn enormous_number_float() {
        assert_eq!(
            BigInt::try_from(
                "1000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000\
                00000000000000000000000000000000000000"
            ),
            Ok(BigInt::infinity())
        )
    }

    #[test]
    fn enormous_number_exponential() {
        assert_eq!(
            BigInt::try_from("1*10^123456"),
            Ok(BigInt {
                coefficient: 0,
                sign: Sign::Pos,
                exponent: 123456,
                ..Default::default()
            })
        )
    }

    #[test]
    #[allow(clippy::useless_conversion)]
    fn from_itself() {
        let expected = BigInt::try_from("123").unwrap();
        let original = BigInt::try_from("123").unwrap();
        let result = BigInt::from(original);
        assert_eq!(result, expected);
    }

    #[test]
    fn use_parse_function() {
        let x = "123.123*10^2".parse::<BigInt>().unwrap();

        assert_eq!("1.23123*10^4", x.to_string())
    }

    #[test]
    fn from_parts() {
        let big_int = BigInt::from((2.1, 5));
        let expected = BigInt::from_float(210000.0);

        assert_eq!(big_int, expected);
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod float {
    use crate::BigInt;
    use std::convert::TryFrom;

    #[test]
    fn pi() {
        let input = BigInt::from_float(std::f64::consts::PI);

        assert_eq!(std::f64::consts::PI, input.to_float())
    }

    #[test]
    fn thousand() {
        let input = BigInt::try_from("1000").unwrap();

        assert_eq!(1000.0, input.to_float())
    }

    #[test]
    fn negative_fifteen_point_five() {
        let input = BigInt::try_from("1.55*10^1").unwrap();

        assert_eq!(15.5, f64::from(input))
    }

    #[test]
    fn super_large() {
        let input = BigInt::try_from("1*10^35000").unwrap();

        assert_eq!(f64::INFINITY, input.to_float())
    }

    #[test]
    fn super_large_f32() {
        let input = BigInt::try_from("1*10^35000").unwrap();

        assert_eq!(f32::INFINITY, f32::from(input))
    }

    #[test]
    fn super_small() {
        let input = BigInt::try_from("1*10^-35000").unwrap();
        assert_eq!(0.0, f64::from(input))
    }
}

#[cfg(test)]
mod ops {
    use crate::BigInt;

    #[test]
    fn neg() {
        let expected = BigInt::one();
        let input = BigInt::from_float(-1.0);

        assert_eq!(expected, -input)
    }

    #[test]
    fn mul_pos() {
        let expected = BigInt::from_parts(2.5, 50);

        let a = BigInt::from_parts(2.0, 30);
        let b = BigInt::from_parts(1.25, 20);

        assert_eq!(expected, a * b)
    }

    #[test]
    fn mul_mixed() {
        let expected = BigInt::from_parts(1.65, -9);

        let a = BigInt::from_parts(5.5, -30);
        let b = BigInt::from_parts(3.0, 20);

        assert_eq!(expected, a * b)
    }

    #[test]
    fn multiply() {
        let expected = BigInt::from_parts(1.1055, -14);

        let a = BigInt::from_parts(5.5, -15);
        let b = 2.01;

        assert_eq!(expected, a.multiply(b))
    }

    #[test]
    fn power_difference() {
        let expected = -1;

        let a = BigInt::from_parts(7.84, -15);
        let b = BigInt::from_parts(1.96, -14);

        assert_eq!(expected, a.power_difference(b))
    }
}
