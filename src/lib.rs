#![deny(clippy::all)]
// #![deny(clippy::pedantic)]
#![allow(clippy::approx_constant)]

use std::convert::TryFrom;
use std::num::FpCategory;
use std::ops::Neg;

#[derive(Debug, PartialEq)]
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
pub struct BigInt {
    /// coefficient: 9.9999999999 -> 1.0
    coefficient: u64,
    sign: Sign,
    exponent: i32,
    special: Option<Special>,
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

impl BigInt {
    pub fn zero() -> Self {
        BigInt {
            coefficient: 0,
            sign: Sign::Pos,
            exponent: 0,
            special: Some(Special::Zero),
        }
    }

    pub fn one() -> Self {
        BigInt {
            coefficient: 0,
            sign: Sign::Pos,
            exponent: 0,
            special: None,
        }
    }

    pub fn infinity() -> Self {
        BigInt {
            coefficient: 0,
            sign: Sign::Pos,
            exponent: 0,
            special: Some(Special::Inf),
        }
    }

    pub fn nan() -> Self {
        BigInt {
            coefficient: 0,
            sign: Sign::Pos,
            exponent: 0,
            special: Some(Special::Nan),
        }
    }

    fn convert(input: f64) -> u64 {
        ((input - 1.0) / U64_STEP) as u64
    }

    fn convert_back(input: u64) -> f64 {
        (input as f64 * U64_STEP) + 1.0
    }

    pub fn from_float(input: f64) -> Self {
        match input.classify() {
            FpCategory::Infinite => {
                let sign = if input.is_sign_positive() {
                    Sign::Pos
                } else {
                    Sign::Neg
                };

                return BigInt {
                    coefficient: 0,
                    sign,
                    exponent: 0,
                    special: Some(Special::Inf),
                };
            }

            FpCategory::Nan => {
                return BigInt {
                    coefficient: 0,
                    sign: Sign::Pos,
                    exponent: 0,
                    special: Some(Special::Nan),
                }
            }

            FpCategory::Zero => return BigInt::zero(),

            _ => (),
        };

        if (input < 10.0) && (input >= 1.0) {
            let coefficient = Self::convert(input);
            return BigInt {
                coefficient,
                sign: Sign::Pos,
                exponent: 0,
                special: None,
            };
        }

        if (input > -10.0) && (input <= -1.0) {
            let coefficient = Self::convert(-input);

            return BigInt {
                coefficient,
                sign: Sign::Neg,
                exponent: 0,
                special: None,
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
                special: None,
            };
        }

        if input.abs() < 1.0 {
            let exponent = input.abs().log10().floor() as i32;
            let remainder = input / (10_f64.powi(exponent));
            let mut big_int = Self::from_float(remainder);

            big_int.exponent = exponent;

            return big_int;
        }

        unreachable!()
    }

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
}

impl From<f64> for BigInt {
    fn from(input: f64) -> Self {
        Self::from_float(input)
    }
}

impl From<f32> for BigInt {
    fn from(input: f32) -> Self {
        Self::from_float(f64::from(input))
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
        if let Ok(x) = input.parse::<f64>() {
            return Ok(Self::from_float(x));
        };

        let parts: Vec<_> = input.split("*10^").collect();
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

        let mut big_int = Self::from_float(first);

        big_int.exponent += second;

        Ok(big_int)
    }
}

impl From<Special> for BigInt {
    fn from(input: Special) -> Self {
        BigInt {
            coefficient: 0,
            sign: Sign::Pos,
            exponent: 0,
            special: Some(input),
        }
    }
}

impl Neg for BigInt {
    type Output = BigInt;

    fn neg(self) -> Self {
        let mut me = self;
        me.sign = -me.sign;

        me
    }
}

impl std::fmt::Display for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
                ..
            } => write!(f, "{}", BigInt::convert_back(self.coefficient)),
            BigInt {
                special: None,
                sign: Sign::Neg,
                exponent: 0,
                ..
            } => write!(f, "-{}", BigInt::convert_back(self.coefficient)),
            BigInt {
                special: None,
                sign: Sign::Pos,
                exponent,
                ..
            } => write!(
                f,
                "{}*10^{}",
                BigInt::convert_back(self.coefficient),
                exponent
            ),
            BigInt {
                special: None,
                sign: Sign::Neg,
                exponent,
                ..
            } => write!(
                f,
                "-{}*10^{}",
                BigInt::convert_back(self.coefficient),
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
    use super::BigInt;

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
    use super::{BigInt, ParseError, Sign};
    use std::convert::TryFrom;

    #[test]
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
                special: None
            })
        )
    }
}

#[cfg(test)]
mod float {
    use super::BigInt;
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
}

#[cfg(test)]
mod ops {
    use super::BigInt;

    #[test]
    fn neg() {
        let expected = BigInt::one();
        let input = BigInt::from_float(-1.0);

        assert_eq!(expected, -input)
    }
}
