#![warn(
    clippy::all,
    clippy::nursery,
    // clippy::pedantic,
    // clippy::cargo,
    // clippy::restriction
)]
#![allow(clippy::use_self, clippy::must_use_candidate)]
#![deny(clippy::all)]

use std::convert::TryFrom;
use std::num::FpCategory;
use std::ops::{Add, Mul, Neg};

mod error;
mod r#macro;

#[cfg(feature = "rayon")]
mod rayon;
#[cfg(feature = "rayon")]
pub use crate::rayon::*;

#[cfg(not(feature = "rayon"))]
mod not_rayon;
#[cfg(not(feature = "rayon"))]
pub use not_rayon::*;

pub use error::*;

#[derive(Debug, PartialEq, Clone)]
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

#[derive(Debug, PartialEq, Clone)]
pub enum Sign {
    Pos,
    Neg,
}

impl Sign {
    pub fn apply(&self, input: f64) -> f64 {
        match self {
            Sign::Pos => input,
            Sign::Neg => -input,
        }
    }
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

#[derive(Debug, PartialEq, Clone)]
/// Struct to store large numbers
///
/// Has nearly the same data model as f64 only just bigger (u64 for precision and i128 for the exponent)
///
/// ```rust
/// use big_int::BigInt;
///
/// let number = "1.25*10^15".parse::<BigInt>();
/// let the_same_number = BigInt::from_parts(1.25, 15);
/// let the_same_number_from_integer: BigInt = 1_250_000_000_000_000u64.into();
/// let also_the_same_number: BigInt = 1.250e15.into();
///  
/// assert_eq!(the_same_number, also_the_same_number);
/// assert_eq!(number, Ok(the_same_number));
/// assert_eq!(number, Ok(the_same_number_from_integer));
/// assert_eq!(number, Ok(also_the_same_number));
/// ```
pub struct BigInt {
    // coefficient: 9.9999999999 -> 1.0
    coefficient: u64,
    sign: Sign,
    exponent: i128,
    special: Option<Special>,
    exponent_style: Option<String>,
}

const U64_STEP: f64 = 4.878_909_776_184_77e-19;
// const U64_MAX: u64 = std::u64::MAX;
const ONE_COEFFICIENT: u64 = std::u64::MAX / 9;
const DEFAULT_EXPONENT_STYLE: &str = "*10^";

impl BigInt {
    /// Creates a `BigInt` with the value 0
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("0", BigInt::zero().to_string())
    /// ```
    pub fn zero() -> BigInt {
        BigInt {
            special: Some(Special::Zero),
            ..BigInt::default()
        }
    }

    /// Creates a `BigInt` with the value 1
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("1", BigInt::one().to_string())
    /// ```
    pub const fn one() -> BigInt {
        BigInt {
            coefficient: 0,
            sign: Sign::Pos,
            exponent: 0,
            special: None,
            exponent_style: None,
        }
    }

    /// Creates a `BigInt` containing `f64::INFINITY`
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("Infinity", BigInt::infinity().to_string())
    /// ```
    pub fn infinity() -> BigInt {
        BigInt {
            special: Some(Special::Inf),
            ..BigInt::default()
        }
    }

    /// Creates a `BigInt` containing `f64::NAN`
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("NaN", BigInt::nan().to_string())
    /// ```
    pub fn nan() -> BigInt {
        BigInt {
            special: Some(Special::Nan),
            ..BigInt::default()
        }
    }

    fn convert(input: f64) -> u64 {
        ((input - 1.0) / U64_STEP) as u64
    }

    fn convert_back(input: u64) -> f64 {
        (input as f64).mul_add(U64_STEP, 1.0)
    }

    /// Creates `BigInt` from a float and exponent part
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// assert_eq!("3.14*10^20", BigInt::from_parts(3.14, 20).to_string())
    /// ```
    pub fn from_parts(coefficient: f64, exponent: i128) -> BigInt {
        let mut big_int = BigInt::from_float(coefficient);
        big_int.exponent += exponent;

        big_int
    }

    /// Creates `BigInt` from a float
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
                ..BigInt::default()
            };
        }

        if (input > -10.0) && (input <= -1.0) {
            let coefficient = Self::convert(-input);

            return BigInt {
                coefficient,
                sign: Sign::Neg,
                ..BigInt::default()
            };
        }

        if (input >= 10.0) || (input < -10.0) {
            // never happens f64::MAX.log10() == 308.25
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
                exponent: exponent as i128,
                ..BigInt::default()
            };
        }

        if input.abs() < 1.0 {
            let exponent = input.abs().log10().floor() as i32;
            let remainder = input / (10_f64.powi(exponent));

            return Self::from_parts(remainder, exponent as i128);
        }

        unreachable!()
    }

    /// Creates `BigInt` from an integer
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// let expected = BigInt::parse("8.3*10^4").expect("invalid format");
    /// assert_eq!(expected, BigInt::from_integer(83000));
    /// ```
    pub fn from_integer(input: i128) -> Self {
        if input == 0 {
            return BigInt::zero();
        };

        let exponent = (input.abs() as f64).log10().floor() as i32;
        let coefficient = (input as f64) / 10_f64.powi(exponent);

        BigInt::from_parts(coefficient, exponent as i128)
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
    /// assert_eq!(0.0, BigInt::from_parts(4.3, -123465789).to_float());
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
        let power = if self.exponent > (i32::MAX as i128) {
            f64::INFINITY
        } else if (i32::MIN as i128) > self.exponent {
            0.0
        } else {
            10_f64.powi(self.exponent as i32)
        };

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
    pub fn to_parts(&self) -> (f64, i128) {
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
    pub fn parse(input: &str) -> Result<BigInt> {
        if let Ok(x) = input.parse::<i128>() {
            return Ok(Self::from_integer(x));
        };

        if let Ok(x) = input.parse::<f64>() {
            return Ok(Self::from_float(x));
        };

        let parts: Vec<_> = input.split(DEFAULT_EXPONENT_STYLE).collect();
        if parts.len() != 2 {
            return Err(ParseError::InvalidFormat.into());
        }

        let first = match parts[0].parse::<f64>() {
            Ok(x) => x,
            Err(_) => return Err(ParseError::InvalidPart.into()),
        };

        let second = match parts[1].parse::<i128>() {
            Ok(x) => x,
            Err(_) => return Err(ParseError::NotExponent.into()),
        };

        Ok(Self::from_parts(first, second))
    }

    // operations

    /// The same as the `mul` function only can take a `Into<BigInt>` as its argument
    pub fn multiply<RHS: Into<BigInt>>(self, rhs: RHS) -> BigInt {
        let other: BigInt = rhs.into();
        self * other
    }

    // pub fn pow(self, power: i32) -> BigInt {
    //     let (change_sign, exponent) = if power == 0 {
    //         (10, self.exponent * power)
    //     } else if power % 2 == 0 {
    //         (2, self.exponent * power)
    //     } else {
    //         (1, self.exponent * power)
    //     };

    //     let mut big_int = BigInt::from_float(Self::convert_back(self.coefficient).powi(power));

    //     match change_sign {
    //         10 => big_int = BigInt::one(),
    //         2 => big_int.sign = Sign::Pos,
    //         1 => big_int.sign = self.sign,
    //         _ => unreachable!(),
    //     };

    //     big_int.exponent += exponent;
    //     big_int
    // }

    /// Calculates the difference between the exponents
    ///
    /// This operation is fast because it is just a subtraction of two i32s
    pub fn power_difference<RHS: Into<BigInt>>(&self, rhs: RHS) -> i128 {
        self.exponent - rhs.into().exponent
    }

    /// Compares if two `BigInt` are nearly equal
    ///
    /// This because sometimes you create `BigInt` from a f64 and these have less precision than `BigInt`
    pub fn near_equal(&self, other: &BigInt) -> bool {
        const SMALL_NUMBER: u64 = 550;

        (self.exponent == other.exponent)
            && (self.sign == other.sign)
            && (Self::abs_difference(self.coefficient, other.coefficient) < SMALL_NUMBER)
    }

    const fn abs_difference(x: u64, y: u64) -> u64 {
        if x < y {
            y - x
        } else {
            x - y
        }
    }

    /// Calculates factorial of n
    ///
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// let calculated = BigInt::factorial(60);
    /// let actual_float = 8_320_987_112_741_390_144_276_341_183_223_364_380_754_172_606_361_245_952_449_277_696_409_600_000_000_000_000_f64;
    /// let calculated_float = calculated.to_float();
    /// let max = actual_float.max(calculated_float);
    /// let difference = ((actual_float - calculated_float) / max).abs();
    ///
    /// assert!(difference < 10e-15);
    /// ```
    pub fn factorial(n: u64) -> BigInt {
        if (n == 0) || (n == 1) {
            BigInt::one()
        } else if n == 2 {
            BigInt::from(2)
        } else {
            (2..n).fold(BigInt::from(n), |acc, x| acc * BigInt::from(x))
        }
    }

    /// Calculates self to the hyperpower of `n`
    ///
    /// Also called tetration. Side note: use very small numbers because most numbers don't even fit in `BigInt`.
    /// ```rust
    /// use big_int::BigInt;
    ///
    /// let result = BigInt::from(2).hyper_exponential(4);
    /// assert_eq!(Ok(BigInt::from(65536)), result);
    /// ```
    pub fn hyper_exponential(self, n: u8) -> Result<BigInt> {
        if n == 0 || n == 1 {
            return Ok(BigInt::one());
        };

        let mut power;
        let base = self.clone();
        let mut big_int = self;
        for _ in 0..n - 1 {
            power = big_int.fits_in_i32()?;
            big_int = base.clone().pow(power as i128)
        }

        Ok(big_int)
    }

    fn fits_in_i32(&self) -> Result<i32> {
        if self.to_float() > (i32::MAX as f64) {
            Err(OperatorError::ExponentTooLarge.into())
        } else {
            Ok(self.to_float() as i32)
        }
    }

    // arrow function ?
}

impl_int!(i128);
impl_int!(i64);
impl_int!(i32);
impl_int!(i16);
impl_int!(i8);
impl_int!(u64);
impl_int!(u32);
impl_int!(u16);
impl_int!(u8);

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

impl From<(f64, i128)> for BigInt {
    fn from(input: (f64, i128)) -> BigInt {
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
    type Error = Error;

    fn try_from(input: String) -> Result<Self> {
        Self::try_from(input.as_str())
    }
}

impl std::convert::TryFrom<&str> for BigInt {
    type Error = Error;

    fn try_from(input: &str) -> Result<Self> {
        BigInt::parse(input)
    }
}

impl std::str::FromStr for BigInt {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        BigInt::parse(s)
    }
}

impl From<Special> for BigInt {
    fn from(input: Special) -> BigInt {
        BigInt {
            special: Some(input),
            ..BigInt::default()
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

impl Add for BigInt {
    type Output = BigInt;

    // #[allow(clippy::suspicious_arithmetic_impl)]
    // fn add(self, other: Self) -> BigInt {
    //     let power_diff = self.exponent - other.exponent;

    //     let self_float = Self::convert_back(self.coefficient);
    //     let other_float = Self::convert_back(other.coefficient);

    //     use std::cmp::Ordering::*;
    //     let xd = match power_diff.cmp(&0) {
    //         Equal => BigInt::from_parts(self_float + other_float, self.exponent),
    //         Less => {
    //             let new_float = if power_diff <= i32::MIN as i128 {
    //                 0.0
    //             } else {
    //                 self_float * 10f64.powi(power_diff as i32)
    //             };
    //             BigInt::from_parts(other_float + new_float, other.exponent)
    //         }
    //         Greater => {
    //             let new_float = if power_diff >= i32::MAX as i128 {
    //                 0.0
    //             } else {
    //                 other_float * 10f64.powi(-power_diff as i32)
    //             };
    //             BigInt::from_parts(self_float + new_float, self.exponent)
    //         }
    //     };
    //     println!("{}", xd);

    //     xd
    // }

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, other: Self) -> BigInt {
        let power_diff = match self.exponent.checked_sub(other.exponent) {
            Some(x) => x,
            None => {
                if self.exponent > other.exponent {
                    return self;
                } else {
                    return other;
                }
            }
        };

        use std::cmp::Ordering::*;
        match power_diff.cmp(&0) {
            Equal => cheese(self.coefficient, other.coefficient, self.exponent),
            Greater => {
                if let Ok(power) = u32::try_from(power_diff) {
                    diff_cheese(self.coefficient, other.coefficient, self.exponent, power)
                } else {
                    self
                }
            }
            Less => {
                if let Ok(power) = u32::try_from(-power_diff) {
                    diff_cheese(other.coefficient, self.coefficient, other.exponent, power)
                } else {
                    other
                }
            }
        }
    }
}

// fn blub(a: u64, b: u64) -> std::result::Result<u64, u8> {
//     println!("{} {}", a, b);
//     if let Some(x) = a.checked_add(ONE_COEFFICIENT) {
//         if let Some(y) = x.checked_add(b) {
//             return Ok(y);
//         } else {
//             return Err(1);
//         };
//     };

//     if let Some(x) = b.checked_add(ONE_COEFFICIENT) {
//         if let Some(y) = x.checked_add(a) {
//             return Ok(y);
//         } else {
//             return Err(1);
//         };
//     };

//     if let Some(x) = a.checked_add(b) {
//         if let Some(y) = x.checked_add(ONE_COEFFICIENT) {
//             return Ok(y);
//         } else {
//             return Err(0);
//         };
//     };

//     panic!("underflow again")
// }

fn cheese(left: u64, right: u64, exponent: i128) -> BigInt {
    match blub(left, right) {
        (x, true) => BigInt {
            coefficient: x,
            exponent: exponent + 1,
            ..BigInt::default()
        },
        (x, false) => BigInt {
            coefficient: x,
            exponent,
            ..BigInt::default()
        },
    }
}

fn diff_cheese(left: u64, right: u64, exponent: i128, diff: u32) -> BigInt {
    match blub_diff(left, right, diff) {
        (x, true) => BigInt {
            coefficient: x,
            exponent: exponent + 1,
            ..BigInt::default()
        },
        (x, false) => BigInt {
            coefficient: x,
            exponent,
            ..BigInt::default()
        },
    }
}

const fn blub(a: u64, b: u64) -> (u64, bool) {
    match a.overflowing_add(ONE_COEFFICIENT) {
        (x, true) => (x + b, true),
        (x, false) => match x.overflowing_add(b) {
            (y, true) => (y / 10, true),
            (y, false) => (y, false),
        },
    }
}

#[allow(clippy::missing_const_for_fn)]
fn blub_diff(a: u64, b: u64, diff: u32) -> (u64, bool) {
    if let Some(pw) = 10u64.checked_pow(diff) {
        let (x, y) = blub(a, b / pw);
        (x - ONE_COEFFICIENT + ONE_COEFFICIENT / pw, y)
    } else {
        (a, false)
    }
}

impl Mul for BigInt {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn mul(self, rhs: Self) -> Self::Output {
        let a = self.sign.apply(Self::convert_back(self.coefficient));
        let b = rhs.sign.apply(Self::convert_back(rhs.coefficient));

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
mod helpers {
    use crate::BigInt;
    pub fn assert_near_equal(a: BigInt, b: BigInt) {
        if !a.near_equal(&b) {
            assert_eq!(a, b)
        }
    }
}

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
            Err(ParseError::InvalidPart.into())
        )
    }

    #[test]
    fn error_exponent() {
        assert_eq!(
            BigInt::try_from("1.23*10^1.123".to_string()),
            Err(ParseError::NotExponent.into())
        )
    }

    #[test]
    fn error_format() {
        assert_eq!(
            BigInt::try_from("testing".to_string()),
            Err(ParseError::InvalidFormat.into())
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
                exponent: 123_456,
                ..BigInt::default()
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
        let expected = BigInt::from(210_000);

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
mod integer {
    use crate::BigInt;

    #[test]
    fn two_hundered_thirty() {
        assert_eq!(BigInt::from_parts(2.3, 2), BigInt::from_integer(230))
    }

    #[test]
    fn negative_four_thousand_fourty() {
        assert_eq!(BigInt::from_parts(-4.04, 3), BigInt::from_integer(-4040))
    }

    #[test]
    fn zero() {
        assert_eq!(BigInt::zero(), BigInt::from_integer(0))
    }

    #[test]
    fn negative_zero() {
        assert_eq!(BigInt::zero(), BigInt::from_integer(-0))
    }

    #[test]
    fn from() {
        assert_eq!(BigInt::from_parts(1.23542, 5), BigInt::from(123_542))
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

    #[test]
    fn square() {
        let result = BigInt::from(3600);
        let expected = BigInt::from_parts(1.296, 7);

        assert_eq!(expected, result.pow(2))
    }

    #[test]
    fn cube() {
        let result = BigInt::from(-36).pow(3);
        let expected = BigInt::from_parts(-4.6656, 4);

        assert_eq!(expected, result)
    }
}

#[cfg(test)]
mod add {
    use crate::helpers::assert_near_equal;
    use crate::BigInt;

    #[test]
    fn one_plus_one() {
        let result = BigInt::one() + BigInt::one();
        assert_near_equal(BigInt::from(2), result);
    }

    #[test]
    fn one_point_two_plus_one_point_three() {
        let result = BigInt::from(1.2) + BigInt::from(1.3);
        assert_near_equal(BigInt::from(2.5), result);
    }

    #[test]
    fn three_plus_two() {
        let result = BigInt::from(3) + BigInt::from(2);
        assert_near_equal(BigInt::from(5), result);
    }

    #[test]
    fn three_plus_eight() {
        let result = BigInt::from(3) + BigInt::from(8);
        assert_near_equal(BigInt::from(11), result)
    }

    #[test]
    fn seven_plus_nine() {
        let result = BigInt::from(7) + BigInt::from(9);
        assert_near_equal(BigInt::from(16), result);
    }

    #[test]
    fn half_plus_six_point_8() {
        let result = BigInt::from(0.5) + BigInt::from(6.8);
        assert_near_equal(BigInt::from(7.3), result);
    }

    #[test]
    fn very_large_plus_normal() {
        let result = BigInt::from_parts(5.0, 123456) + BigInt::from(6.8);
        assert_near_equal(BigInt::from_parts(5.0, 123456), result);
    }

    #[test]
    fn very_small_plus_normal() {
        let result = BigInt::from_parts(5.0, -123456) + BigInt::from(6.8);
        assert_near_equal(BigInt::from(6.8), result);
    }

    #[test]
    fn very_small_plus_very_large() {
        let result = BigInt::from_parts(5.0, -123456) + BigInt::from_parts(5.0, 123456789111213);
        assert_near_equal(BigInt::from_parts(5.0, 123456789111213), result);
    }

    #[test]
    fn large_plus_small() {
        let result = BigInt::from_parts(5.0, 3) + BigInt::from_parts(5.0, -3);
        assert_near_equal(BigInt::from_parts(5.000005, 3), result);
    }

    #[test]
    fn small_plus_large() {
        let result = BigInt::from_parts(5.0, -3) + BigInt::from_parts(5.0, 3);
        assert_near_equal(BigInt::from_parts(5.000005, 3), result);
    }

    #[test]
    fn extremes_one() {
        let result = BigInt::from_parts(5.0, i128::MIN) + BigInt::from_parts(5.0, i128::MAX);
        assert_near_equal(BigInt::from_parts(5.0, i128::MAX), result);
    }

    #[test]
    fn extremes_two() {
        let result = BigInt::from_parts(8.0, i128::MAX) + BigInt::from_parts(3.0, i128::MIN);
        assert_near_equal(BigInt::from_parts(8.0, i128::MAX), result);
    }
}

#[cfg(test)]
mod factorial {
    use crate::BigInt;

    fn compare(n: u64, actual: f64) -> bool {
        let calculated = BigInt::factorial(n);

        let actual_float = actual;
        let calculated_float = calculated.to_float();

        let max = actual_float.max(calculated_float);
        let difference = ((actual_float - calculated_float) / max).abs();
        difference < 10e-15
    }

    #[test]
    fn small_error_30() {
        assert!(compare(30, 265_252_859_812_191_058_636_308_480_000_000_f64))
    }

    #[test]
    fn small_error_35() {
        assert!(compare(
            35,
            10_333_147_966_386_144_929_666_651_337_523_200_000_000_f64
        ))
    }

    #[test]
    fn small_error_40() {
        assert!(compare(
            40,
            815_915_283_247_897_734_345_611_269_596_115_894_272_000_000_000_f64
        ))
    }

    #[test]
    fn small_error_45() {
        assert!(compare(
            45,
            119_622_220_865_480_194_561_963_161_495_657_715_064_383_733_760_000_000_000_f64
        ))
    }

    #[test]
    fn small_error_60() {
        assert!(compare(
            60,
            8_320_987_112_741_390_144_276_341_183_223_364_380_754_172_606_361_245_952_449_277_696_409_600_000_000_000_000_f64
        ))
    }

    #[test]
    fn small_error_100() {
        assert!(compare(
            100,
            93_326_215_443_944_152_681_699_238_856_266_700_490_715_968_264_381_621_468_592_963_895_217_599_993_229_915_608_941_463_976_156_518_286_253_697_920_827_223_758_251_185_210_916_864_000_000_000_000_000_000_000_000_f64
        ))
    }
}

#[cfg(test)]
mod hyper_exponential {
    use crate::{BigInt, OperatorError};

    #[test]
    fn zero_two() {
        let result = BigInt::from(2).hyper_exponential(0);
        assert_eq!(Ok(BigInt::one()), result);
    }

    #[test]
    fn one_two() {
        let result = BigInt::from(2).hyper_exponential(1);
        assert_eq!(Ok(BigInt::one()), result);
    }

    #[test]
    fn two_two() {
        let result = BigInt::from(2).hyper_exponential(2);
        assert_eq!(Ok(BigInt::from(4)), result);
    }
    #[test]
    fn three_two() {
        let result = BigInt::from(2).hyper_exponential(3);
        assert_eq!(Ok(BigInt::from(16)), result);
    }

    #[test]
    fn four_two() {
        let result = BigInt::from(2).hyper_exponential(4);
        assert_eq!(Ok(BigInt::from(65536)), result);
    }

    #[test]
    fn five_two() {
        let result = BigInt::from(2).hyper_exponential(5);
        assert_eq!(Ok(BigInt::from_parts(1.0017649652034222, 19728)), result);
    }

    #[test]
    fn six_two_is_too_much() {
        let result = BigInt::from(2).hyper_exponential(6);
        assert_eq!(Err(OperatorError::ExponentTooLarge.into()), result);
    }

    #[test]
    fn two_three() {
        let result = BigInt::from(3).hyper_exponential(2);
        assert_eq!(Ok(BigInt::from_integer(27)), result);
    }

    #[test]
    fn three_three() {
        let result = BigInt::from(3).hyper_exponential(3);
        assert_eq!(Ok(BigInt::from_parts(7.625597484987001, 12)), result);
    }

    #[test]
    fn four_three_is_too_much() {
        let result = BigInt::from(3).hyper_exponential(4);
        assert_eq!(Err(OperatorError::ExponentTooLarge.into()), result);
    }
}

// #[test]
// fn xd() {
//     println!("{:?}", i32::MIN.checked_sub(i32::MAX));

//     assert!(false);
// }
