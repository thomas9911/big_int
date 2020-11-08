use crate::{BigInt, Result};
use rayon::prelude::*;

impl BigInt {
    /// Calculates self to the power of `power`
    pub fn pow(self, power: i128) -> BigInt {
        if power > i32::MAX as i128 {
            panic!("this will take too long:, {}", power)
        };

        if power == 0 {
            return BigInt::one();
        }

        if power == 1 {
            return self;
        }

        (0..power)
            .into_par_iter()
            .fold(BigInt::one, |acc, _x| acc * self.clone())
            .reduce(BigInt::one, |a, b| a * b)
    }
}

// #[test]
// fn xdxd() {
//     // let result = BigInt::from(2).pow(4);
//     let result = BigInt::from(7).pow(5);

//     println!("res: {}", result);
//     assert!(false);
// }
