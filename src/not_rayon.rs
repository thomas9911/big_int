use crate::BigInt;

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

        (1..power).fold(self.clone(), |acc, _x| acc * self.clone())
    }
}
