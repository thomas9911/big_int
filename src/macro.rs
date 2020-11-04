#[macro_export]
macro_rules! impl_int {
    ($ty:ty) => {
        impl From<$ty> for BigInt {
            fn from(input: $ty) -> BigInt {
                Self::from_integer(input as i128)
            }
        }
    };
}
