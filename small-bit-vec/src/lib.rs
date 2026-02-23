#![feature(disjoint_bitor)]

mod small_bit_vec;
mod bmi2;

pub use self::small_bit_vec::{SmallBitVec, Iter, IntoIter};

#[cfg(test)]
mod test;

