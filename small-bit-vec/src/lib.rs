mod small_bit_vec;
mod bmi2;

use core::hint::unreachable_unchecked;
pub use self::small_bit_vec::{SmallBitVec, Iter, IntoIter};

#[cfg(test)]
mod test;

/// Takes the bitwise `or` of two 32-bit values whose 1 bits do not overlap.
/// 
/// For such values, `|` and `+` are equivalent, and the compiler may use this to its advantage.
///
/// Rust stdlib tracking issue: https://github.com/rust-lang/rust/issues/135758
///
/// # Safety
///
/// If any bits are set in both `a` and `b`, the result is undefined behavior.
unsafe fn unchecked_disjoint_bitor(a: usize, b: usize) -> usize {
    if a & b != 0 {
        // SAFETY:
        unsafe { unreachable_unchecked() }
    }
    a | b
}
