use std::fmt::{Debug, Display};
use std::ops::{Add, BitXor, Mul, Sub};

pub trait BigInt:
    Sized
    + Copy
    + Clone
    + Debug
    + Display
    + Default
    + PartialEq
    + Eq
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + BitXor<Output = Self>
{
    const NUM_LIMBS: usize;

    fn zero() -> Self;

    fn one() -> Self;

    fn carrying_add(&self, rhs: &Self) -> (Self, bool);

    fn borrowing_sub(&self, rhs: &Self) -> (Self, bool);
    fn conditional_select(a: &Self, b: &Self, choice: bool) -> Self;
}
