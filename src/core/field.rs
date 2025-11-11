use std::ops::{Add, Mul, Sub};

pub trait Field:
    Sized
    + Copy
    + Clone
    + Send
    + Sync
    + PartialEq
    + Eq
    + std::fmt::Debug
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
{
}
