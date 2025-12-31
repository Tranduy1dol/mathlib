use std::fmt::{Debug, Display};
use std::ops::{Add, BitXor, Mul, Sub};

/// Trait for big integer types used in cryptographic operations.
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

/// Trait for types that can be created from a cryptographic hash.
///
/// This trait allows deriving cryptographic values (like field elements
/// or big integers) from arbitrary byte data using SHA256-based hashing.
///
/// # Examples
///
/// ```
/// use lumen_math::{U1024, Digest};
///
/// let hash = U1024::from_hash(b"hello world");
/// let hash2 = U1024::from_hash(b"hello world");
/// assert_eq!(hash, hash2); // Deterministic
///
/// let hash3 = U1024::from_hash(b"different");
/// assert_ne!(hash, hash3);
/// ```
pub trait Digest: Sized {
    /// Creates a value by hashing the input bytes using SHA256.
    ///
    /// Uses expand_message_xmd to generate sufficient entropy for the type.
    fn from_hash(input: &[u8]) -> Self;

    /// Creates a value by hashing with domain separation.
    ///
    /// Domain separation ensures that hashes for different purposes don't
    /// collide, even with the same input data.
    fn from_hash_with_domain(domain: &[u8], input: &[u8]) -> Self;
}
