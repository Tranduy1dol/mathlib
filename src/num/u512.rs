#[repr(align(32))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct U512(pub [u64; 8]);

impl U512 {
    pub const ZERO: Self = Self([0; 8]);
}
