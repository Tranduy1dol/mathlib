use crate::big_int::U1024;
use crate::traits::BigInt;

#[derive(Clone, Debug)]
pub struct MontgomeryParams {
    pub modulus: U1024,
    pub r2: U1024,
    pub k0: u64,
}

impl MontgomeryParams {
    pub fn new(modulus: U1024) -> Self {
        let k0 = Self::compute_k0(&modulus);
        let r2 = Self::compute_r2(&modulus);

        Self { modulus, r2, k0 }
    }

    fn compute_k0(modulus: &U1024) -> u64 {
        let p0 = modulus.0[0];
        let mut inv = 1u64;

        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
        }

        inv.wrapping_neg()
    }

    fn compute_r2(modulus: &U1024) -> U1024 {
        // TODO: Implement compute_r2 properly
        U1024::zero()
    }
}
