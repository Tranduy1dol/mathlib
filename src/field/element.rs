use std::fmt;
use std::ops::{Add, Mul, Sub};

use crate::U1024;
use crate::field::montgomery::MontgomeryParams;
use crate::traits::BigInt;

#[derive(Clone)]
pub struct FieldElement<'a> {
    pub value: U1024,
    pub params: &'a MontgomeryParams,
}

impl<'a> FieldElement<'a> {
    pub fn new(value: U1024, params: &'a MontgomeryParams) -> Self {
        let (lo, hi) = value.full_mul(&params.r2);
        let mont_value = params.reduce(&lo, &hi);

        Self {
            value: mont_value,
            params,
        }
    }

    pub fn from_montgomery(value: U1024, params: &'a MontgomeryParams) -> Self {
        Self { value, params }
    }

    pub fn zero(params: &'a MontgomeryParams) -> Self {
        Self {
            value: U1024::zero(),
            params,
        }
    }

    pub fn one(params: &'a MontgomeryParams) -> Self {
        Self::new(U1024::one(), params)
    }

    pub fn to_u1024(&self) -> U1024 {
        self.params.reduce(&self.value, &U1024::zero())
    }
}

impl<'a> Add for FieldElement<'a> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (sum, carry) = self.value.carrying_add(&rhs.value);

        let (sub_res, borrow) = sum.borrowing_sub(&self.params.modulus);
        let use_sub = carry || !borrow;

        Self {
            value: U1024::conditional_select(&sub_res, &sum, use_sub),
            params: self.params,
        }
    }
}

impl<'a> Sub for FieldElement<'a> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let (diff, borrow) = self.value.borrowing_sub(&rhs.value);

        let (corr, _) = diff.carrying_add(&self.params.modulus);
        Self {
            value: U1024::conditional_select(&corr, &diff, borrow),
            params: self.params,
        }
    }
}

impl<'a> Mul for FieldElement<'a> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let (lo, hi) = self.value.full_mul(&rhs.value);

        let res = self.params.reduce(&lo, &hi);

        Self {
            value: res,
            params: self.params,
        }
    }
}

impl<'a> fmt::Debug for FieldElement<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let raw = self.to_u1024();
        write!(f, "FieldElement({:?})", raw)
    }
}

impl<'a> PartialEq for FieldElement<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl<'a> Eq for FieldElement<'a> {}
