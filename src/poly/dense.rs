use std::fmt;
use std::ops::{Add, Mul};

use crate::FieldElement;

#[derive(Clone)]
pub struct DensePolynomial<'a> {
    pub coeffs: Vec<FieldElement<'a>>,
}

impl<'a> DensePolynomial<'a> {
    pub fn new(coeffs: Vec<FieldElement<'a>>) -> Self {
        let mut poly = Self { coeffs };
        poly.trim();
        poly
    }

    fn trim(&mut self) {
        while let Some(c) = self.coeffs.last() {
            if c.to_u1024().0.iter().all(|&x| x == 0) {
                self.coeffs.pop();
            } else {
                break;
            }
        }
    }

    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    pub fn evaluate(&self, x: &FieldElement<'a>) -> FieldElement<'a> {
        if self.coeffs.is_empty() {
            return FieldElement::zero(x.params);
        }

        let mut res = self.coeffs.last().unwrap().clone();
        for i in (0..self.coeffs.len() - 1).rev() {
            res = (res * x.clone()) + self.coeffs[i].clone();
        }
        res
    }
}

impl<'a> Add for DensePolynomial<'a> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        if self.coeffs.is_empty() {
            return rhs;
        }
        if rhs.coeffs.is_empty() {
            return self;
        }

        let max_len = std::cmp::max(self.coeffs.len(), rhs.coeffs.len());
        let mut new_coeffs = Vec::with_capacity(max_len);
        let params = self.coeffs[0].params;
        let zero = FieldElement::zero(params);

        for i in 0..max_len {
            let a = self.coeffs.get(i).unwrap_or(&zero);
            let b = rhs.coeffs.get(i).unwrap_or(&zero);
            new_coeffs.push(a.clone() + b.clone());
        }

        Self::new(new_coeffs)
    }
}

impl<'a> Mul for DensePolynomial<'a> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        if self.coeffs.is_empty() || rhs.coeffs.is_empty() {
            return Self::zero();
        }

        let len = self.coeffs.len() + rhs.coeffs.len() - 1;
        let params = self.coeffs[0].params;
        let zero = FieldElement::zero(params);

        let mut res = vec![zero; len];

        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in rhs.coeffs.iter().enumerate() {
                let product = a.clone() * b.clone();
                res[i + j] = res[i + j].clone() + product;
            }
        }

        Self::new(res)
    }
}

impl<'a> fmt::Debug for DensePolynomial<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Poly{:?}", self.coeffs)
    }
}
