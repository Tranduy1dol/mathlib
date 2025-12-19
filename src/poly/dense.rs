use std::fmt;
use std::ops::{Add, Mul};

use crate::{FieldConfig, FieldElement, intt, ntt};

#[derive(Clone)]
pub struct DensePolynomial<C: FieldConfig> {
    pub coeffs: Vec<FieldElement<C>>,
}

impl<C: FieldConfig> DensePolynomial<C> {
    /// Constructs a DensePolynomial from the given coefficient vector, removing any trailing coefficients that are the field zero.
    pub fn new(coeffs: Vec<FieldElement<C>>) -> Self {
        let mut poly = Self { coeffs };
        poly.trim();
        poly
    }

    /// Remove trailing zero coefficients from the polynomial's coefficient vector.
    fn trim(&mut self) {
        while let Some(c) = self.coeffs.last() {
            if c.to_u1024().0.iter().all(|&x| x == 0) {
                self.coeffs.pop();
            } else {
                break;
            }
        }
    }

    /// Create an empty polynomial representing the zero polynomial.
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Evaluate the polynomial at the given point.
    pub fn evaluate(&self, x: &FieldElement<C>) -> FieldElement<C> {
        if self.coeffs.is_empty() {
            return FieldElement::zero();
        }

        let mut res = *self.coeffs.last().unwrap();
        for i in (0..self.coeffs.len() - 1).rev() {
            res = (res * *x) + self.coeffs[i];
        }
        res
    }

    /// Multiplies two polynomials using the Number Theoretic Transform (NTT).
    pub fn mul_fast(&self, rhs: &Self) -> Self {
        if self.coeffs.is_empty() || rhs.coeffs.is_empty() {
            return Self::zero();
        }

        let output_len = self.coeffs.len() + rhs.coeffs.len() - 1;
        let size = output_len.next_power_of_two();

        let zero = FieldElement::zero();

        let mut a_coeffs = self.coeffs.clone();
        a_coeffs.resize(size, zero);

        let mut b_coeffs = rhs.coeffs.clone();
        b_coeffs.resize(size, zero);

        ntt(&mut a_coeffs);
        ntt(&mut b_coeffs);

        for i in 0..size {
            a_coeffs[i] = a_coeffs[i] * b_coeffs[i];
        }

        intt(&mut a_coeffs);

        a_coeffs.truncate(output_len);

        let mut res = Self::new(a_coeffs);
        res.trim();
        res
    }
}

impl<C: FieldConfig> Add for DensePolynomial<C> {
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
        let zero = FieldElement::zero();

        for i in 0..max_len {
            let a = self.coeffs.get(i).unwrap_or(&zero);
            let b = rhs.coeffs.get(i).unwrap_or(&zero);
            new_coeffs.push(*a + *b);
        }

        Self::new(new_coeffs)
    }
}

impl<C: FieldConfig> Mul for DensePolynomial<C> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        if self.coeffs.is_empty() || rhs.coeffs.is_empty() {
            return Self::zero();
        }

        let len = self.coeffs.len() + rhs.coeffs.len() - 1;
        let zero = FieldElement::zero();

        let mut res = vec![zero; len];

        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in rhs.coeffs.iter().enumerate() {
                let product = *a * *b;
                res[i + j] = res[i + j] + product;
            }
        }

        Self::new(res)
    }
}

impl<C: FieldConfig> fmt::Debug for DensePolynomial<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Poly({})", self)
    }
}

impl<C: FieldConfig> fmt::Display for DensePolynomial<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.coeffs.is_empty() {
            return write!(f, "0");
        }

        let mut first = true;
        let one = crate::U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

        for (i, coeff) in self.coeffs.iter().enumerate().rev() {
            // Skip zero coefficients
            if coeff.is_zero() {
                continue;
            }

            // Get the full 1024-bit coefficient value
            let coeff_u1024 = coeff.to_u1024();

            // Check if coefficient is exactly 1 (compare full 1024-bit representation)
            let is_one = coeff_u1024.0 == one.0;

            // Format coefficient: use compact decimal if small (fits in u64), otherwise hex
            let coeff_str = if coeff_u1024.0[1..].iter().all(|&x| x == 0) {
                // Fits in the first limb (≤64 bits), use decimal
                format!("{}", coeff_u1024.0[0])
            } else {
                // Large value, use hex with 0x prefix
                // Build hex string from limbs (big-endian order for display)
                let mut hex_str = String::from("0x");
                let mut started = false;
                for &limb in coeff_u1024.0.iter().rev() {
                    if !started && limb == 0 {
                        continue; // Skip leading zero limbs
                    }
                    if started {
                        // After first non-zero limb, pad to 16 hex digits
                        hex_str.push_str(&format!("{:016x}", limb));
                    } else {
                        // First non-zero limb, no padding
                        hex_str.push_str(&format!("{:x}", limb));
                        started = true;
                    }
                }
                hex_str
            };

            // Add + sign for non-first terms
            if !first {
                write!(f, " + ")?;
            }
            first = false;

            match i {
                0 => {
                    // Constant term
                    write!(f, "{}", coeff_str)?;
                }
                1 => {
                    // Linear term
                    if is_one {
                        write!(f, "x")?;
                    } else {
                        write!(f, "{}x", coeff_str)?;
                    }
                }
                _ => {
                    // Higher degree terms
                    if is_one {
                        write!(f, "x^{}", i)?;
                    } else {
                        write!(f, "{}x^{}", coeff_str, i)?;
                    }
                }
            }
        }

        // Handle case where all coefficients were zero
        if first {
            write!(f, "0")?;
        }

        Ok(())
    }
}
