//! Univariate polynomial with enhanced operations for ZK applications.
//!
//! Provides comprehensive polynomial operations including:
//! - Basic arithmetic (add, sub, mul, div, mod)
//! - Evaluation and interpolation
//! - Composition and derivative
//! - Division with remainder (zerofier)

use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

use crate::poly::ntt::{intt, ntt};
use crate::{FieldConfig, FieldElement};

/// A univariate polynomial over a finite field.
///
/// Coefficients are stored in ascending order of degree:
/// `coeffs[i]` is the coefficient of x^i.
#[derive(Clone)]
pub struct Polynomial<C: FieldConfig> {
    pub coeffs: Vec<FieldElement<C>>,
}

impl<C: FieldConfig> Polynomial<C> {
    /// Creates a new polynomial from coefficients.
    /// Trailing zeros are automatically removed.
    pub fn new(coeffs: Vec<FieldElement<C>>) -> Self {
        let mut poly = Self { coeffs };
        poly.trim();
        poly
    }

    /// Creates the zero polynomial.
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Creates the constant polynomial 1.
    pub fn one() -> Self {
        Self {
            coeffs: vec![FieldElement::one()],
        }
    }

    /// Creates a constant polynomial.
    pub fn constant(c: FieldElement<C>) -> Self {
        Self::new(vec![c])
    }

    /// Creates the polynomial x.
    pub fn x() -> Self {
        Self {
            coeffs: vec![FieldElement::zero(), FieldElement::one()],
        }
    }

    /// Creates a monomial c * x^degree.
    pub fn monomial(coeff: FieldElement<C>, degree: usize) -> Self {
        let mut coeffs = vec![FieldElement::zero(); degree + 1];
        coeffs[degree] = coeff;
        Self::new(coeffs)
    }

    /// Returns the degree of the polynomial.
    /// Returns None for the zero polynomial.
    pub fn degree(&self) -> Option<usize> {
        if self.coeffs.is_empty() {
            None
        } else {
            Some(self.coeffs.len() - 1)
        }
    }

    /// Returns true if this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Returns the leading coefficient.
    pub fn leading_coefficient(&self) -> Option<FieldElement<C>> {
        self.coeffs.last().copied()
    }

    /// Removes trailing zero coefficients.
    fn trim(&mut self) {
        while let Some(c) = self.coeffs.last() {
            if c.is_zero() {
                self.coeffs.pop();
            } else {
                break;
            }
        }
    }

    /// Evaluates the polynomial at point x using Horner's method.
    pub fn evaluate(&self, x: &FieldElement<C>) -> FieldElement<C> {
        if self.coeffs.is_empty() {
            return FieldElement::zero();
        }

        let mut result = *self.coeffs.last().unwrap();
        for i in (0..self.coeffs.len() - 1).rev() {
            result = result * *x + self.coeffs[i];
        }
        result
    }

    /// Evaluates the polynomial at multiple points.
    pub fn evaluate_batch(&self, points: &[FieldElement<C>]) -> Vec<FieldElement<C>> {
        points.iter().map(|x| self.evaluate(x)).collect()
    }

    /// Computes the formal derivative of the polynomial.
    pub fn derivative(&self) -> Self {
        if self.coeffs.len() <= 1 {
            return Self::zero();
        }

        let mut result = Vec::with_capacity(self.coeffs.len() - 1);
        for (i, coeff) in self.coeffs.iter().enumerate().skip(1) {
            // multiply by i
            let mut acc = FieldElement::zero();
            for _ in 0..i {
                acc = acc + *coeff;
            }
            result.push(acc);
        }
        Self::new(result)
    }

    /// Computes the polynomial modulo (x - root), i.e., P(x) mod (x - root).
    /// This is equivalent to P(root).
    pub fn mod_linear(&self, root: &FieldElement<C>) -> FieldElement<C> {
        self.evaluate(root)
    }

    /// Polynomial division with remainder.
    /// Returns (quotient, remainder) such that self = quotient * divisor + remainder.
    pub fn divide_with_remainder(&self, divisor: &Self) -> (Self, Self) {
        if divisor.is_zero() {
            panic!("Division by zero polynomial");
        }

        if self.is_zero() {
            return (Self::zero(), Self::zero());
        }

        let self_deg = match self.degree() {
            Some(d) => d,
            None => return (Self::zero(), Self::zero()),
        };
        let divisor_deg = match divisor.degree() {
            Some(d) => d,
            None => panic!("Division by zero polynomial"),
        };

        if self_deg < divisor_deg {
            return (Self::zero(), self.clone());
        }

        let mut remainder = self.coeffs.clone();
        let mut quotient = vec![FieldElement::zero(); self_deg - divisor_deg + 1];
        let lead_inv = divisor.leading_coefficient().unwrap().inv();

        for i in (0..=self_deg - divisor_deg).rev() {
            let coeff = remainder[i + divisor_deg] * lead_inv;
            quotient[i] = coeff;
            for j in 0..=divisor_deg {
                remainder[i + j] = remainder[i + j] - coeff * divisor.coeffs[j];
            }
        }

        (Self::new(quotient), Self::new(remainder))
    }

    /// Multiplies two polynomials using NTT for large degrees.
    pub fn mul_ntt(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }

        let output_len = self.coeffs.len() + other.coeffs.len() - 1;
        let size = output_len.next_power_of_two();

        let zero = FieldElement::zero();

        let mut a_coeffs = self.coeffs.clone();
        a_coeffs.resize(size, zero);

        let mut b_coeffs = other.coeffs.clone();
        b_coeffs.resize(size, zero);

        ntt(&mut a_coeffs);
        ntt(&mut b_coeffs);

        for i in 0..size {
            a_coeffs[i] = a_coeffs[i] * b_coeffs[i];
        }

        intt(&mut a_coeffs);
        a_coeffs.truncate(output_len);

        Self::new(a_coeffs)
    }

    /// Multiplies two polynomials using NTT (alias for `mul_ntt`).
    ///
    /// This is provided for backward compatibility with `DensePolynomial`.
    #[inline]
    pub fn mul_fast(&self, other: &Self) -> Self {
        self.mul_ntt(other)
    }

    /// Multiplies polynomial by a scalar.
    pub fn scale(&self, scalar: &FieldElement<C>) -> Self {
        Self::new(self.coeffs.iter().map(|c| *c * *scalar).collect())
    }

    /// Shifts coefficients by n (multiply by x^n).
    pub fn shift(&self, n: usize) -> Self {
        if self.is_zero() {
            return Self::zero();
        }

        let mut new_coeffs = vec![FieldElement::zero(); n];
        new_coeffs.extend(self.coeffs.clone());
        Self::new(new_coeffs)
    }

    /// Creates the zerofier polynomial for a set of points.
    /// This is the polynomial that evaluates to zero at all given points.
    /// Z(x) = (x - p0)(x - p1)...(x - pn)
    pub fn zerofier(points: &[FieldElement<C>]) -> Self {
        if points.is_empty() {
            return Self::one();
        }

        let mut result = Self::new(vec![-points[0], FieldElement::one()]);
        for point in points.iter().skip(1) {
            let factor = Self::new(vec![-*point, FieldElement::one()]);
            result = result * factor;
        }
        result
    }

    /// Lagrange interpolation: constructs a polynomial passing through given points.
    pub fn interpolate(points: &[FieldElement<C>], values: &[FieldElement<C>]) -> Self {
        assert_eq!(
            points.len(),
            values.len(),
            "Points and values must have same length"
        );

        if points.is_empty() {
            return Self::zero();
        }

        let n = points.len();
        let mut result = Self::zero();

        for i in 0..n {
            // Compute Lagrange basis polynomial L_i(x)
            let mut numerator = Self::one();
            let mut denominator = FieldElement::one();

            for j in 0..n {
                if i != j {
                    // numerator *= (x - points[j])
                    let factor = Self::new(vec![-points[j], FieldElement::one()]);
                    numerator = numerator * factor;

                    // denominator *= (points[i] - points[j])
                    denominator = denominator * (points[i] - points[j]);
                }
            }

            // L_i(x) = numerator / denominator
            let basis = numerator.scale(&denominator.inv());

            // result += values[i] * L_i(x)
            result = result + basis.scale(&values[i]);
        }

        result
    }

    /// Computes polynomial composition self(other(x)).
    pub fn compose(&self, other: &Self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }

        let mut result = Self::constant(*self.coeffs.last().unwrap());
        for i in (0..self.coeffs.len() - 1).rev() {
            result = result * other.clone() + Self::constant(self.coeffs[i]);
        }
        result
    }

    /// Returns the polynomial as coefficient vector.
    pub fn to_vec(&self) -> Vec<FieldElement<C>> {
        self.coeffs.clone()
    }
}

// Arithmetic traits

impl<C: FieldConfig> Add for Polynomial<C> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        if self.is_zero() {
            return rhs;
        }
        if rhs.is_zero() {
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

impl<C: FieldConfig> Sub for Polynomial<C> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self + (-rhs)
    }
}

impl<C: FieldConfig> Neg for Polynomial<C> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(self.coeffs.into_iter().map(|c| -c).collect())
    }
}

impl<C: FieldConfig> Mul for Polynomial<C> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }

        // Use NTT for large polynomials
        if self.coeffs.len() + rhs.coeffs.len() > 64 {
            return self.mul_ntt(&rhs);
        }

        let len = self.coeffs.len() + rhs.coeffs.len() - 1;
        let mut result = vec![FieldElement::zero(); len];

        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in rhs.coeffs.iter().enumerate() {
                result[i + j] = result[i + j] + *a * *b;
            }
        }

        Self::new(result)
    }
}

impl<C: FieldConfig> Div for Polynomial<C> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        self.divide_with_remainder(&rhs).0
    }
}

impl<C: FieldConfig> Rem for Polynomial<C> {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self {
        self.divide_with_remainder(&rhs).1
    }
}

impl<C: FieldConfig> PartialEq for Polynomial<C> {
    fn eq(&self, other: &Self) -> bool {
        if self.coeffs.len() != other.coeffs.len() {
            return false;
        }
        self.coeffs
            .iter()
            .zip(other.coeffs.iter())
            .all(|(a, b)| a.to_u1024() == b.to_u1024())
    }
}

impl<C: FieldConfig> Eq for Polynomial<C> {}

impl<C: FieldConfig> fmt::Debug for Polynomial<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Polynomial({})", self)
    }
}

impl<C: FieldConfig> fmt::Display for Polynomial<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.coeffs.is_empty() {
            return write!(f, "0");
        }

        let mut first = true;
        let one = crate::U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

        for (i, coeff) in self.coeffs.iter().enumerate().rev() {
            if coeff.is_zero() {
                continue;
            }

            let coeff_u1024 = coeff.to_u1024();
            let is_one = coeff_u1024.0 == one.0;

            let coeff_str = if coeff_u1024.0[1..].iter().all(|&x| x == 0) {
                format!("{}", coeff_u1024.0[0])
            } else {
                let mut hex_str = String::from("0x");
                let mut started = false;
                for &limb in coeff_u1024.0.iter().rev() {
                    if !started && limb == 0 {
                        continue;
                    }
                    if started {
                        hex_str.push_str(&format!("{:016x}", limb));
                    } else {
                        hex_str.push_str(&format!("{:x}", limb));
                        started = true;
                    }
                }
                hex_str
            };

            if !first {
                write!(f, " + ")?;
            }
            first = false;

            match i {
                0 => write!(f, "{}", coeff_str)?,
                1 => {
                    if is_one {
                        write!(f, "x")?;
                    } else {
                        write!(f, "{}x", coeff_str)?;
                    }
                }
                _ => {
                    if is_one {
                        write!(f, "x^{}", i)?;
                    } else {
                        write!(f, "{}x^{}", coeff_str, i)?;
                    }
                }
            }
        }

        if first {
            write!(f, "0")?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::config::DefaultFieldConfig;
    use crate::fp;

    type Poly = Polynomial<DefaultFieldConfig>;

    #[test]
    fn test_polynomial_basic() {
        let p = Poly::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
        assert_eq!(p.degree(), Some(2));
        assert!(!p.is_zero());
    }

    #[test]
    fn test_polynomial_zero() {
        let p = Poly::zero();
        assert!(p.is_zero());
        assert_eq!(p.degree(), None);
    }

    #[test]
    fn test_polynomial_derivative() {
        // d/dx (1 + 2x + 3x^2) = 2 + 6x
        let p = Poly::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
        let dp = p.derivative();
        assert_eq!(dp.coeffs.len(), 2);
    }

    #[test]
    fn test_polynomial_division() {
        // (x^2 - 1) / (x - 1) = x + 1
        let num = Poly::new(vec![-FieldElement::one(), fp!(0u64), FieldElement::one()]);
        let den = Poly::new(vec![-FieldElement::one(), FieldElement::one()]);
        let (q, r) = num.divide_with_remainder(&den);

        assert!(r.is_zero());
        assert_eq!(q.degree(), Some(1));
    }
}
