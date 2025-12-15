use std::fmt;
use std::ops::{Add, Mul};

use crate::FieldElement;
use crate::poly::ntt::{intt, ntt};

#[derive(Clone)]
pub struct DensePolynomial<'a> {
    pub coeffs: Vec<FieldElement<'a>>,
}

impl<'a> DensePolynomial<'a> {
    /// Constructs a DensePolynomial from the given coefficient vector, removing any trailing coefficients that are the field zero.
    ///
    /// The input vector order is preserved; trailing zero coefficients are dropped so that the internal representation has no unnecessary trailing zeros. If all coefficients are zero the resulting polynomial is empty (zero polynomial).
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont};
    /// use mathlib::{DensePolynomial, FieldElement};
    ///
    /// // Create a polynomial and have trailing zero coefficients trimmed
    /// let params = mont!(17u64, 2u64);
    /// let coeffs = vec![FieldElement::one(&params), FieldElement::zero(&params)];
    /// let poly = DensePolynomial::new(coeffs);
    /// assert_eq!(poly.coeffs.len(), 1);
    /// ```
    pub fn new(coeffs: Vec<FieldElement<'a>>) -> Self {
        let mut poly = Self { coeffs };
        poly.trim();
        poly
    }

    /// Remove trailing zero coefficients from the polynomial's coefficient vector.
    ///
    /// This method repeatedly pops the last coefficient while that coefficient's
    /// internal `to_u1024().0` representation consists entirely of zeros. It
    /// makes no changes to leading or interior coefficients.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{mont};
    /// use mathlib::{DensePolynomial, FieldElement};
    ///
    /// // Given a polynomial constructed with trailing zero field elements,
    /// // constructing via `DensePolynomial::new` will result in those trailing
    /// // zeros being removed (internally by `trim`).
    /// let params = mont!(17u64, 2u64);
    /// let p = DensePolynomial::new(vec![FieldElement::one(&params), FieldElement::zero(&params)]);
    /// // trailing zero coefficients are removed so the length is shorter than input
    /// assert!(p.coeffs.len() < 2);
    /// ```
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
    ///
    /// The returned `DensePolynomial` has no coefficients (`coeffs` is an empty `Vec`)
    /// and represents the additive identity polynomial.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::DensePolynomial;
    ///
    /// let p = DensePolynomial::zero();
    /// assert!(p.coeffs.is_empty());
    /// ```
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Evaluate the polynomial at the given point.
    ///
    /// Returns the polynomial's value evaluated at `x`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont, u1024};
    /// use mathlib::DensePolynomial;
    ///
    /// // Construct a polynomial p(x) = 3 + 2*x + 1*x^2 (coeffs are [3, 2, 1])
    /// let params = mont!(17u64, 2u64);
    /// let three = fp!(3u64, &params);
    /// let two = fp!(2u64, &params);
    /// let one = fp!(1u64, &params);
    /// let x = fp!(5u64, &params);
    /// let p = DensePolynomial::new(vec![three, two, one]);
    /// let y = p.evaluate(&x);
    /// // 3 + 2*5 + 1*5^2 = 3 + 10 + 25 = 38 = 4 mod 17
    /// assert_eq!(y.to_u1024(), u1024!(4u64));
    /// ```
    pub fn evaluate(&self, x: &FieldElement<'a>) -> FieldElement<'a> {
        if self.coeffs.is_empty() {
            return FieldElement::zero(x.params);
        }

        let mut res = *self.coeffs.last().unwrap();
        for i in (0..self.coeffs.len() - 1).rev() {
            res = (res * *x) + self.coeffs[i];
        }
        res
    }

    /// Multiplies two polynomials using the Number Theoretic Transform (NTT).
    ///
    /// This method performs multiplication in O(n log n) time complexity, which is significantly
    /// faster than the naive O(n^2) approach for large polynomials. It pads the coefficients
    /// to a power of two, transforms them to an evaluation form using NTT, performs pointwise
    /// multiplication, and transforms back using Inverse NTT.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, DensePolynomial, get_params};
    ///
    /// // (1 + 2x) * (3 + 4x) = 3 + 10x + 8x^2
    /// let params = get_params();
    /// let one = fp!(1u64, params);
    /// let two = fp!(2u64, params);
    /// let three = fp!(3u64, params);
    /// let four = fp!(4u64, params);
    ///
    /// let a = DensePolynomial::new(vec![one, two]);
    /// let b = DensePolynomial::new(vec![three, four]);
    /// let c = a.mul_fast(&b);
    /// assert_eq!(c.coeffs.len(), 3);
    /// ```
    pub fn mul_fast(&self, rhs: &Self) -> Self {
        if self.coeffs.is_empty() || rhs.coeffs.is_empty() {
            return Self::zero();
        }

        let output_len = self.coeffs.len() + rhs.coeffs.len() - 1;

        let size = output_len.next_power_of_two();

        let params = self.coeffs[0].params;
        let zero = FieldElement::zero(params);

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

impl<'a> Add for DensePolynomial<'a> {
    type Output = Self;
    /// Adds two dense polynomials coefficient-wise.
    ///
    /// The resulting polynomial has coefficients equal to the pairwise sum of the inputs'
    /// coefficients; trailing zero coefficients are removed.
    ///
    /// # Returns
    ///
    /// `DensePolynomial` representing the coefficient-wise sum of `self` and `rhs`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::DensePolynomial;
    ///
    /// let a = DensePolynomial::zero();
    /// let b = DensePolynomial::zero();
    /// let c = a + b;
    /// assert!(c.coeffs.is_empty());
    /// ```
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
            new_coeffs.push(*a + *b);
        }

        Self::new(new_coeffs)
    }
}

impl<'a> Mul for DensePolynomial<'a> {
    type Output = Self;
    /// Computes the product of two polynomials and returns the resulting polynomial.
    ///
    /// The resulting polynomial coefficients are the discrete convolution of the input
    /// coefficient vectors (formal polynomial multiplication). If either operand is the
    /// zero polynomial (empty coefficients), the result is the zero polynomial.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont, DensePolynomial};
    ///
    /// // (1 + 2x) * (3 + 4x) = 3 + 10x + 8x^2
    /// let params = mont!(17u64, 2u64);
    /// let one = fp!(1u64, &params);
    /// let two = fp!(2u64, &params);
    /// let three = fp!(3u64, &params);
    /// let four = fp!(4u64, &params);
    ///
    /// let a = DensePolynomial::new(vec![one, two]);
    /// let b = DensePolynomial::new(vec![three, four]);
    /// let c = a * b;
    /// assert_eq!(c.coeffs.len(), 3);
    /// ```
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
                let product = *a * *b;
                res[i + j] = res[i + j] + product;
            }
        }

        Self::new(res)
    }
}

impl<'a> fmt::Debug for DensePolynomial<'a> {
    /// Formats the polynomial for debug output.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::DensePolynomial;
    ///
    /// let p = DensePolynomial::zero();
    /// let s = format!("{:?}", p);
    /// assert!(s.starts_with("Poly"));
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Poly{:?}", self.coeffs)
    }
}
