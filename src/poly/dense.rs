use std::fmt;
use std::ops::{Add, Mul};

use crate::FieldElement;

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
    /// ```rust,ignore
    /// use crate::poly::dense::DensePolynomial;
    /// use crate::field::FieldElement;
    ///
    /// // Create a polynomial and have trailing zero coefficients trimmed
    /// let coeffs = vec![ /* FieldElement instances */ ];
    /// let poly = DensePolynomial::new(coeffs);
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
    /// ```ignore
    /// // Given a polynomial constructed with trailing zero field elements,
    /// // constructing via `DensePolynomial::new` will result in those trailing
    /// // zeros being removed (internally by `trim`).
    /// let p = DensePolynomial::new(vec![/* nonzero */]);
    /// // trailing zero coefficients are removed so the length is shorter than input
    /// assert!(p.coeffs.len() < 3);
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
    /// ```ignore
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
    /// ```ignore
    /// // Construct a polynomial p(x) = 3 + 2*x + 1*x^2 (coeffs are [3, 2, 1])
    /// // let params = /* field parameters */;
    /// // let three = FieldElement::from_u64(3, params);
    /// // let two = FieldElement::from_u64(2, params);
    /// // let one = FieldElement::from_u64(1, params);
    /// // let x = FieldElement::from_u64(5, params);
    /// // let p = DensePolynomial::new(vec![three, two, one]);
    /// // let y = p.evaluate(&x);
    /// // assert_eq!(y, /* expected FieldElement value */);
    /// ```
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
    /// ```ignore
    /// use crate::poly::dense::DensePolynomial;
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
            new_coeffs.push(a.clone() + b.clone());
        }

        Self::new(new_coeffs)
    }
}

impl<'a> Mul for DensePolynomial<'a> {
    type Output = Self;
    /// Computes the product of two polynomials and returns the resulting polynomial.
    ///
    /// The resulting polynomial's coefficients are the discrete convolution of the input
    /// coefficient vectors (formal polynomial multiplication). If either operand is the
    /// zero polynomial (empty coefficients), the result is the zero polynomial.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// # use crate::poly::DensePolynomial;
    /// # use crate::field::FieldElement;
    /// // (1 + 2x) * (3 + 4x) = 3 + 10x + 8x^2
    /// let a = DensePolynomial::new(vec![FieldElement::from(1u64), FieldElement::from(2u64)]);
    /// let b = DensePolynomial::new(vec![FieldElement::from(3u64), FieldElement::from(4u64)]);
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
                let product = a.clone() * b.clone();
                res[i + j] = res[i + j].clone() + product;
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
    /// ```ignore
    /// let p = DensePolynomial::zero::<_>();
    /// let s = format!("{:?}", p);
    /// assert!(s.starts_with("Poly"));
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Poly{:?}", self.coeffs)
    }
}
