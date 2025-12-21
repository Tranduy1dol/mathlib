//! Multivariate polynomial implementation for ZK applications.
//!
//! Provides multivariate polynomials over finite fields with support for:
//! - Arbitrary number of variables
//! - Sparse representation using monomial map
//! - Evaluation and partial evaluation
//! - Basic arithmetic operations

use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

use crate::{FieldConfig, FieldElement};

/// A monomial represented as a vector of exponents.
/// For variables x0, x1, ..., xn, the monomial x0^e0 * x1^e1 * ... * xn^en
/// is represented as the vector [e0, e1, ..., en].
pub type Exponent = Vec<usize>;

/// A multivariate polynomial over a finite field.
///
/// Uses a sparse representation mapping exponent vectors to coefficients.
/// Only non-zero terms are stored.
#[derive(Clone)]
pub struct MultivariatePolynomial<C: FieldConfig> {
    /// Number of variables
    pub num_vars: usize,
    /// Mapping from exponent vectors to coefficients
    pub terms: BTreeMap<Exponent, FieldElement<C>>,
}

impl<C: FieldConfig> MultivariatePolynomial<C> {
    /// Creates a new multivariate polynomial with the given number of variables.
    pub fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            terms: BTreeMap::new(),
        }
    }

    /// Creates the zero polynomial.
    pub fn zero(num_vars: usize) -> Self {
        Self::new(num_vars)
    }

    /// Creates the constant polynomial 1.
    pub fn one(num_vars: usize) -> Self {
        let mut poly = Self::new(num_vars);
        poly.add_term(vec![0; num_vars], FieldElement::one());
        poly
    }

    /// Creates a constant polynomial.
    pub fn constant(num_vars: usize, c: FieldElement<C>) -> Self {
        let mut poly = Self::new(num_vars);
        if !c.is_zero() {
            poly.add_term(vec![0; num_vars], c);
        }
        poly
    }

    /// Creates a polynomial representing a single variable x_i.
    pub fn variable(num_vars: usize, var_index: usize) -> Self {
        assert!(var_index < num_vars, "Variable index out of bounds");
        let mut poly = Self::new(num_vars);
        let mut exp = vec![0; num_vars];
        exp[var_index] = 1;
        poly.add_term(exp, FieldElement::one());
        poly
    }

    /// Creates a monomial c * x0^e0 * x1^e1 * ... * xn^en.
    pub fn monomial(num_vars: usize, exponents: Exponent, coeff: FieldElement<C>) -> Self {
        assert_eq!(
            exponents.len(),
            num_vars,
            "Exponent vector length must match num_vars"
        );
        let mut poly = Self::new(num_vars);
        if !coeff.is_zero() {
            poly.add_term(exponents, coeff);
        }
        poly
    }

    /// Returns true if this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Returns the number of non-zero terms.
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Returns the total degree of the polynomial.
    /// This is the maximum sum of exponents across all terms.
    pub fn total_degree(&self) -> Option<usize> {
        self.terms.keys().map(|exp| exp.iter().sum()).max()
    }

    /// Returns the degree in a specific variable.
    pub fn degree_in(&self, var_index: usize) -> usize {
        assert!(var_index < self.num_vars, "Variable index out of bounds");
        self.terms
            .keys()
            .map(|exp| exp[var_index])
            .max()
            .unwrap_or(0)
    }

    /// Adds a term to the polynomial.
    /// If a term with the same exponent exists, coefficients are added.
    pub fn add_term(&mut self, exponents: Exponent, coeff: FieldElement<C>) {
        assert_eq!(
            exponents.len(),
            self.num_vars,
            "Exponent vector length must match num_vars"
        );

        if coeff.is_zero() {
            return;
        }

        let entry = self.terms.entry(exponents).or_insert(FieldElement::zero());
        *entry = *entry + coeff;

        // Remove if resulting coefficient is zero
        if entry.is_zero() {
            let exp = self
                .terms
                .keys()
                .find(|k| self.terms[*k].is_zero())
                .cloned();
            if let Some(e) = exp {
                self.terms.remove(&e);
            }
        }
    }

    /// Gets the coefficient for a given exponent.
    pub fn get_coefficient(&self, exponents: &Exponent) -> FieldElement<C> {
        self.terms
            .get(exponents)
            .copied()
            .unwrap_or_else(FieldElement::zero)
    }

    /// Evaluates the polynomial at a given point.
    pub fn evaluate(&self, point: &[FieldElement<C>]) -> FieldElement<C> {
        assert_eq!(
            point.len(),
            self.num_vars,
            "Point dimension must match num_vars"
        );

        let mut result = FieldElement::zero();

        for (exponents, coeff) in &self.terms {
            let mut term_value = *coeff;
            for (i, &exp) in exponents.iter().enumerate() {
                // Compute point[i]^exp
                let mut power = FieldElement::one();
                for _ in 0..exp {
                    power = power * point[i];
                }
                term_value = term_value * power;
            }
            result = result + term_value;
        }

        result
    }

    /// Partially evaluates the polynomial by fixing some variables.
    /// `assignments` is a map from variable index to value.
    pub fn partial_evaluate(&self, assignments: &BTreeMap<usize, FieldElement<C>>) -> Self {
        let remaining_vars: Vec<usize> = (0..self.num_vars)
            .filter(|i| !assignments.contains_key(i))
            .collect();

        let new_num_vars = remaining_vars.len();
        let mut result = Self::new(new_num_vars);

        for (exponents, coeff) in &self.terms {
            let mut term_coeff = *coeff;
            let mut new_exponents = Vec::with_capacity(new_num_vars);

            for (i, &exp) in exponents.iter().enumerate() {
                if let Some(&val) = assignments.get(&i) {
                    // Variable is assigned - multiply coefficient by val^exp
                    let mut power = FieldElement::one();
                    for _ in 0..exp {
                        power = power * val;
                    }
                    term_coeff = term_coeff * power;
                } else {
                    // Variable remains - keep its exponent
                    new_exponents.push(exp);
                }
            }

            if !term_coeff.is_zero() {
                result.add_term(new_exponents, term_coeff);
            }
        }

        result
    }

    /// Multiplies the polynomial by a scalar.
    pub fn scale(&self, scalar: &FieldElement<C>) -> Self {
        if scalar.is_zero() {
            return Self::zero(self.num_vars);
        }

        let mut result = Self::new(self.num_vars);
        for (exp, coeff) in &self.terms {
            result.add_term(exp.clone(), *coeff * *scalar);
        }
        result
    }

    /// Converts a univariate polynomial to multivariate (single variable).
    pub fn from_univariate(poly: &crate::poly::univariate::Polynomial<C>) -> Self {
        let mut result = Self::new(1);
        for (i, coeff) in poly.coeffs.iter().enumerate() {
            if !coeff.is_zero() {
                result.add_term(vec![i], *coeff);
            }
        }
        result
    }

    /// Converts to univariate if this has only one variable.
    pub fn to_univariate(&self) -> Option<crate::poly::univariate::Polynomial<C>> {
        if self.num_vars != 1 {
            return None;
        }

        let degree = self.degree_in(0);
        let mut coeffs = vec![FieldElement::zero(); degree + 1];

        for (exp, coeff) in &self.terms {
            coeffs[exp[0]] = *coeff;
        }

        Some(crate::poly::univariate::Polynomial::new(coeffs))
    }
}

// Arithmetic operations

impl<C: FieldConfig> Add for MultivariatePolynomial<C> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        assert_eq!(
            self.num_vars, rhs.num_vars,
            "Number of variables must match"
        );

        let mut result = self.clone();
        for (exp, coeff) in rhs.terms {
            result.add_term(exp, coeff);
        }
        result
    }
}

impl<C: FieldConfig> Sub for MultivariatePolynomial<C> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self + (-rhs)
    }
}

impl<C: FieldConfig> Neg for MultivariatePolynomial<C> {
    type Output = Self;

    fn neg(self) -> Self {
        let mut result = Self::new(self.num_vars);
        for (exp, coeff) in self.terms {
            result.terms.insert(exp, -coeff);
        }
        result
    }
}

impl<C: FieldConfig> Mul for MultivariatePolynomial<C> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        assert_eq!(
            self.num_vars, rhs.num_vars,
            "Number of variables must match"
        );

        let mut result = Self::new(self.num_vars);

        for (exp1, coeff1) in &self.terms {
            for (exp2, coeff2) in &rhs.terms {
                // Add exponents component-wise
                let new_exp: Exponent = exp1
                    .iter()
                    .zip(exp2.iter())
                    .map(|(&e1, &e2)| e1 + e2)
                    .collect();

                let new_coeff = *coeff1 * *coeff2;
                result.add_term(new_exp, new_coeff);
            }
        }

        result
    }
}

impl<C: FieldConfig> PartialEq for MultivariatePolynomial<C> {
    fn eq(&self, other: &Self) -> bool {
        if self.num_vars != other.num_vars {
            return false;
        }
        if self.terms.len() != other.terms.len() {
            return false;
        }
        for (exp, coeff) in &self.terms {
            match other.terms.get(exp) {
                Some(other_coeff) => {
                    if coeff.to_u1024() != other_coeff.to_u1024() {
                        return false;
                    }
                }
                None => return false,
            }
        }
        true
    }
}

impl<C: FieldConfig> Eq for MultivariatePolynomial<C> {}

impl<C: FieldConfig> fmt::Debug for MultivariatePolynomial<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MultivariatePolynomial({} vars, {} terms)",
            self.num_vars,
            self.terms.len()
        )
    }
}

impl<C: FieldConfig> fmt::Display for MultivariatePolynomial<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            return write!(f, "0");
        }

        let mut first = true;
        let one = crate::U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

        for (exponents, coeff) in self.terms.iter().rev() {
            if coeff.is_zero() {
                continue;
            }

            let coeff_u1024 = coeff.to_u1024();
            let is_one = coeff_u1024.0 == one.0;
            let is_constant = exponents.iter().all(|&e| e == 0);

            let coeff_str = if coeff_u1024.0[1..].iter().all(|&x| x == 0) {
                format!("{}", coeff_u1024.0[0])
            } else {
                format!("0x{:x}", coeff_u1024.0[0])
            };

            if !first {
                write!(f, " + ")?;
            }
            first = false;

            if is_constant {
                write!(f, "{}", coeff_str)?;
            } else {
                if !is_one {
                    write!(f, "{}", coeff_str)?;
                }

                for (i, &exp) in exponents.iter().enumerate() {
                    if exp > 0 {
                        if exp == 1 {
                            write!(f, "x{}", i)?;
                        } else {
                            write!(f, "x{}^{}", i, exp)?;
                        }
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

    type MvPoly = MultivariatePolynomial<DefaultFieldConfig>;

    #[test]
    fn test_multivariate_basic() {
        let mut p = MvPoly::new(2);
        p.add_term(vec![0, 0], fp!(5u64)); // 5
        p.add_term(vec![1, 0], fp!(3u64)); // 3*x0
        p.add_term(vec![0, 1], fp!(2u64)); // 2*x1

        assert_eq!(p.num_terms(), 3);
        assert_eq!(p.total_degree(), Some(1));
    }

    #[test]
    fn test_multivariate_evaluate() {
        // p(x0, x1) = 1 + x0 + x1
        let mut p = MvPoly::new(2);
        p.add_term(vec![0, 0], fp!(1u64));
        p.add_term(vec![1, 0], fp!(1u64));
        p.add_term(vec![0, 1], fp!(1u64));

        // Evaluate at (2, 3): 1 + 2 + 3 = 6
        let result = p.evaluate(&[fp!(2u64), fp!(3u64)]);
        assert_eq!(result.to_u1024(), crate::u1024!(6));
    }

    #[test]
    fn test_multivariate_add() {
        let mut p1 = MvPoly::new(2);
        p1.add_term(vec![1, 0], fp!(2u64)); // 2*x0

        let mut p2 = MvPoly::new(2);
        p2.add_term(vec![0, 1], fp!(3u64)); // 3*x1

        let sum = p1 + p2;
        assert_eq!(sum.num_terms(), 2);
    }

    #[test]
    fn test_multivariate_mul() {
        // (1 + x0) * (1 + x1) = 1 + x0 + x1 + x0*x1
        let mut p1 = MvPoly::new(2);
        p1.add_term(vec![0, 0], fp!(1u64));
        p1.add_term(vec![1, 0], fp!(1u64));

        let mut p2 = MvPoly::new(2);
        p2.add_term(vec![0, 0], fp!(1u64));
        p2.add_term(vec![0, 1], fp!(1u64));

        let product = p1 * p2;
        assert_eq!(product.num_terms(), 4);
    }

    #[test]
    fn test_multivariate_variable() {
        let x0 = MvPoly::variable(3, 0);
        let x1 = MvPoly::variable(3, 1);

        assert_eq!(x0.degree_in(0), 1);
        assert_eq!(x0.degree_in(1), 0);
        assert_eq!(x1.degree_in(1), 1);
    }
}
