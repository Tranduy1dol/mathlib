//! Ring module for lattice-based cryptography.
//!
//! This module provides ring elements for working with polynomials in
//! Rq = Zq[X]/(X^N + 1).

pub mod element;

pub use element::{RingElement, RingElementState};
