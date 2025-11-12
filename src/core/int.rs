pub trait BigInt: Sized + Copy + Clone + Send + Sync + PartialEq + Eq + std::fmt::Debug {
    const ZERO: Self;
    const ONE: Self;

    fn carrying_add(&self, rhs: &Self) -> (Self, bool);
    fn borrowing_sub(&self, rhs: &Self) -> (Self, bool);
    fn conditional_select(a: &Self, b: &Self, condition: bool) -> Self;
}
