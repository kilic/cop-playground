use std::ops::Shl;

use halo2curves::ff::PrimeField;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};

//  for<'a> Mul<&'a Self, Output = Self>
pub(crate) fn schoolbook<T: Clone>(a: &[T], b: &[T]) -> Vec<Vec<T>>
where
    for<'a> &'a T: std::ops::Mul<&'a T, Output = T>,
{
    let mut wide = vec![vec![]; a.len() + b.len() - 1];
    for (i, a) in a.iter().enumerate() {
        for (j, b) in b.iter().enumerate() {
            wide[i + j].push(a * b);
        }
    }
    wide
}

pub(crate) fn _div_exact(a: &BigUint, b: &BigUint) -> BigUint {
    let (q, r) = a.div_rem(b);
    assert!(r.is_zero());
    q
}

pub(crate) fn powers(e: &BigUint, n: usize) -> Vec<BigUint> {
    let mut b = Vec::with_capacity(n);
    let mut cur = BigUint::one();
    for _ in 0..n {
        b.push(cur.clone());
        cur *= e;
    }
    b
}

pub(crate) fn invert(e: &BigUint, modulus: &BigUint) -> BigUint {
    e.modpow(&(modulus - 2usize), modulus)
}

pub(crate) fn decompose(e: &BigUint, number_of_limbs: usize, limb_size: usize) -> Vec<BigUint> {
    let mask = &(BigUint::one().shl(limb_size) - 1usize);
    (0usize..)
        .step_by(limb_size)
        .take(number_of_limbs)
        .map(|shift| ((e >> shift) & mask))
        .collect::<Vec<_>>()
}

pub(crate) fn compose(input: &[BigUint], limb_size: usize) -> BigUint {
    input
        .iter()
        .rev()
        .fold(BigUint::zero(), |acc, val| (acc << limb_size) + val)
}

pub(crate) fn modulus<F: PrimeField>() -> BigUint {
    fe_to_big(&-F::ONE) + 1usize
}

pub(crate) fn big_to_fe<F: PrimeField>(e: &BigUint) -> F {
    let modulus = modulus::<F>();
    let e = e % modulus;
    let bytes = e.to_bytes_le();
    let mut repr = F::Repr::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(&bytes[..]);
    F::from_repr(repr).unwrap()
}

pub(crate) fn fe_to_big<F: PrimeField>(fe: &F) -> BigUint {
    BigUint::from_bytes_le(fe.to_repr().as_ref())
}
