use halo2curves::ff::PrimeField;
use num_bigint::{BigUint, RandBigInt};
use num_integer::{div_ceil, Integer as _};
use num_traits::{identities::One, Zero};
use rand_core::RngCore;

use crate::{
    utils::{big_to_fe, compose, decompose, modulus, powers, schoolbook},
    Integer,
};

pub struct Aztec {
    number_of_limbs: usize,
    number_of_carries: usize,
    limb_size: usize,
    wrong_modulus: BigUint,
    _native_modulus: BigUint,
    _binary_modulus: BigUint,
    max_quotient: BigUint,
    max_quotient_limbs: Vec<BigUint>,
    max_remainder: BigUint,
    max_remainder_limbs: Vec<BigUint>,
    bases: Vec<BigUint>,
    _neg_wrong_in_binary: BigUint,
    _neg_wrong_in_native: BigUint,
    neg_wrong_in_binary_limbs: Vec<BigUint>,
}

pub struct MulWitness {
    pub(crate) quotient: Integer,
    pub(crate) result: Integer,
    pub(crate) carries: Vec<BigUint>,
    pub(crate) max_carries: Vec<usize>,
}

impl Aztec {
    pub fn new(wrong_modulus: &BigUint, native_modulus: &BigUint, limb_size: usize) -> Aztec {
        let number_of_limbs = div_ceil(wrong_modulus.bits() as usize, limb_size);

        let one = &BigUint::one();
        let max_limb = (one << limb_size) - 1usize;

        let max_remainder = &((one << wrong_modulus.bits()) - 1usize);
        let max_most_significant_limb = max_remainder >> ((number_of_limbs - 1) * limb_size);
        let mut max_remainder_limbs = vec![max_limb.clone(); number_of_limbs - 1];
        max_remainder_limbs.push(max_most_significant_limb);

        let pre_binary_modulus = wrong_modulus.pow(2) / native_modulus;
        let pre_binary_modulus_size = pre_binary_modulus.bits() as usize;
        let t = one << pre_binary_modulus_size;
        assert!(t * native_modulus > wrong_modulus.pow(2));

        // also number of limbs of binary modulus
        let number_of_carries = div_ceil(pre_binary_modulus_size, limb_size);
        let binary_modulus_size = number_of_carries * limb_size;
        let binary_modulus = &(one << binary_modulus_size);
        assert!(binary_modulus * native_modulus > wrong_modulus.pow(2));

        let crt_modulus = &(binary_modulus * native_modulus);

        let pre_max_quotient: &BigUint = &((crt_modulus - max_remainder) / wrong_modulus);
        let max_quotient = &((one << (pre_max_quotient.bits() - 1)) - 1usize);

        let max_quotient_bit_len = ((max_quotient * wrong_modulus + max_remainder).bits() - 1) / 2;
        let max_quotient = &((one << max_quotient_bit_len) - one);
        let max_most_significant_limb = max_quotient >> ((number_of_limbs - 1) * limb_size);
        let mut max_quotient_limbs = vec![max_limb; number_of_limbs - 1];
        max_quotient_limbs.push(max_most_significant_limb);

        let max_operand_bit_len = ((max_quotient * wrong_modulus + max_remainder).bits() - 1) / 2;
        let max_operand = &((one << max_operand_bit_len) - one);
        {
            let lhs = &(max_operand * max_operand);
            let rhs = &(max_quotient * wrong_modulus + max_remainder);
            assert!(binary_modulus > wrong_modulus);
            assert!(binary_modulus > native_modulus);
            assert!(max_remainder > wrong_modulus);
            assert!(max_operand > wrong_modulus);
            assert!(max_quotient > wrong_modulus);
            assert!(max_remainder < binary_modulus);
            assert!(max_operand < binary_modulus);
            assert!(max_quotient < binary_modulus);
            assert!(rhs < crt_modulus);
            assert!(lhs < rhs);
        }

        let neg_wrong_in_binary = binary_modulus - wrong_modulus;
        let neg_wrong_in_native = native_modulus - (wrong_modulus % native_modulus);
        let neg_wrong_in_binary_limbs =
            decompose(&neg_wrong_in_binary, number_of_carries, limb_size);

        let b = &(BigUint::one() << limb_size);
        let bases = powers(b, 2 * number_of_limbs - 1);

        Aztec {
            bases,
            limb_size,
            number_of_limbs,
            number_of_carries,
            wrong_modulus: wrong_modulus.clone(),
            _native_modulus: native_modulus.clone(),
            _binary_modulus: binary_modulus.clone(),
            max_remainder: max_remainder.clone(),
            max_remainder_limbs,
            max_quotient: max_quotient.clone(),
            max_quotient_limbs,

            _neg_wrong_in_binary: neg_wrong_in_binary,
            _neg_wrong_in_native: neg_wrong_in_native,
            neg_wrong_in_binary_limbs,
        }
    }

    pub fn base(&self) -> &BigUint {
        &self.bases[1]
    }

    pub fn rand(&self, rng: &mut impl RngCore) -> Integer {
        let value = rng.gen_biguint_below(&self.max_remainder);
        self.new_int_remainder(&value)
    }

    pub fn new_int(&self, value: &BigUint, max_values: &[BigUint]) -> Integer {
        let max = compose(max_values, self.limb_size);
        assert!(value < &max);
        Integer {
            max_values: max_values.to_vec(),
            max,
            limbs: decompose(value, self.number_of_limbs, self.limb_size),
            value: value.clone(),
        }
    }

    pub fn new_int_remainder(&self, value: &BigUint) -> Integer {
        let max_values = self.max_remainder_limbs.clone();
        self.new_int(value, &max_values[..])
    }

    pub fn new_int_quotient(&self, value: &BigUint) -> Integer {
        let max_values = self.max_quotient_limbs.clone();
        self.new_int(value, &max_values[..])
    }

    pub fn mul_witness(&self, w0: &Integer, w1: &Integer, to_add: &[Integer]) -> MulWitness {
        let to_add_sum = to_add.iter().map(|e| e.value.clone()).sum::<BigUint>();
        let (quotient, result) = (&w0.value * &w1.value + to_add_sum).div_rem(&self.wrong_modulus);
        assert!(quotient < self.max_quotient);

        let quotient = self.new_int_quotient(&quotient);
        let result = self.new_int_remainder(&result);

        let max_carries = {
            let t_ww = schoolbook(&w0.max_values, &w1.max_values);
            let t_pq = schoolbook(&quotient.max_values, &self.neg_wrong_in_binary_limbs);
            let schoolbook = t_ww.iter().zip(t_pq.iter());

            let mut carry = BigUint::zero();
            schoolbook
                .take(self.number_of_carries)
                .enumerate()
                .map(|(i, (ww, pq))| {
                    let to_add = to_add
                        .iter()
                        .map(|e| e.max_values[i].clone())
                        .sum::<BigUint>();
                    let ww = ww.iter().sum::<BigUint>();
                    let pq = pq.iter().sum::<BigUint>();
                    let t = ww + pq + &carry + to_add;
                    carry = &t >> self.limb_size;
                    carry.clone()
                })
                .collect::<Vec<_>>()
        };

        let carries = {
            let t_ww = schoolbook(&w0.limbs, &w1.limbs);
            let t_pq = schoolbook(&quotient.limbs, &self.neg_wrong_in_binary_limbs);

            let zero = BigUint::zero();
            let schoolbook = t_ww
                .iter()
                .zip(t_pq.iter())
                .zip(result.limbs.iter().chain(std::iter::repeat_with(|| &zero)));

            let mut carry = BigUint::zero();
            let carries = schoolbook
                .take(self.number_of_carries)
                .enumerate()
                .map(|(i, ((ww, pq), res))| {
                    let to_add = to_add.iter().map(|e| e.limbs[i].clone()).sum::<BigUint>();
                    let ww = ww.iter().sum::<BigUint>();
                    let pq = pq.iter().sum::<BigUint>();
                    let t = ww + pq + &carry - res + to_add;
                    carry = &t >> self.limb_size;
                    carry.clone()
                })
                .collect::<Vec<_>>();

            carries
                .iter()
                .zip(max_carries.iter())
                .for_each(|(carry, max_carry)| assert!((carry < max_carry)));

            carries
        };

        let max_carries = max_carries
            .iter()
            .map(|max_carry| max_carry.bits() as usize)
            .collect::<Vec<_>>();

        MulWitness {
            quotient,
            result,
            carries,
            max_carries,
        }
    }

    pub fn ver_mul<N: PrimeField>(
        &self,
        witness: &MulWitness,
        w0: &Integer,
        w1: &Integer,
        to_add: &[Integer],
        lookup_size: usize,
    ) {
        assert_eq!(modulus::<N>(), self._native_modulus);

        let w0 = w0.app::<N>();
        let w1 = w1.app::<N>();
        let to_add = to_add.iter().map(|e| e.app::<N>()).collect::<Vec<_>>();

        // excluding 'to_add' for simplicity
        let mut lookup_cost = 0;
        let mut first_degree_composition_cost = 0;
        let mut second_degree_composition_cost = 0;

        // assignment cost (finds the native value)
        let quotient = witness.quotient.app::<N>();
        first_degree_composition_cost += quotient.len() + 1;
        // decompose and lookup for quotient limbs
        for e in witness.quotient.max_values.iter() {
            lookup_cost += div_ceil(e.bits() as usize, lookup_size);
        }

        // assignment cost (finds the native value)
        let result = witness.result.app::<N>();
        first_degree_composition_cost += result.len() + 1;
        // decompose and lookup for result limbs
        for e in witness.result.max_values.iter() {
            lookup_cost += div_ceil(e.bits() as usize, lookup_size);
        }

        // decompose and lookup for carries
        for max_carry in witness.max_carries.iter() {
            lookup_cost += div_ceil(*max_carry, lookup_size);
        }

        let carries = witness
            .carries
            .iter()
            .map(|e| big_to_fe::<N>(e))
            .collect::<Vec<_>>();

        let mut wide_ww = vec![vec![]; self.number_of_carries];
        for (i, a) in w0.iter().enumerate() {
            for (j, b) in w1.iter().enumerate() {
                if i + j < self.number_of_carries {
                    second_degree_composition_cost += 1;
                    wide_ww[i + j].push(*a * *b);
                }
            }
        }
        let wide_ww = wide_ww.iter().map(|e| e.iter().sum::<N>());

        let mut wide_pq = vec![vec![]; self.number_of_carries];
        for (i, a) in quotient.iter().enumerate() {
            for (j, b) in self.neg_wrong_in_binary_limbs.iter().enumerate() {
                if i + j < self.number_of_carries {
                    first_degree_composition_cost += 1;
                    wide_pq[i + j].push(*a * big_to_fe::<N>(b));
                }
            }
        }
        let wide_pq = wide_pq.iter().map(|e| e.iter().sum::<N>());

        let mut carry_cur = N::ZERO;
        let base = big_to_fe::<N>(self.base());
        wide_ww
            .zip(wide_pq)
            .zip(
                result
                    .iter()
                    .map(Some)
                    .chain(std::iter::repeat_with(|| None)),
            )
            .zip(carries.iter())
            .enumerate()
            .for_each(|(i, (((ww, pq), res), carry))| {
                let to_add = to_add.iter().map(|to_add| to_add[i]).sum::<N>();

                // plus one for the carry
                first_degree_composition_cost += 1;
                let t = ww + to_add + pq + carry_cur;
                let t = match res {
                    Some(res) => {
                        // plus one for the result limb
                        first_degree_composition_cost += 1;
                        t - res
                    }
                    None => t,
                };

                assert_eq!(*carry * base, t);
                carry_cur = *carry;
            });

        println!(
            "MUL COST\nL: {lookup_size}, l: {lookup_cost}, fd: {first_degree_composition_cost}, sd: {second_degree_composition_cost}",
        );
    }
}
