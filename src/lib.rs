use halo2curves::ff::PrimeField;
use num_bigint::BigUint;
use num_bigint::RandBigInt;
use num_integer::div_ceil;
use num_integer::Integer as _;
use num_prime::nt_funcs::prev_prime;
use num_traits::{identities::One, Zero};
use rand_core::RngCore;
use utils::*;

#[cfg(test)]
mod test;
mod utils;

#[derive(Clone)]
pub struct Integer {
    limbs: Vec<BigUint>,
    value: BigUint,
    max: BigUint,
    max_values: Vec<BigUint>,
}

impl std::fmt::Debug for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug = f.debug_struct("Integer");

        debug.field(
            "value:  ",
            &format!("{}, 0x{}", self.value.bits(), self.value.to_str_radix(16)),
        );

        debug.field(
            "max:    ",
            &format!("{}, 0x{}", self.max.bits(), self.max.to_str_radix(16)),
        );

        self.limbs
            .iter()
            .zip(self.max_values.iter())
            .enumerate()
            .for_each(|(_, (limb, max))| {
                debug.field(
                    "limb:   ",
                    &format!("{}, 0x{}", max.bits(), limb.to_str_radix(16)),
                );
            });
        debug.finish()
    }
}

// impl<N: PrimeField> std::fmt::Debug for Integer {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         let mut debug = f.debug_struct("Integer");

//         debug.field(
//             "max:    ",
//             &format!("{}, 0x{}", self.max.bits(), self.max.to_str_radix(16)),
//         );

//         self.limbs
//             .iter()
//             .zip(self.max_values.iter())
//             .enumerate()
//             .for_each(|(_, (limb, max))| {
//                 debug.field(
//                     "limb:   ",
//                     &format!("{}, 0x{}", max.bits(), fe_to_big(limb).to_str_radix(16)),
//                 );
//             });
//         debug.finish()
//     }
// }

impl Integer {
    pub fn add(&self, other: &Self) -> Self {
        let mut limbs = Vec::with_capacity(self.limbs.len());
        for (a, b) in self.limbs.iter().zip(other.limbs.iter()) {
            limbs.push(a + b);
        }
        Integer {
            limbs,
            value: &self.value + &other.value,
            max: &self.max + &other.max,
            max_values: self
                .max_values
                .iter()
                .zip(other.max_values.iter())
                .map(|(a, b)| a + b)
                .collect::<Vec<_>>(),
        }
    }

    pub fn value<W: PrimeField>(&self, limb_size: usize) -> W {
        let value = compose(&self.limbs, limb_size);
        big_to_fe(&value)
    }
}

pub struct ReductionWitness {
    pub(crate) res: Integer,
    pub(crate) w_quotient: BigUint,
    pub(crate) m_quotients: Vec<BigUint>,
    pub(crate) _w_quotient_size: usize,
    pub(crate) _m_quotients_size: Vec<usize>,
}

#[derive(Debug)]
// W doesn't have to be prime actually but we need this thread to use util functions
pub struct COP {
    pub(crate) number_of_limbs: usize,
    pub(crate) limb_size: usize,
    pub(crate) m_set: Vec<BigUint>,

    pub(crate) bases: Vec<BigUint>,
    pub(crate) bases_in_wrong: Vec<BigUint>,
    pub(crate) neg_bases_in_wrong: Vec<BigUint>,
    pub(crate) bases_in_wrong_in_m: Vec<Vec<BigUint>>,
    pub(crate) neg_bases_in_wrong_in_m: Vec<Vec<BigUint>>,

    pub(crate) quotient_w_max: BigUint,
    pub(crate) quotient_m_max: BigUint,
    pub(crate) quotient_w_max_red: BigUint,
    pub(crate) quotient_m_max_red: BigUint,

    pub(crate) native: BigUint,
    pub(crate) wrong: BigUint,

    pub(crate) _wrong_in_native: BigUint,
    pub(crate) neg_wrong_in_native: BigUint,
    pub(crate) _wrong_in_m: Vec<BigUint>,
    pub(crate) neg_wrong_in_m: Vec<BigUint>,

    pub(crate) max_remainder: BigUint,
    pub(crate) max_remainder_limbs: Vec<BigUint>,
}

fn prs_red_add(e: &Integer, bases: &[BigUint]) -> (BigUint, BigUint) {
    fn prs_red_add(limbs: &[BigUint], bases: &[BigUint]) -> BigUint {
        limbs
            .iter()
            .zip(bases)
            .enumerate()
            .fold(BigUint::zero(), |acc, (_, (limb, base))| acc + base * limb)
    }

    let max = prs_red_add(&e.max_values, bases);
    let value = prs_red_add(&e.limbs, bases);
    (max, value)
}

fn prs_red_mul(e0: &Integer, e1: &Integer, bases: &[BigUint]) -> (BigUint, BigUint) {
    fn prs_red_mul(w0_limbs: &[BigUint], w1_limbs: &[BigUint], bases: &[BigUint]) -> BigUint {
        w0_limbs
            .iter()
            .enumerate()
            .fold(BigUint::zero(), |acc, (i, w0_limb)| {
                acc + w1_limbs
                    .iter()
                    .enumerate()
                    .fold(BigUint::zero(), |acc, (j, w1_limb)| {
                        acc + &bases[i + j] * w0_limb * w1_limb
                    })
            })
    }

    let max = prs_red_mul(&e0.max_values, &e1.max_values, bases);
    let value = prs_red_mul(&e0.limbs, &e1.limbs, bases);
    (max, value)
}

impl COP {
    pub fn rand(&self, rng: &mut impl RngCore) -> Integer {
        let value = rng.gen_biguint_below(&self.max_remainder);
        self.new_int(&value)
    }

    pub fn new_int(&self, value: &BigUint) -> Integer {
        let max_values = self.max_remainder_limbs.clone();
        Integer {
            max_values: max_values.clone(),
            max: compose(&max_values, self.limb_size),
            limbs: decompose(value, self.number_of_limbs, self.limb_size),
            value: value.clone(),
        }
    }

    // pub fn int_from_witness(&self, integer: &Integer) -> Integer {
    //     let limbs = integer
    //         .limbs
    //         .iter()
    //         .map(|limb| fe_to_big(limb))
    //         .collect::<Vec<_>>();
    //     let value = compose(&limbs, self.limb_size);

    //     Integer {
    //         max_values: integer.max_values.clone(),
    //         max: compose(&integer.max_values, self.limb_size),
    //         limbs,
    //         value,
    //     }
    // }

    // pub fn int_to_witness(&self, integer: Integer) -> Integer {
    //     let limbs = integer
    //         .limbs
    //         .iter()
    //         .map(|limb| big_to_fe::<N>(limb))
    //         .collect::<Vec<_>>();
    //     Integer            max_values: integer.max_values.clone(),
    //         max: integer.max,
    //         limbs,
    //         native: big_to_fe::<N>(&self.native),
    //     }
    // }

    pub fn base(&self) -> &BigUint {
        &self.bases[1]
    }

    fn find_m_set(mi_max: &BigUint, lcm_rest: &BigUint) -> Vec<BigUint> {
        let target = prev_prime::<BigUint>(mi_max, None).unwrap();
        let u = std::iter::successors(Some((target, BigUint::one())), |(target, acc)| {
            let target = prev_prime::<BigUint>(target, None).unwrap();
            let acc = acc * mi_max;
            (acc <= *lcm_rest).then_some((target, acc))
        })
        .collect::<Vec<_>>();
        u.iter().map(|(a, _)| a).cloned().collect()
    }

    pub fn new(
        wrong_modulus: &BigUint,
        native_modulus: &BigUint,
        limb_size: usize,
        overflow_size: usize,
        m_set: Option<Vec<BigUint>>,
        lookup_size: Option<usize>,
    ) -> Self {
        // we want to allow reduction free first degree operations ie addition, subtraction
        // so lets expand the size of `b` and find range bounds
        // `b = 2^(limb_size+overflow_size)`
        let overflow_base = BigUint::one() << (limb_size + overflow_size);

        // guarantee that limb representation covers field elements in wrong field
        let number_of_limbs = div_ceil(wrong_modulus.bits() as usize, limb_size);

        // obviously wrong modulus must be in representation range that is `b^n >= p`
        assert!(wrong_modulus < &(BigUint::one() << (limb_size * number_of_limbs)));

        // `quotient_w_max = n^2 * b^2` max value for `quotient_w` witness where `n` is number of limbs
        let quotient_w_max = &(&overflow_base * &overflow_base * number_of_limbs.pow(2));

        // `quotient_m_max = 2 * n^2 * b^2` max value for `s` witness
        let quotient_m_max = &(quotient_w_max * 2u64);

        // this time for reduction
        let quotient_w_max_red = &(&overflow_base * number_of_limbs);
        let quotient_m_max_red = &(quotient_w_max_red * 2u64);

        // `mi_max = p / 4 * n^2 * b^2` where `p` is native modulus
        let mi_max = &(native_modulus / (quotient_w_max * 4u64));

        // `lcm(M_set) = n^2 * b^2 * q` where `q` is wrong modulus
        // then we cancel out native modulus `lcm(M_rest) = n^2 * b^2 * q / p`
        let lcm_rest = quotient_w_max * 2u64 * wrong_modulus / native_modulus;

        let m_set = match m_set {
            Some(m_set) => m_set,
            None => Self::find_m_set(mi_max, &lcm_rest),
        };

        {
            let mut acc = BigUint::one();
            let mut k0 = 0;
            while acc <= lcm_rest {
                acc *= mi_max;

                k0 += 1;
            }
            let k1 = m_set.len();
            assert_eq!(k0, k1);
        }

        {
            // lcm check at intro of section 3 of COP paper
            let lcm_m = m_set
                .iter()
                .chain(std::iter::once(native_modulus))
                .product::<BigUint>();

            // `lcm(M) >= 2n^2 * q * b^2`
            assert!(lcm_m >= quotient_m_max * wrong_modulus);

            // wrap around check. section 3.2
            m_set.iter().for_each(|m| {
                assert!(&(quotient_w_max * m * &BigUint::from(4u64)) < native_modulus);
            });
        }

        // cost analysis
        {
            println!("COP ({number_of_limbs}, {limb_size}+{overflow_size})");
            println!("k:       {:?}", m_set.len());
            println!("q_w:     {:?}", (quotient_w_max - 1usize).bits());
            println!("q_m:     {:?}", (quotient_m_max - 1usize).bits());
            println!("q_w_red: {:?}", (quotient_w_max_red - 1usize).bits());
            println!("q_m_red: {:?}", (quotient_m_max_red - 1usize).bits());
            if let Some(lookup_size) = lookup_size {
                let quotient_w_size = (quotient_w_max - 1usize).bits();
                let r_lookup_n = div_ceil(quotient_w_size as usize, lookup_size);
                let quotient_m_max_size = (quotient_m_max - 1usize).bits();
                let s_lookup_n = div_ceil(quotient_m_max_size as usize, lookup_size);
                let limb_lookup_n = div_ceil(limb_size, lookup_size);
                let lookup_cost =
                    r_lookup_n + s_lookup_n * m_set.len() + limb_lookup_n * number_of_limbs;
                let second_degree_cost = number_of_limbs * number_of_limbs;
                let first_degree_cost = 2 + number_of_limbs;

                // for vanilla gate
                let composition_cost = second_degree_cost + first_degree_cost / 2;

                println!(
                    "w: {:?}, L: {}, n: {}, k: {}, lc: {:?}, cc: {:?}",
                    limb_size,
                    lookup_size,
                    number_of_limbs,
                    m_set.len(),
                    lookup_cost,
                    composition_cost
                );
            }
        }

        // find the actual base `b`
        let b = &(BigUint::one() << limb_size);
        let bases = powers(b, 2 * number_of_limbs - 1);

        let bases_in_wrong = bases.iter().map(|b| b % wrong_modulus).collect::<Vec<_>>();

        let neg_bases_in_wrong = bases
            .iter()
            .map(|b| wrong_modulus - (b % wrong_modulus))
            .collect::<Vec<_>>();

        let bases_in_wrong_in_m = m_set
            .iter()
            .map(|m| {
                bases_in_wrong
                    .iter()
                    .map(|b| b % m)
                    .collect::<Vec<BigUint>>()
            })
            .collect::<Vec<_>>();

        let neg_bases_in_wrong_in_m = m_set
            .iter()
            .map(|m| {
                neg_bases_in_wrong
                    .iter()
                    .map(|b| (b % m))
                    .collect::<Vec<BigUint>>()
            })
            .collect::<Vec<_>>();

        let wrong_in_native = wrong_modulus % native_modulus;
        let neg_wrong_in_native = native_modulus - &wrong_in_native;
        let wrong_in_m = m_set.iter().map(|m| wrong_modulus % m).collect::<Vec<_>>();
        let neg_wrong_in_m = m_set
            .iter()
            .map(|m| m - (wrong_modulus % m))
            .collect::<Vec<_>>();

        let max_remainder = (BigUint::one() << wrong_modulus.bits()) - 1usize;
        let max_most_significant_limb = &max_remainder >> ((number_of_limbs - 1) * limb_size);
        let max_limb = (BigUint::one() << limb_size) - 1usize;
        let mut max_remainder_limbs = vec![max_limb; number_of_limbs - 1];
        max_remainder_limbs.push(max_most_significant_limb);

        COP {
            max_remainder_limbs,
            max_remainder,

            number_of_limbs,
            limb_size,

            quotient_w_max: quotient_w_max.clone(),
            quotient_m_max: quotient_m_max.clone(),
            quotient_w_max_red: quotient_w_max_red.clone(),
            quotient_m_max_red: quotient_m_max_red.clone(),

            m_set,

            wrong: wrong_modulus.clone(),
            native: native_modulus.clone(),

            bases,
            bases_in_wrong,
            neg_bases_in_wrong,
            bases_in_wrong_in_m,
            neg_bases_in_wrong_in_m,

            _wrong_in_native: wrong_in_native,
            neg_wrong_in_native,
            _wrong_in_m: wrong_in_m,
            neg_wrong_in_m,
        }
    }

    pub fn red_witness(&self, e: &Integer) -> ReductionWitness {
        let witness = {
            // let e = self.int_from_witness(e);

            // find the result
            let res = {
                let res = &e.value % &self.wrong;
                self.new_int(&res)
            };

            // find quotient under wrong modulus
            let (max_w_quotient, w_quotient) = {
                let (base, neg_base) = (&self.bases_in_wrong, &self.neg_bases_in_wrong);

                let (max_e, e) = prs_red_add(&e, base);
                let (max_res, res) = prs_red_add(&res, neg_base);

                // find max possible quotient value under wrong modulus
                let max_w_quotient = {
                    let lhs = max_e + max_res;
                    let (max_w_quotient, _) = lhs.div_rem(&self.wrong);
                    assert!(max_w_quotient < self.quotient_w_max_red);
                    max_w_quotient
                };

                let w_quotient = {
                    let (w_quotient, must_be_zero) = (e + &res).div_rem(&self.wrong);
                    assert!(must_be_zero.is_zero());
                    w_quotient
                };

                (max_w_quotient, w_quotient)
            };

            // find quotients under auxilarry moduluses
            let (max_m_quotients, m_quotients): (Vec<BigUint>, Vec<BigUint>) = self
                .m_set
                .iter()
                .enumerate()
                .map(|(i, m)| {
                    let (base, neg_base) = (
                        &self.bases_in_wrong_in_m[i],
                        &self.neg_bases_in_wrong_in_m[i],
                    );

                    let (max_e, e) = &prs_red_add(&e, base);
                    let (max_res, res) = prs_red_add(&res, neg_base);

                    // find max possible quotient value under aux modulus
                    let max_m_quotient = {
                        let lhs = max_e + max_res + &max_w_quotient * &self.neg_wrong_in_m[i];
                        assert!(lhs < self.native);
                        let (max_m_quotient, _) = lhs.div_rem(&self.wrong);
                        assert!(max_m_quotient < self.quotient_m_max_red);
                        max_m_quotient
                    };

                    let lhs = e + res + &w_quotient * &self.neg_wrong_in_m[i];
                    let (m_quotient, must_be_zero) = lhs.div_rem(m);
                    assert!(must_be_zero.is_zero());

                    (max_m_quotient, m_quotient)
                })
                .unzip();

            // let w_quotient = big_to_fe::<N>(&w_quotient);
            // let res = self.int_to_witness(res);
            // let m_quotients = m_quotients
            //     .iter()
            //     .map(|m_quotient| big_to_fe::<N>(m_quotient))
            //     .collect::<Vec<_>>();

            let witness = ReductionWitness {
                res,
                w_quotient,
                m_quotients,
                _w_quotient_size: max_w_quotient.bits() as usize,
                _m_quotients_size: max_m_quotients.iter().map(|q| q.bits() as usize).collect(),
            };

            witness
        };

        witness
    }

    pub fn ver_red<N: PrimeField>(&self, witness: &ReductionWitness, e: &Integer) {
        assert_eq!(modulus::<N>(), self.native);

        let e = e.limbs.iter().map(big_to_fe::<N>).collect::<Vec<_>>();
        let res = witness
            .res
            .limbs
            .iter()
            .map(big_to_fe::<N>)
            .collect::<Vec<_>>();
        let w_quotient = big_to_fe::<N>(&witness.w_quotient);
        let m_quotients = witness
            .m_quotients
            .iter()
            .map(|m_quotient| big_to_fe::<N>(m_quotient))
            .collect::<Vec<_>>();

        // emulate circuit checks for native
        {
            let mut acc = e.iter().zip(self.bases_in_wrong.iter()).enumerate().fold(
                N::ZERO,
                |acc, (_, (limb, base))| {
                    let base = big_to_fe::<N>(base);
                    acc + base * limb
                },
            );

            let res = res
                .iter()
                .zip(self.neg_bases_in_wrong.iter())
                .enumerate()
                .fold(N::ZERO, |acc, (_, (limb, base))| {
                    let base = big_to_fe::<N>(base);
                    acc + base * limb
                });

            acc += &res;
            acc += w_quotient * big_to_fe::<N>(&self.neg_wrong_in_native);
            assert_eq!(acc, N::ZERO);
        }

        // emulate circuit checks for m_1
        {
            let mut acc = e
                .iter()
                .zip(self.bases_in_wrong_in_m[0].iter())
                .enumerate()
                .fold(N::ZERO, |acc, (_, (limb, base))| {
                    let base = big_to_fe::<N>(base);
                    acc + base * limb
                });

            let res = res
                .iter()
                .zip(self.neg_bases_in_wrong_in_m[0].iter())
                .enumerate()
                .fold(N::ZERO, |acc, (_, (limb, base))| {
                    let base = big_to_fe::<N>(base);
                    acc + base * limb
                });

            acc += &res;
            acc += w_quotient * big_to_fe::<N>(&self.neg_wrong_in_m[0]);
            acc -= m_quotients[0] * big_to_fe::<N>(&self.m_set[0]);
            assert_eq!(acc, N::ZERO);
        }
    }

    pub fn mul_witness(&self, w0: &Integer, w1: &Integer, to_add: &[Integer]) -> ReductionWitness {
        let witness = {
            // let to_add = to_add
            //     .iter()
            //     .map(|to_add| self.int_from_witness(to_add))
            //     .collect::<Vec<_>>();

            // find the result
            let res = {
                let mul = &w0.value * &w1.value;
                let to_add = to_add.iter().map(|to_add| &to_add.value).sum::<BigUint>();
                let res = (mul + to_add) % &self.wrong;
                self.new_int(&res)
            };

            // find quotient under wrong modulus
            let (max_w_quotient, w_quotient) = {
                let (base, neg_base) = (&self.bases_in_wrong, &self.neg_bases_in_wrong);

                let (max_mul, mul) = &prs_red_mul(&w0, &w1, base);
                let (max_to_add, to_add) = to_add.iter().fold(
                    (BigUint::zero(), BigUint::zero()),
                    |(acc_max, acc), cur| {
                        let (max_e, e) = prs_red_add(cur, base);
                        (acc_max + max_e, acc + e)
                    },
                );
                let (max_res, res) = prs_red_add(&res, neg_base);

                // find max possible quotient value under wrong modulus
                let max_w_quotient = {
                    let lhs = max_mul + max_to_add + max_res;
                    let (max_w_quotient, _) = lhs.div_rem(&self.wrong);
                    assert!(max_w_quotient < self.quotient_w_max);
                    max_w_quotient
                };

                let w_quotient = {
                    let (w_quotient, must_be_zero) = (mul + to_add + &res).div_rem(&self.wrong);
                    assert!(must_be_zero.is_zero());
                    w_quotient
                };

                (max_w_quotient, w_quotient)
            };

            // find quotients under auxilarry moduluses
            let (max_m_quotients, m_quotients): (Vec<BigUint>, Vec<BigUint>) = self
                .m_set
                .iter()
                .enumerate()
                .map(|(i, m)| {
                    let (base, neg_base) = (
                        &self.bases_in_wrong_in_m[i],
                        &self.neg_bases_in_wrong_in_m[i],
                    );

                    let (max_mul, mul) = &prs_red_mul(&w0, &w1, base);
                    let (max_to_add, to_add) = to_add.iter().fold(
                        (BigUint::zero(), BigUint::zero()),
                        |(acc_max, acc), cur| {
                            let (max_e, e) = prs_red_add(cur, base);
                            (acc_max + max_e, acc + e)
                        },
                    );
                    let (max_res, res) = prs_red_add(&res, neg_base);

                    // find max possible quotient value under aux modulus
                    let max_m_quotient = {
                        let lhs = max_mul
                            + max_to_add
                            + max_res
                            + &max_w_quotient * &self.neg_wrong_in_m[i];
                        // assert!(lhs < self.native);
                        let (max_m_quotient, _) = lhs.div_rem(&self.wrong);
                        // assert!(max_m_quotient < self.quotient_w_max);
                        max_m_quotient
                    };

                    let lhs = mul + to_add + res + &w_quotient * &self.neg_wrong_in_m[i];
                    let (m_quotient, must_be_zero) = lhs.div_rem(m);
                    assert!(must_be_zero.is_zero());

                    (max_m_quotient, m_quotient)
                })
                .unzip();

            let witness = ReductionWitness {
                res,
                w_quotient,
                m_quotients,
                _w_quotient_size: max_w_quotient.bits() as usize,
                _m_quotients_size: max_m_quotients.iter().map(|q| q.bits() as usize).collect(),
            };

            witness
        };

        witness
    }

    pub fn ver_mul<N: PrimeField>(
        &self,
        witness: &ReductionWitness,
        w0: &Integer,
        w1: &Integer,
        to_add: &[Integer],
    ) {
        assert_eq!(modulus::<N>(), self.native);
        let w0 = w0.limbs.iter().map(big_to_fe::<N>).collect::<Vec<_>>();
        let w1 = w1.limbs.iter().map(big_to_fe::<N>).collect::<Vec<_>>();
        let res = witness
            .res
            .limbs
            .iter()
            .map(big_to_fe::<N>)
            .collect::<Vec<_>>();
        let w_quotient = big_to_fe::<N>(&witness.w_quotient);
        let m_quotients = witness
            .m_quotients
            .iter()
            .map(|m_quotient| big_to_fe::<N>(m_quotient))
            .collect::<Vec<_>>();
        let to_add = to_add
            .iter()
            .map(|to_add| to_add.limbs.iter().map(big_to_fe::<N>).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        let mut mul = vec![N::ZERO; 2 * w0.len() - 1];
        w0.iter().enumerate().for_each(|(i, w0)| {
            w1.iter().enumerate().for_each(|(j, w1)| {
                mul[i + j] += *w0 * *w1;
            })
        });

        // emulate circuit checks for native modulus
        {
            let mul = mul
                .iter()
                .zip(self.bases_in_wrong.iter())
                .enumerate()
                .map(|(_, (limb, base))| *limb * big_to_fe::<N>(base))
                .sum::<N>();

            let res = res
                .iter()
                .zip(self.neg_bases_in_wrong.iter())
                .enumerate()
                .fold(N::ZERO, |acc, (_, (limb, base))| {
                    acc + *limb * big_to_fe::<N>(base)
                });

            let to_add = to_add
                .iter()
                .map(|to_add| {
                    to_add
                        .iter()
                        .zip(self.bases_in_wrong.iter())
                        .fold(N::ZERO, |acc, (limb, base)| {
                            acc + *limb * big_to_fe::<N>(base)
                        })
                })
                .sum::<N>();

            let mut acc = mul;
            acc += res;
            acc += to_add;
            acc += w_quotient * big_to_fe::<N>(&self.neg_wrong_in_native);
            assert_eq!(acc, N::ZERO);
        }

        // emulate circuit checks for m_1
        {
            let mul = mul
                .iter()
                .take(self.number_of_limbs)
                .zip(self.bases_in_wrong_in_m[0].iter())
                .enumerate()
                .map(|(_, (limb, base))| *limb * big_to_fe::<N>(base))
                .sum::<N>();

            let res = res
                .iter()
                .zip(self.neg_bases_in_wrong_in_m[0].iter())
                .enumerate()
                .fold(N::ZERO, |acc, (_, (limb, base))| {
                    acc + *limb * big_to_fe::<N>(base)
                });

            let to_add = to_add
                .iter()
                .map(|to_add| {
                    to_add
                        .iter()
                        .zip(self.bases_in_wrong_in_m[0].iter())
                        .fold(N::ZERO, |acc, (limb, base)| {
                            acc + *limb * big_to_fe::<N>(base)
                        })
                })
                .sum::<N>();

            println!("xx {:?}", w_quotient);
            println!("xx {:?}", m_quotients[0]);

            let mut acc = mul;
            acc += res;
            acc += to_add;
            acc += w_quotient * big_to_fe::<N>(&self.neg_wrong_in_m[0]);
            acc -= m_quotients[0] * big_to_fe::<N>(&self.m_set[0]);
            assert_eq!(acc, N::ZERO);
        }
    }

    pub fn div_witness(&self, numer: &Integer, denom: &Integer) -> ReductionWitness {
        let witness = {
            // let numer = self.int_from_witness(numer);
            // let denom = self.int_from_witness(denom);
            // find the result
            let res = (&numer.value * invert(&denom.value, &self.wrong)) % &self.wrong;
            let res = self.new_int(&res);

            // find quotient under wrong moduluses
            let (max_w_quotient, w_quotient) = {
                let (base, neg_base) = (&self.bases_in_wrong, &self.neg_bases_in_wrong);

                let (max_mul, mul) = prs_red_mul(&res, &denom, base);
                let (max_numer, numer) = prs_red_add(&numer, neg_base);

                let max_w_quotient = {
                    let (max_w_quotient, _) = (max_mul + &max_numer).div_rem(&self.wrong);
                    assert!(max_w_quotient < self.quotient_w_max);
                    max_w_quotient
                };

                let w_quotient = {
                    let (w_quotient, must_be_zero) = (mul + &numer).div_rem(&self.wrong);
                    assert!(must_be_zero.is_zero());
                    w_quotient
                };
                (max_w_quotient, w_quotient)
            };

            // find quotients under auxilarry moduluses
            let (max_m_quotients, m_quotients): (Vec<BigUint>, Vec<BigUint>) = self
                .m_set
                .iter()
                .enumerate()
                .map(|(i, m)| {
                    let base = &self.bases_in_wrong_in_m[i];
                    let neg_base = &self.neg_bases_in_wrong_in_m[i];

                    let (max_mul, mul) = prs_red_mul(&res, &denom, base);
                    let (max_numer, numer) = prs_red_add(&numer, neg_base);

                    let max_m_quotient = {
                        let lhs = &max_mul + &max_numer + &max_w_quotient * &self.neg_wrong_in_m[i];
                        assert!(lhs < self.native);
                        let (max_m_quotient, _) = lhs.div_rem(m);
                        assert!(max_m_quotient < self.quotient_m_max);
                        max_m_quotient
                    };

                    let m_quotient = {
                        let lhs = &mul + &numer + &w_quotient * &self.neg_wrong_in_m[i];
                        let (m_quotient, must_be_zero) = lhs.div_rem(m);
                        assert!(must_be_zero.is_zero());
                        m_quotient
                    };

                    (max_m_quotient, m_quotient)
                })
                .unzip();

            let witness = ReductionWitness {
                res,
                w_quotient,
                m_quotients,
                _w_quotient_size: max_w_quotient.bits() as usize,
                _m_quotients_size: max_m_quotients.iter().map(|q| q.bits() as usize).collect(),
            };

            witness
        };

        witness
    }

    pub fn ver_div<N: PrimeField>(
        &self,
        witness: &ReductionWitness,
        numer: &Integer,
        denom: &Integer,
    ) {
        assert_eq!(modulus::<N>(), self.native);
        let numer = numer.limbs.iter().map(big_to_fe::<N>).collect::<Vec<_>>();
        let denom = denom.limbs.iter().map(big_to_fe::<N>).collect::<Vec<_>>();
        let res = witness
            .res
            .limbs
            .iter()
            .map(big_to_fe::<N>)
            .collect::<Vec<_>>();
        let w_quotient = big_to_fe::<N>(&witness.w_quotient);
        let m_quotients = witness
            .m_quotients
            .iter()
            .map(|m_quotient| big_to_fe::<N>(m_quotient))
            .collect::<Vec<_>>();

        let mut mul = vec![N::ZERO; 2 * res.len() - 1];
        res.iter().enumerate().for_each(|(i, res)| {
            denom.iter().enumerate().for_each(|(j, denom)| {
                mul[i + j] += *res * *denom;
            })
        });

        // emulate circuit checks for native modulus
        {
            let mul = mul
                .iter()
                .zip(self.bases_in_wrong.iter())
                .enumerate()
                .map(|(_, (limb, base))| *limb * big_to_fe::<N>(base))
                .sum::<N>();

            let numer = numer
                .iter()
                .zip(self.neg_bases_in_wrong.iter())
                .fold(N::ZERO, |acc, (limb, base)| {
                    acc + *limb * big_to_fe::<N>(base)
                });

            let acc = mul + numer + w_quotient * big_to_fe::<N>(&self.neg_wrong_in_native);

            assert_eq!(acc, N::ZERO);
        }

        // emulate circuit checks for m_1
        {
            let mul = mul
                .iter()
                .zip(self.bases_in_wrong_in_m[0].iter())
                .enumerate()
                .map(|(_, (limb, base))| *limb * big_to_fe::<N>(base))
                .sum::<N>();

            let numer = numer
                .iter()
                .zip(self.neg_bases_in_wrong_in_m[0].iter())
                .fold(N::ZERO, |acc, (limb, base)| {
                    acc + *limb * big_to_fe::<N>(base)
                });

            let acc = mul + numer + w_quotient * big_to_fe::<N>(&self.neg_wrong_in_m[0])
                - m_quotients[0] * big_to_fe::<N>(&self.m_set[0]);
            assert_eq!(acc, N::ZERO);
        }
    }
}
