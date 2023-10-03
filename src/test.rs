use halo2curves::{
    ff::PrimeField,
    pasta::{Fp, Fq},
};

use rand_core::OsRng;

use crate::{WitnessInteger, COP};

fn run_cop<W: PrimeField, N: PrimeField>() {
    let double_n = |n: usize, int: &WitnessInteger<N>| {
        let mut acc = int.clone();
        for _ in 0..n {
            acc = acc.add(&acc)
        }
        acc
    };

    // let add_n = |n: usize, int: &WitnessInteger<N>| {
    //     let mut acc = int.clone();
    //     for _ in 0..n {
    //         acc = acc.add(&int)
    //     }
    //     acc
    // };

    // use rand_xorshift::XorShiftRng;
    // use rand_core::{SeedableRng};
    // let rng = &mut XorShiftRng::from_seed([1u8; 16]);
    let rng = &mut OsRng;

    let number_of_limbs = 5;
    let limb_size = 51;
    let overflow_size = 3;
    let cop = COP::<W, N>::new(number_of_limbs, limb_size, overflow_size, None, None);

    let w0 = cop.rand(rng);
    let w1 = cop.rand(rng);
    let w0 = double_n(3, &w0);
    let w1 = double_n(3, &w1);
    cop.reduction_witness(&w0);
    cop.reduction_witness(&w1);
    cop.mul_witness(&w0, &w1, &[]);
    cop.div_witness(&w0, &w1);
}

#[test]
fn test_cop() {
    run_cop::<Fq, Fp>();
}
