use halo2curves::{
    ff::PrimeField,
    pasta::{Fp, Fq},
};

use num_bigint::BigUint;
use num_traits::Num;
use rand_core::OsRng;

use crate::{utils::modulus, Integer, COP};

fn run_cop<W: PrimeField, N: PrimeField>() {
    let double_n = |n: usize, int: &Integer| {
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

    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;
    let rng = &mut XorShiftRng::from_seed([1u8; 16]);
    // let rng = &mut OsRng;

    let wrong_modulus = &modulus::<W>();
    let native_modulus = &modulus::<N>();

    let limb_size = 51;
    let overflow_size = 3;
    let cop = COP::new(
        wrong_modulus,
        native_modulus,
        limb_size,
        overflow_size,
        None,
        None,
    );

    let w0 = cop.rand(rng);
    let w1 = cop.rand(rng);
    // let w0 = cop.new_int(&BigUint::from(2));
    // let w1 = cop.new_int(&BigUint::from(5));
    let w0 = double_n(0, &w0);
    let w1 = double_n(0, &w1);
    // let witness = &cop.red_witness(&w0);
    // cop.ver_red::<N>(witness, &w0);
    // let witness = &cop.red_witness(&w1);
    // cop.ver_red::<N>(witness, &w1);
    let witness = &cop.mul_witness(&w0, &w1, &[]);
    cop.ver_mul::<N>(witness, &w0, &w1, &[]);
    let witness = &cop.div_witness(&w0, &w1);
    cop.ver_div::<N>(witness, &w0, &w1);
}

#[test]
fn test_cop() {
    run_cop::<Fq, Fp>();
}
