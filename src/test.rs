use halo2curves::{
    bn256::{Fq as BnFq, Fr as BnFr},
    ff::PrimeField,
    pasta::{Fp as PastaFp, Fq as PastaFq},
};

use rand_core::OsRng;

use crate::{aztec::Aztec, cop::COP, utils::modulus, Integer};

fn double_n(n: usize, int: &Integer) -> Integer {
    let mut acc = int.clone();
    for _ in 0..n {
        acc = acc.add(&acc)
    }
    acc
}

// fn add_n(n: usize, int: &Integer) -> Integer {
//     let mut acc = int.clone();
//     for _ in 0..n {
//         acc = acc.add(&int)
//     }
//     acc
// }

fn run_cop<W: PrimeField, N: PrimeField>() {
    // use rand_core::SeedableRng;
    // use rand_xorshift::XorShiftRng;
    // let rng = &mut XorShiftRng::from_seed([1u8; 16]);
    let rng = &mut OsRng;

    let wrong_modulus = &modulus::<W>();
    let native_modulus = &modulus::<N>();

    let limb_size = 51;
    let overflow_size = 3;
    let lookup_size = 17;
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

    let w0 = double_n(3, &w0);
    let w1 = double_n(3, &w1);
    let witness = &cop.red_witness(&w0);
    cop.ver_red::<N>(witness, &w0);
    let witness = &cop.red_witness(&w1);
    cop.ver_red::<N>(witness, &w1);
    let witness = &cop.mul_witness(&w0, &w1, &[]);
    cop.ver_mul::<N>(witness, &w0, &w1, &[], lookup_size);
    let witness = &cop.div_witness(&w0, &w1);
    cop.ver_div::<N>(witness, &w0, &w1);
}

#[test]
fn test_cop() {
    run_cop::<PastaFq, PastaFp>();
}

fn run_aztec<W: PrimeField, N: PrimeField>() {
    // use rand_core::SeedableRng;
    // use rand_xorshift::XorShiftRng;
    // let rng = &mut XorShiftRng::from_seed([1u8; 16]);
    let rng = &mut OsRng;

    // use num_bigint::BigUint;
    // use num_traits::Num;
    // let wrong_modulus = &BigUint::from_str_radix("122e824fb83ce0ad187c94004faff3eb926186a81d14688528275ef8087be41707ba638e584e91903cebaff25b423048689c8ed12f9fd9071dcd3dc73ebff2e98a116c25667a8f8160cf8aeeaf0a437e6913e6870000082f49d00000000008b", 16).unwrap();
    let wrong_modulus = &modulus::<W>();
    let native_modulus = &modulus::<N>();

    let lookup_size = 18;
    let limb_size = 90;
    let aztec = Aztec::new(wrong_modulus, native_modulus, limb_size);

    let w0 = aztec.rand(rng);
    let w1 = aztec.rand(rng);

    let w0 = double_n(0, &w0);
    let w1 = double_n(0, &w1);
    let witness = &aztec.mul_witness(&w0, &w1, &[]);
    aztec.ver_mul::<N>(witness, &w0, &w1, &[], lookup_size);
}

#[test]
fn test_aztec() {
    run_aztec::<BnFq, BnFr>();
}
