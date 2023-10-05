use halo2curves::ff::PrimeField;
use num_bigint::BigUint;
use utils::{big_to_fe, compose};

pub mod aztec;
pub mod cop;
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

    pub fn app<N: PrimeField>(&self) -> Vec<N> {
        self.limbs.iter().map(|x| big_to_fe(x)).collect::<Vec<_>>()
    }
}
