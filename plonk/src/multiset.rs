use std::ops::{Deref, DerefMut};

use ark_bls12_381::FrParameters;
use ark_ff::Fp256;

#[derive(Debug)]
pub struct MultiSet(Vec<Fp256<FrParameters>>);

impl Deref for MultiSet {
    type Target = Vec<Fp256<FrParameters>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for MultiSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<Vec<Fp256<FrParameters>>> for MultiSet {
    fn from(vec: Vec<Fp256<FrParameters>>) -> Self {
        MultiSet(vec)
    }
}

impl MultiSet {
    pub fn new() -> Self {
        MultiSet(Vec::new())
    }
}