use ark_bls12_381::Fr;
use ark_ff::{FftField, One, Zero};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain,
};
use ark_poly::{Polynomial, UVPolynomial};
use kgz::{srs::Srs, KzgCommitment, KzgScheme};
use kgz::{KzgOpening, Poly};
use std::iter::repeat;
use std::ops::{Add, Mul};

use crate::challenges::ChallengeGenerator;
use crate::multiset::MultiSet;
use crate::proof::{vanishes, PolyProof};
use crate::utils::{add_to_poly, l0_poly, SlicedPoly};

pub struct LookupTable {
    t_table: MultiSet,
    // f_table: MultiSet,
    // table length
    size: usize,
    srs: Option<Srs>,
}

pub struct FTable {
    f_table: MultiSet,
}

impl FTable {
    pub fn new() -> Self {
        Self { f_table: MultiSet::new() }
    }
    pub fn add_table(&mut self, f_table: Vec<impl Into<Fr>>) {
        for item in f_table.into_iter() {
            let f_value = item.into();
            // if !self.t_table.contains(&f_value) {
            //     panic!("Item {:?} does not exist in t_table", f_value);
            // }
            self.f_table.push(f_value);
        }
    }
}

pub struct LookupProof {
    opening_commitments: [PolyProof; 2],
    quotient_commit: [KzgCommitment; 3],
    opening_evals: [Fr; 4],
    r_open: KzgOpening,
}

impl LookupTable {
    pub fn new(inputs: Vec<impl Into<Fr>>) -> Self {
        let inputs = inputs
            .into_iter()
            .map(Into::into)
            .collect::<Vec<_>>()
            .into();

        Self {
            t_table: inputs,
            size: 0,
            srs: None
        }
    }

    pub fn prove(&mut self, f_table: FTable) -> LookupProof {
        let f_table = self.fill_table(f_table.f_table);

        let (s_even, s_odd) = self.generate_s(f_table.clone().try_into().unwrap());

        let domain = <GeneralEvaluationDomain<Fr>>::new(self.size).unwrap();
        let srs = self.srs.as_ref().unwrap();
        let scheme = KzgScheme::new(srs);

        let polys = [self.t_table.clone(), f_table.clone(), s_odd.to_vec()].map(|table| {
            let evals = Evaluations::from_vec_and_domain(table.to_vec(), domain);
            evals.interpolate()
        });

        let [t_poly, f_poly, s_odd_poly] = polys;
        let (s_even_poly, s_even_commitment) =
            generate_poly_commitment(s_even.clone(), domain, &scheme);

        let mut challenge_generator = ChallengeGenerator::with_digest(&[s_even_commitment]);
        let [beta, gamma] = challenge_generator.clone().generate_challenges();

        let acc =
            self.compute_accumulator(&self.t_table, &f_table, &s_even, &s_odd, beta, gamma);
        let mut acc_shifted = acc.clone();
        acc_shifted.rotate_left(1);
        let (acc_poly, acc_commitment) = generate_poly_commitment(acc, domain, &scheme);
        let acc_shifted_poly = Evaluations::from_vec_and_domain(acc_shifted, domain).interpolate();

        challenge_generator.digest(&acc_commitment);
        let [alpha, zeta] = challenge_generator.generate_challenges();

        let w = Fr::get_root_of_unity(self.size).unwrap();

        let quotient = self.quotient_polynomial(
            &t_poly,
            &f_poly,
            (&s_even_poly, &s_odd_poly),
            (&acc_poly, &acc_shifted_poly),
            [alpha, beta, gamma],
            w,
            &domain,
        );
        let quotient_commit = quotient.commit(&scheme);

        let (r_poly, opening_evals) = self.linearisation_poly(
            &t_poly,
            &f_poly,
            (&s_even_poly, &s_odd_poly),
            (&acc_poly, &acc_shifted_poly),
            &quotient,
            [alpha, beta, gamma, zeta],
            w,
            &domain,
        );


        let r_open = scheme.open(r_poly, zeta);
        assert_eq!(r_open.1.is_zero(), true);

        let opening_commitments: [PolyProof; 2] = [s_even_poly, acc_poly]
            .into_iter()
            .zip([s_even_commitment, acc_commitment])
            .map(|(poly, commitment)| {
                let opening = scheme.open(poly, zeta);
                PolyProof {
                    commitment,
                    opening,
                }
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        LookupProof {
            opening_commitments,
            quotient_commit,
            opening_evals,
            r_open,
        }
    }

    pub fn verify(&self, proof: LookupProof) -> bool {
        let LookupProof {
            opening_commitments,
            quotient_commit,
            opening_evals,
            r_open,
        } = proof;

        let [s_even_commitment, acc_commitment] = opening_commitments
            .iter()
            .map(|polyproof| polyproof.commitment)
            .collect::<Vec<KzgCommitment>>()
            .try_into()
            .unwrap();

        let domain = <GeneralEvaluationDomain<Fr>>::new(self.size).unwrap();

        let srs = self.srs.as_ref().unwrap();
        let scheme = KzgScheme::new(srs);
        let w = Fr::get_root_of_unity(self.size).unwrap();

        let mut challenge_generator = ChallengeGenerator::with_digest(&[s_even_commitment]);
        let [beta, gamma] = challenge_generator.clone().generate_challenges();

        challenge_generator.digest(&acc_commitment);
        let [alpha, zeta] = challenge_generator.generate_challenges();

        let t_poly = Evaluations::from_vec_and_domain(self.t_table.to_vec(), domain).interpolate();
        let t_w_poly = compute_f_xw(&t_poly, w);
        let t_evals = [t_poly, t_w_poly]
            .map(|poly| {
                poly.evaluate(&zeta)
            });
        
        let opening_evals: [Fr; 6] = [opening_evals.as_slice(), t_evals.as_slice()].concat().try_into().unwrap();

        let r_commitment = self.linearisation_commitment(
            [s_even_commitment, acc_commitment],
            opening_evals,
            quotient_commit,
            [alpha, beta, gamma, zeta],
            &domain
        );
        let open_valid = scheme.verify(&r_commitment, &r_open, zeta);
        open_valid && r_open.1.is_zero()

    }

    fn fill_table(&mut self, f_table: MultiSet) -> MultiSet {
        let mut f_table = f_table;

        self.t_table.sort();
        f_table.sort();

        let t_length = self.t_table.len();
        let f_length = f_table.len();
        let length = std::cmp::max(t_length, f_length);

        let size = repeat(())
            .scan(2_usize, |state, _| {
                let old = *state;
                *state = old * 2;
                Some(old)
            })
            .find(|size| size >= &length)
            .unwrap();

        let t_last = self.t_table[t_length - 1].clone();
        let f_last = f_table[f_length - 1].clone();

        self.t_table.resize(size, t_last);
        f_table.resize(size, f_last);
        self.size = size;
        
        let srs = Srs::random(size);
        self.srs = Some(srs);

        f_table
    }

    // generate s_even and s_odd
    fn generate_s(&self, f_table: MultiSet) -> (MultiSet, MultiSet) {
        let mut s_table = self.t_table.clone();
        s_table.extend(f_table.clone());
        s_table.sort();
        let mut s_even = MultiSet::new();
        let mut s_odd = MultiSet::new();

        for (index, value) in s_table.iter().enumerate() {
            if index % 2 == 0 {
                s_even.push(value.clone());
            } else {
                s_odd.push(value.clone());
            }
        }
        (s_even, s_odd)
    }

    fn compute_accumulator(
        &self,
        t: &MultiSet,
        f: &MultiSet,
        s_even: &MultiSet,
        s_odd: &MultiSet,
        beta: Fr,
        gamma: Fr,
    ) -> Vec<Fr> {
        let mut acc = vec![Fr::one()];
        let mut num = Fr::one();
        let mut den = Fr::one();

        for i in 0..self.size {
            // use modulo to wrap around(%)
            let numerator = (Fr::one() + beta)
                * (f[i] + gamma)
                * (t[i] + beta * t[(i + 1) % self.size] + gamma * (Fr::one() + beta));
            num *= numerator;

            let de1 = s_even[i] + beta * s_odd[i] + gamma * (Fr::one() + beta);
            let de2 = s_odd[i] + beta * s_even[(i + 1) % self.size] + gamma * (Fr::one() + beta);
            let denominator = de1 * de2;
            den *= denominator;

            acc.push(num / den);
        }

        assert!(acc[acc.len() - 1] == Fr::one(), "Accumulator is wrong!");
        // pop acc(x*w) item
        acc.pop();
        acc
    }

    fn quotient_polynomial(
        &self,
        t: &Poly,
        f: &Poly,
        // s_even and s_odd
        s: (&Poly, &Poly),
        // Z and Zw
        acc: (&Poly, &Poly),
        // challenges alpha, beta, gamma
        challenges: [Fr; 3],
        w: Fr,
        domain: &GeneralEvaluationDomain<Fr>,
    ) -> SlicedPoly<3> {
        let (s_even, s_odd) = s;
        let (z, z_w) = acc;
        let [alpha, beta, gamma] = challenges;

        let t_w = compute_f_xw(t, w);
        let s_even_w = compute_f_xw(s_even, w);

        let line1 = {
            let mut f_add_gamma = f.clone();
            f_add_gamma = add_to_poly(f_add_gamma, gamma);
            let g3_1 = f_add_gamma.mul(Fr::one() + beta);
            let beta_t_w = t_w.mul(beta);
            let g3_2 = add_to_poly(&beta_t_w + t, gamma * (Fr::one() + beta));
            let g3 = g3_1.naive_mul(&g3_2);

            let beta_s_odd = s_odd.mul(beta);
            let beta_s_even_w = s_even_w.mul(beta);
            let g4_1 = s_even.clone() + add_to_poly(beta_s_odd, gamma * (Fr::one() + beta));
            let g4_2 = s_odd.clone() + add_to_poly(beta_s_even_w, gamma * (Fr::one() + beta));
            let g4 = g4_1.naive_mul(&g4_2);

            &z_w.naive_mul(&g4) - &z.naive_mul(&g3)
        };
        assert_eq!(line1.evaluate(&w), Fr::zero());

        let line2 = {
            let l0 = l0_poly(*domain);
            let mut z = z.clone();
            z.coeffs[0] -= Fr::one();
            z.naive_mul(&l0)
        };
        vanishes(&line2, *domain);

        let combination_element = [Fr::one(), alpha];
        let constrains = [line1, line2];
        let sum_poly = constrains
            .into_iter()
            .zip(combination_element.into_iter())
            .map(|(constrain, elem)| constrain.mul(elem))
            .reduce(Add::add)
            .unwrap();
        vanishes(&sum_poly, *domain);

        let (q_x, _) = sum_poly.divide_by_vanishing_poly(*domain).unwrap();
        SlicedPoly::from_poly(q_x, domain.size())
    }

    fn linearisation_poly(
        &self,
        t: &Poly,
        f: &Poly,
        // s_even and s_odd
        s: (&Poly, &Poly),
        // Z and Zw
        acc: (&Poly, &Poly),
        q: &SlicedPoly<3>,
        // challenges alpha, beta, gamma, zeta
        challenges: [Fr; 4],
        w: Fr,
        domain: &GeneralEvaluationDomain<Fr>,
    ) -> (Poly, [Fr; 4]) {
        let (s_even, s_odd) = s;
        let (z, z_w) = acc;
        let [alpha, beta, gamma, zeta] = challenges;

        let t_w = compute_f_xw(t, w);
        let s_even_w = compute_f_xw(s_even, w);

        let open_evals = [f, t, &t_w, s_odd, &s_even_w, z_w].map(|poly| poly.evaluate(&zeta));

        let [f_eval, t_eval, t_w_eval, s_odd_eval, s_even_w_eval, z_w_eval] = open_evals;

        let line1 = {
            let g3_eval = ((Fr::one() + beta) * (f_eval + gamma))
                * (t_eval + beta * t_w_eval + gamma * (Fr::one() + beta));

            let g4_1 = add_to_poly(
                s_even.clone(),
                beta * s_odd_eval + gamma * (Fr::one() + beta),
            );
            let g4_2 = s_odd_eval + beta * s_even_w_eval + gamma * (Fr::one() + beta);
            let g4 = g4_1.mul(g4_2);

            &g4.mul(z_w_eval) - &z.mul(g3_eval)
        };

        let line2 = {
            let l0 = l0_poly(*domain);
            let l0_eval = l0.evaluate(&zeta);
            let mut z = z.clone();
            z.coeffs[0] -= Fr::one();
            z.mul(l0_eval)
        };
        assert_eq!(line2.evaluate(&Fr::one()), Fr::zero());

        let line3 = q
            .compact(zeta)
            .mul(domain.evaluate_vanishing_polynomial(zeta));

        let r = &(line1 + line2.mul(alpha)) - &line3;
        let opening_evals = [f_eval, z_w_eval, s_odd_eval, s_even_w_eval];
        (r, opening_evals)
    }

    fn linearisation_commitment(
        &self,
        commitments: [KzgCommitment; 2],
        opening_evals: [Fr; 6],
        quotient_commit: [KzgCommitment; 3],
        challenges: [Fr; 4],
        domain: &GeneralEvaluationDomain<Fr>,
    ) -> KzgCommitment {
        let [f_eval, z_w_eval, s_odd_eval, s_even_w_eval, t_eval, t_w_eval] = opening_evals;
        let [s_even_commitment, acc_commitment] = commitments;
        let [alpha, beta, gamma, zeta] = challenges;

        let line1 = {
            let g3_eval = ((Fr::one() + beta) * (f_eval + gamma))
                * (t_eval + beta * t_w_eval + gamma * (Fr::one() + beta));
            let g4_1 = s_even_commitment + beta * s_odd_eval + gamma * (Fr::one() + beta);
            let g4_2 = s_odd_eval + beta * s_even_w_eval + gamma * (Fr::one() + beta);
            let g4 = g4_1.mul(g4_2);
            g4.mul(z_w_eval) - acc_commitment.mul(g3_eval)
        };

        let line2 = {
            let l0 = l0_poly(*domain);
            let l0_eval = l0.evaluate(&zeta);
            let z = acc_commitment + -Fr::one();
            z.mul(l0_eval)
        };

        let quotient = <SlicedPoly<3>>::compact_commitment(self.size, quotient_commit, zeta);
        let vanish_eval = domain.evaluate_vanishing_polynomial(zeta);
        let line3 = quotient * vanish_eval;

        let r = line1 + line2.mul(alpha) + -line3;
        r
    }
}

fn generate_poly_commitment(
    evals: Vec<Fr>,
    domain: GeneralEvaluationDomain<Fr>,
    scheme: &KzgScheme,
) -> (DensePolynomial<Fr>, KzgCommitment) {
    let poly = Evaluations::from_vec_and_domain(evals, domain).interpolate();
    let commitment = scheme.commit(&poly);
    (poly, commitment)
}

fn compute_f_xw(poly: &Poly, w: Fr) -> Poly {
    // f(x) = a_0+a_1x+a_2x^2+...+a_nx^n -> coeffs: [a_0, a_1, a_2, ..., a_n]
    let mut new_coeffs = poly.coeffs.clone();
    let mut power_of_w = Fr::one();

    // f(xw) = a_0+a_1xw+a_2x^2w^2+...+a_nx^nw^n -> coeffs: [a_0*1, a_1*w, a_2*w^2, ..., a_n*w^n]
    for coeffs in &mut new_coeffs {
        *coeffs *= power_of_w;
        power_of_w *= w;
    }

    DensePolynomial::from_coefficients_vec(new_coeffs)
}

// implment test
#[cfg(test)]
mod tests {
    use std::vec;

    use super::*;

    #[test]
    fn test_lookup_table() {
        let mut table = LookupTable::new(vec![2, 3, 4]);
        let mut f_table = FTable::new();
        f_table.add_table(vec![2, 3, 4]);

        let proof = table.prove(f_table);
        table.verify(proof);
    }
}
