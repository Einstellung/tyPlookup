use ark_bls12_381::Fr;
use ark_ff::{One, Zero};
use ark_poly::{EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial};
use kgz::{KzgCommitment, KzgScheme};
use std::{
    collections::{HashMap, HashSet},
    mem::swap,
};

pub mod proving;

#[derive(Hash, Debug, PartialEq, Eq, Clone, Copy)]
pub struct Tag {
    pub i: usize,
    pub j: usize,
}
impl Tag {
    fn to_index(&self, rows: &usize) -> usize {
        self.j + self.i * rows
    }
    fn from_index(index: &usize, rows: &usize) -> Self {
        let i = index / rows;
        let j = index % rows;
        Tag { i, j }
    }
}
#[derive(Default, Debug)]
pub struct PermutationBuilder<const C: usize> {
    //(i,j)
    constrains: HashMap<Tag, Vec<Tag>>,
    rows: usize,
}

impl<const C: usize> PermutationBuilder<C> {
    pub fn add_row(&mut self) {
        self.rows += 1;
    }
    pub fn with_rows(rows: usize) -> Self {
        let mut new = Self::default();
        new.rows = rows;
        new
    }
    ///checks if a tag is valid
    fn check_tag(&self, tag: &Tag) -> bool {
        let Tag { i, j } = tag;
        i <= &C && j < &self.rows
    }
    pub fn add_constrain(&mut self, left: Tag, right: Tag) -> Result<(), ()> {
        if !(self.check_tag(&left) && self.check_tag(&right)) {
            Err(())
        } else {
            let cell = self.constrains.entry(left).or_insert(Vec::with_capacity(8));
            cell.push(right);
            Ok(())
        }
    }
    pub fn add_constrains(&mut self, constrains: Vec<(Tag, Tag)>) {
        for (left, right) in constrains {
            self.add_constrain(left, right).unwrap();
        }
    }
    pub fn build(&mut self, size: usize) -> Permutation<C> {
        let len = size * C;
        let mut mapping = (0..len).collect::<Vec<_>>();
        let mut aux = (0..len).collect::<Vec<_>>();
        let mut sizes = std::iter::repeat(1).take(len).collect::<Vec<_>>();
        let constrains = std::mem::take(&mut self.constrains);
        for (left, rights) in constrains.into_iter() {
            let mut left = left.to_index(&size);
            for right in rights {
                let mut right = right.to_index(&size);
                if aux[left] == aux[right] {
                    continue;
                }
                if sizes[aux[left]] < sizes[aux[right]] {
                    swap(&mut left, &mut right);
                }
                sizes[aux[left]] += sizes[aux[right]];
                //step 4
                let mut next = right;
                let aux_left = aux[left];
                loop {
                    aux[next] = aux_left;
                    next = mapping[next];
                    if aux[next] == aux_left {
                        break;
                    }
                }
                mapping.swap(left, right);
            }
        }
        Permutation { perm: mapping }
    }
}
#[derive(Debug)]
pub struct Permutation<const C: usize> {
    perm: Vec<usize>,
}

impl<const C: usize> Permutation<C> {
    pub fn compile(self) -> CompiledPermutation<C> {
        assert_eq!(self.perm.len() % C, 0);
        let rows = self.perm.len() / C;
        let cols = self.perm.chunks(rows);
        let cosets = Self::cosets(rows);
        let domain = <GeneralEvaluationDomain<Fr>>::new(rows).unwrap();
        let roots = domain.elements().collect::<Vec<_>>();
        let perm = cols.enumerate().map(|(i, col)| {
            let coefficients = col
                .iter()
                .enumerate()
                .map(|(j, index)| {
                    let tag = Tag::from_index(index, &rows);
                    let value = cosets[tag.i] * roots[tag.j];
                    let tag = cosets[i] * roots[j];
                    (tag, value)
                })
                .collect();
            coefficients
            //let poly = DensePolynomial::from_coefficients_vec(coefficients);
            //poly
        });
        let mut cols: [Vec<(Fr, Fr)>; C] = [0_u8; C].map(|_| Default::default());
        for (i, col) in perm.enumerate() {
            cols[i] = col;
        }
        CompiledPermutation { cols, cosets, rows }
    }
    pub fn print(&self) {
        println!("len: {}", self.perm.len());
        let rows = self.perm.len() / C;
        let perm = &self.perm;
        for j in 0..rows {
            let mut row = vec![];
            for i in 0..C {
                row.push(perm[j + i * rows]);
            }
            println!("{:?}", row);
        }
    }
    fn cosets(gates: usize) -> [Fr; C] {
        let domain = <GeneralEvaluationDomain<Fr>>::new(gates).unwrap();
        let mut cosets = [Fr::zero(); C];

        let mut k = Fr::one();
        for coset in cosets.iter_mut() {
            while domain.evaluate_vanishing_polynomial(k).is_zero() {
                k += Fr::from(1);
            }
            *coset = k;
            k += Fr::from(1);
        }
        cosets
    }
}
#[derive(Debug)]
pub struct CompiledPermutation<const C: usize> {
    //cols: Vec<Vec<(Fr, Fr)>>,
    pub cols: [Vec<(Fr, Fr)>; C],
    pub cosets: [Fr; C],
    rows: usize,
}

impl<const C: usize> CompiledPermutation<C> {
    pub fn sigma_evals(&self, point: &Fr, domain: GeneralEvaluationDomain<Fr>) -> [Fr; C] {
        self.cols
            .iter()
            .map(|col| {
                let evals = col.iter().map(|cell| cell.1).collect();
                let eval = <Evaluations<Fr>>::from_vec_and_domain(evals, domain);
                let poly = eval.interpolate();
                poly.evaluate(point)
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }
    pub fn sigma_commitments(
        &self,
        scheme: &KzgScheme,
        domain: GeneralEvaluationDomain<Fr>,
    ) -> [KzgCommitment; C] {
        self.cols
            .iter()
            .map(|col| {
                let evals = col.iter().map(|cell| cell.1).collect();
                let eval = <Evaluations<Fr>>::from_vec_and_domain(evals, domain);
                let poly = eval.interpolate();
                scheme.commit(&poly)
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }
}

#[allow(dead_code)]
fn print_matrix(matrix: &[usize], cols: usize) {
    println!();
    for row in matrix.chunks(cols) {
        println!("{:?}", row);
    }
}

#[allow(dead_code)]
fn print_cycle(elems: &[usize]) {
    let mut seen = HashSet::new();
    for elem in elems {
        if seen.contains(elem) {
            continue;
        } else {
            seen.insert(*elem);
            let mut cycle = vec![*elem];
            let mut next = elems[*elem];
            loop {
                if seen.contains(&next) {
                    break;
                }
                seen.insert(next);
                cycle.push(next);
                next = elems[next];
            }
            println!("{:?}", cycle);
        }
    }
}
