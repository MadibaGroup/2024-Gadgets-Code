use std::ops::Mul;

use ark_ec::{pairing::Pairing, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField, Zero};
use ark_poly::{univariate::DensePolynomial, Polynomial, DenseUVPolynomial};
use ark_poly_commit::kzg10::{Commitment, Powers, Randomness, VerifierKey, KZG10};
use ark_std::{rand::RngCore, UniformRand};

use num_bigint::BigUint;

use sha2::{Digest, Sha256};

#[derive(Debug)]
pub struct HashBox<E: Pairing> {
    pub object: E::G1Affine,
}

pub fn calculate_hash<E: Pairing>(objects: &Vec<HashBox<E>>) -> E::ScalarField {
    let mut hasher = Sha256::default();
    let mut msg: String = "".to_owned();
    for obj in objects {
        msg.push_str(&format!("{:?}", obj));
    }
    hasher.update(msg);
    let digest = hasher.finalize();
    let num = BigUint::from_bytes_le(&digest);
    E::ScalarField::from(num)
}

pub enum OpenEval<E: Pairing> {
    Plain(E::ScalarField, E::ScalarField),
    Committed(E::G1Affine),
}

impl<E> OpenEval<E> where E: Pairing {
    pub fn into_committed_value(&self) -> E::G1Affine {
        if let OpenEval::Committed(value) = self {
            *value
        } else {
            panic!("Not a committed value")
        }
    }

    pub fn into_plain_value(&self) -> (E::ScalarField, E::ScalarField) {
        if let OpenEval::Plain(value, r) = self {
            (*value, *r)
        } else {
            panic!("Not a plain value")
        }
    } 
}

// the batched KZG opening scheme in [GWC19]
#[inline]
pub fn batch_open<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    polys: &Vec<&DensePolynomial<E::ScalarField>>,
    randoms: &Vec<&Randomness<E::ScalarField, DensePolynomial<E::ScalarField>>>,
    point: E::ScalarField,
    hiding_evals: bool,
    rng: &mut R,
) -> (E::G1, Vec<OpenEval<E>>, E::ScalarField) {
    assert!(polys.len() == randoms.len());
    let gamma = E::ScalarField::rand(rng);
    let mut w = DensePolynomial::<E::ScalarField>::zero();
    let mut rand_h = DensePolynomial::<E::ScalarField>::zero();
    let mut plain_evals = Vec::<(E::ScalarField, E::ScalarField)>::new();
    let mut committed_evals = Vec::<E::G1Affine>::new();
    let mut i = 0u64;
    for (p, random) in polys.into_iter().zip(randoms) {
        let eval = p.evaluate(&point);
        let blinding_eval = random.blinding_polynomial.evaluate(&point);

        let (witness, random_witness) =
            KZG10::<E, DensePolynomial<E::ScalarField>>::compute_witness_polynomial(&p, point, &random).unwrap();

        let factor = gamma.pow(&[i]);
        w = w + witness.mul(factor);
        rand_h = rand_h + random_witness.unwrap().mul(factor);

        i += 1;

        let committed_eval = powers.powers_of_g[0].mul(eval) + powers.powers_of_gamma_g[0].mul(blinding_eval);

        plain_evals.push((eval, blinding_eval));
        committed_evals.push(committed_eval.into_affine());
    }

    let (num_leading_zeros, witness_coeffs) =
            skip_leading_zeros_and_convert_to_bigints(&w);

    let mut h = E::G1::msm_bigint(
        &powers.powers_of_g[num_leading_zeros..],
        witness_coeffs.as_slice(),
    );
    let random_witness_coeffs = convert_to_bigints(&rand_h.coeffs());
    h += &<E::G1 as VariableBaseMSM>::msm_bigint(
        &powers.powers_of_gamma_g,
        random_witness_coeffs.as_slice(),
    );

    let open_evals: Vec<OpenEval<E>> = match hiding_evals {
        true => committed_evals.into_iter().map(| eval | OpenEval::Committed(eval)).collect(),
        false => plain_evals.into_iter().map(| (eval, blind) | OpenEval::Plain(eval, blind)).collect(),
    };
    (h, open_evals, gamma)
}

pub struct BatchCheckProof<E: Pairing> {
    pub commitments: Vec<Vec<Commitment<E>>>,
    pub witnesses: Vec<E::G1>,
    pub points: Vec<E::ScalarField>,
    pub open_evals: Vec<Vec<OpenEval<E>>>,
    pub gammas: Vec<E::ScalarField>,
}

// the batched KZG opening scheme in [GWC19]
pub fn batch_check<E: Pairing, R: RngCore>(
    vk: &VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    rng: &mut R,
) {
    let BatchCheckProof { commitments, witnesses, points, open_evals, gammas } = proof;
    assert!(&points.len() == &open_evals.len() && &points.len() == &witnesses.len() && &gammas.len() == &points.len());
    let mut left = E::G1::zero();
    let mut right = E::G1::zero();
    let mut i: usize = 0;
    let r = E::ScalarField::rand(rng);
    for gamma in gammas {
        let cms = &commitments[i];
        let evals = &open_evals[i];
        assert_eq!(&cms.len(), &evals.len());
        let mut j = 0u64;
        let mut sum_cm = E::G1::zero();
        let mut sum_committed_eval = E::G1::zero();
        let mut sum_value = E::ScalarField::zero();
        let mut sum_blinding = E::ScalarField::zero();
        for (cm, eval) in cms.into_iter().zip(evals) {
            let factor = gamma.pow(&[j]);
            sum_cm += cm.0.mul(factor);
            match eval {
                OpenEval::Plain(value, blinding) => {
                    sum_value += value.mul(factor);
                    sum_blinding += blinding.mul(factor);
                }
                OpenEval::Committed(committed_eval) => sum_committed_eval += committed_eval.mul(factor)
            };
            j += 1;
        }
        sum_committed_eval += vk.g.mul(sum_value) + vk.gamma_g.mul(sum_blinding);
        let factor = r.pow(&[i as u64]);
        left += (sum_cm - sum_committed_eval).mul(factor);
        let witness = witnesses[i];
        let point = points[i];
        let r_times_w = witness.mul(factor);
        left += r_times_w.mul(point);
        right += r_times_w;
        i += 1;
    }
    let lhs = E::pairing(left, vk.h);
    let rhs = E::pairing(right, vk.beta_h);
    assert_eq!(lhs, rhs);
}

#[inline]
pub fn skip_leading_zeros_and_convert_to_bigints<F: PrimeField, P: DenseUVPolynomial<F>>(
    p: &P,
) -> (usize, Vec<F::BigInt>) {
    let mut num_leading_zeros = 0;
    while num_leading_zeros < p.coeffs().len() && p.coeffs()[num_leading_zeros].is_zero() {
        num_leading_zeros += 1;
    }
    let coeffs = convert_to_bigints(&p.coeffs()[num_leading_zeros..]);
    (num_leading_zeros, coeffs)
}

#[inline]
pub fn convert_to_bigints<F: PrimeField>(p: &[F]) -> Vec<F::BigInt> {
    let coeffs = ark_std::cfg_iter!(p)
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>();
    coeffs
}
