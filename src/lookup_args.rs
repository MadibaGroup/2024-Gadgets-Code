use std::collections::BTreeMap;
use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_poly::{univariate::DensePolynomial, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
use ark_std::{iterable::Iterable, rand::RngCore};

use crate::{permutation_check, utils::{batch_open, calculate_hash, BatchCheckProof, HashBox}};

/// [unoptimized] the lookup argument in halo2
pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    a_evals: &Vec<u64>,
    s_evals: &Vec<u64>,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> Vec<BatchCheckProof<E>> {
    let (a_prime_evals, s_prime_evals) = sort(a_evals, s_evals);
    let a_evals: Vec<_> = a_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let s_evals: Vec<_> = s_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let a_prime_evals: Vec<_> = a_prime_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let s_prime_evals: Vec<_> = s_prime_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();

    // prove A^prime is the permutation of A
    let perm_proof1 = permutation_check::prove(powers, &a_evals, &a_prime_evals, domain, rng);
    // prove S^prime is the permutation of S
    let perm_proof2 = permutation_check::prove(powers, &s_evals, &s_prime_evals, domain, rng);

    vec![perm_proof1, perm_proof2]
}

pub fn verify<E: Pairing, R: RngCore>(
    vk: &VerifierKey<E>,
    proofs: &Vec<BatchCheckProof<E>>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) {
    for proof in proofs {
        permutation_check::verify(vk, proof, domain, rng);
    }
}

fn sort(
    a_evals: &Vec<u64>,
    s_evals: &Vec<u64>,
) -> (Vec<u64>, Vec<u64>) {
    // convert S from an array into a map
    let s_map: Vec<(u64, usize)> = s_evals.iter()
        .map(| val | {
            (*val, 1)
        })
        .collect();
    let mut s_map = BTreeMap::from_iter(s_map);

    // construct A^prime by copying A and sort A^prime
    let mut a_prime_evals = a_evals.clone();
    a_prime_evals.sort();

    // initialize S^prime by filling it with 0
    let mut s_prime_evals= Vec::<u64>::with_capacity(s_evals.len());
    for _ in 0..s_evals.len() { s_prime_evals.push(0); }

    let mut repeated_evals = vec![];

    // S^prime[0] = A^prime[0]
    s_prime_evals[0] = a_prime_evals[0];
    let x = s_map.get_mut(&a_prime_evals[0]).unwrap();
    *x -= 1;

    for i in 1..a_prime_evals.len() {
        let prev = a_prime_evals[i - 1];
        let cur = a_prime_evals[i];
        if prev == cur { 
            // when the current element is equal to the previous one, record the index and dont update S^prime
            repeated_evals.push(i);
        } else {
            // when the current element is different from the previous one, update S^prime and decrease the count
            s_prime_evals[i] = cur;
            let x = s_map.get_mut(&cur).unwrap();
            *x -= 1;
        }
    }

    for (val, count) in s_map {
        // fill S^prime with the elements not queried in the map
        if count == 1 {
            if let Some(idx) = repeated_evals.pop() {
                s_prime_evals[idx] = val;
            }
        }
    }

    (a_prime_evals, s_prime_evals)
}
