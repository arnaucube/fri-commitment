#![allow(non_snake_case)]

pub mod merkletree;
use merkletree::{MerkleTreePoseidon as MT, Params as MTParams};

use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, UVPolynomial};
use ark_std::log2;
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;
use ark_std::{rand::Rng, UniformRand};

pub struct FRI<F: PrimeField, P: UVPolynomial<F>> {
    _f: PhantomData<F>,
    _poly: PhantomData<P>,
}

impl<F: PrimeField, P: UVPolynomial<F>> FRI<F, P> {
    pub fn new() -> Self {
        Self {
            _f: PhantomData,
            _poly: PhantomData,
        }
    }

    pub fn split(p: &P) -> (P, P) {
        // let d = p.degree() + 1;
        let d = p.coeffs().len();
        if (d != 0) && (d & (d - 1) != 0) {
            println!("d={:?}", d);
            panic!("d should be a power of 2");
        }

        let coeffs = p.coeffs();
        let odd: Vec<F> = coeffs.iter().step_by(2).cloned().collect();
        let even: Vec<F> = coeffs.iter().skip(1).step_by(2).cloned().collect();

        return (
            P::from_coefficients_vec(odd),
            P::from_coefficients_vec(even),
        );
    }

    pub fn prove<R: Rng>(rng: &mut R, p: &P) -> (Vec<F>, [F; 2]) {
        // f_0(x) = fL_0(x^2) + x fR_0(x^2)
        let mut f_i1 = p.clone();

        // TODO challenge a_0
        let mut f_is: Vec<P> = Vec::new();
        f_is.push(p.clone());
        let mut commitments: Vec<F> = Vec::new();
        let mut mts: Vec<MT<F>> = Vec::new();
        while f_i1.degree() > 1 {
            let alpha_i = F::from(3_u64); // TODO: WIP, defined by Verifier (well, hash transcript)

            let (fL_i, fR_i) = Self::split(&f_i1);

            // compute f_{i+1}(x) = fL_i(x) + alpha_i * fR_i(x)
            let aux = DensePolynomial::from_coefficients_slice(fR_i.coeffs());
            f_i1 = fL_i.clone() + P::from_coefficients_slice(aux.mul(alpha_i).coeffs());
            f_is.push(f_i1.clone());
        }
        let (fL_i, fR_i) = Self::split(&f_i1);
        let constant_fL_l: F = fL_i.coeffs()[0].clone();
        let constant_fR_l: F = fR_i.coeffs()[0].clone();

        // TODO evaluate f_i(z^{2^i})
        let evals: Vec<F> = Vec::new();

        (evals, [constant_fL_l, constant_fR_l])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;
    use ark_std::UniformRand;
    pub type Fr = ark_bn254::Fr; // scalar field
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::Polynomial;

    #[test]
    fn test_split() {
        let mut rng = ark_std::test_rng();
        let deg = 7;
        let p = DensePolynomial::<Fr>::rand(deg, &mut rng);
        assert_eq!(p.degree(), deg);

        type FRIC = FRI<Fr, DensePolynomial<Fr>>;
        let (pL, pR) = FRIC::split(&p);

        // check that f(z) == fL(x^2) + x * fR(x^2), for a rand z
        let z = Fr::rand(&mut rng);
        assert_eq!(
            p.evaluate(&z),
            pL.evaluate(&z.square()) + z * pR.evaluate(&z.square())
        );
    }
}
