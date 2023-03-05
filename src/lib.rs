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

    pub fn prove<R: Rng>(rng: &mut R, p: &P) -> (Vec<F>, Vec<F>, [F; 2]) {
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

            // commit to f_{i+1}(x) = fL_i(x) + alpha_i * fR_i(x)
            let (cm_i, mt_i) = MT::commit(f_i1.coeffs());
            commitments.push(cm_i);
            mts.push(mt_i);
        }
        let (fL_i, fR_i) = Self::split(&f_i1);
        let constant_fL_l: F = fL_i.coeffs()[0].clone();
        let constant_fR_l: F = fR_i.coeffs()[0].clone();

        // TODO this will be a hash from the transcript
        // V sets rand z \in \mathbb{F} challenge
        let z = F::from(10_u64);

        let mut evals: Vec<F> = Vec::new();
        // TODO this will be done inside the prev loop, now it is here just for clarity
        // evaluate f_i(z^{2^i})
        for i in 0..f_is.len() {
            // TODO check usage of .pow(u64)
            let z_2i = z.pow([2_u64.pow(i as u32)]); // z^{2^i}
            let neg_z_2i = z_2i.neg();
            let eval_i = f_is[i].evaluate(&z_2i);
            evals.push(eval_i);
            let eval_i = f_is[i].evaluate(&neg_z_2i);
            evals.push(eval_i);
        }

        // TODO return also the commitment_proofs
        // return: Comm(f_i(x)), f_i(+-z^{2^i}), constant values {f_l^L, f_l^R}
        (commitments, evals, [constant_fL_l, constant_fR_l])
    }

    pub fn verify(commitments: Vec<F>, evals: Vec<F>, constants: [F; 2]) -> bool {
        let z = F::from(10_u64); // TODO this will be a hash from the transcript

        // TODO check commitments.len()==evals.len()/2

        for i in (0..evals.len()).step_by(2) {
            let alpha_i = F::from(3_u64); // TODO: WIP, defined by Verifier (well, hash transcript)

            let z_2i = z.pow([2_u64.pow((i as u32) / 2)]); // z^{2^i}
                                                           // take f_i(z^2) from evals
            let fi_z = evals[i];
            let neg_fi_z = evals[i + 1];
            // compute f_i^L(z^2), f_i^R(z^2) from the linear combination
            let L = (fi_z + neg_fi_z) * F::from(2_u32).inverse().unwrap();
            let R = (fi_z - neg_fi_z) * (F::from(2_u32) * z_2i).inverse().unwrap();

            // compute f_{i+1}(z^2) = f_i^L(z^2) + a_i f_i^R(z^2)
            let next_fi_z2 = L + alpha_i * R;

            // check: obtained f_{i+1}(z^2) == evals.f_{i+1}(z^2) (=evals[i+2])
            if i < evals.len() - 2 {
                if next_fi_z2 != evals[i + 2] {
                    println!("\nerr, i={:?}", i);
                    println!("  next_fi^z2 {:?}", next_fi_z2.to_string());
                    println!("  e[i] {:?}", evals[i + 2].to_string());
                    panic!("should f_i+1(z^2) == evals.f_i+1(z^2) (=evals[i+2])");
                }
            }

            // check commitment opening
            // TODO

            // last iteration, check constant values equal to the obtained f_i^L(z^{2^i}),
            // f_i^R(z^{2^i})
            if i == evals.len() - 2 {
                if L != constants[0] {
                    panic!("constant L not equal");
                }
                if R != constants[1] {
                    println!("R {:?}\n  {:?}", R.to_string(), constants[1].to_string());
                    panic!("constant R not equal");
                }
            }
        }

        true
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

    #[test]
    fn test_prove() {
        let mut rng = ark_std::test_rng();

        let deg = 15;
        let p = DensePolynomial::<Fr>::rand(deg, &mut rng);
        assert_eq!(p.degree(), deg);
        // println!("p {:?}", p);

        type FRIC = FRI<Fr, DensePolynomial<Fr>>;
        // prover
        let (commitments, evals, constvals) = FRIC::prove(&mut rng, &p);
        // commitments contains the commitments to each f_0, f_1, ..., f_n, with n=log2(d)
        assert_eq!(commitments.len(), log2(p.coeffs().len()) as usize - 1);
        assert_eq!(evals.len(), 2 * log2(p.coeffs().len()) as usize);

        let v = FRIC::verify(commitments, evals, constvals);
        assert!(v);
    }
}
