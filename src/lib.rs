#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

pub mod merkletree;
use merkletree::{Hash, MerkleTree};
pub mod transcript;
use transcript::Transcript;

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
};

use ark_std::cfg_into_iter;
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;

// rho^-1
const rho1: usize = 8; // WIP

pub struct FRI_LDT<F: PrimeField, P: DenseUVPolynomial<F>, H: Hash<F>> {
    _f: PhantomData<F>,
    _poly: PhantomData<P>,
    _h: PhantomData<H>,
}

impl<F: PrimeField, P: DenseUVPolynomial<F>, H: Hash<F>> FRI_LDT<F, P, H> {
    pub fn new() -> Self {
        Self {
            _f: PhantomData,
            _poly: PhantomData,
            _h: PhantomData,
        }
    }

    fn split(p: &P) -> (P, P) {
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

    // prove implements the proof generation for a FRI-low-degree-testing
    pub fn prove(p: &P) -> (Vec<F>, Vec<Vec<F>>, Vec<F>, [F; 2]) {
        // init transcript
        let mut transcript: Transcript<F> = Transcript::<F>::new();

        let d = p.degree();
        let mut commitments: Vec<F> = Vec::new();
        let mut mts: Vec<MerkleTree<F, H>> = Vec::new();

        // f_0(x) = fL_0(x^2) + x fR_0(x^2)
        let mut f_i1 = p.clone();

        // sub_order = |F_i| = rho^-1 * d
        let mut sub_order = d * rho1; // TMP, TODO this will depend on rho parameter
        let mut eval_sub_domain: GeneralEvaluationDomain<F> =
            GeneralEvaluationDomain::new(sub_order).unwrap();

        // V sets rand z \in \mathbb{F} challenge
        let (z_pos, z) = transcript.get_challenge_in_eval_domain(eval_sub_domain, b"get z");

        let mut f_is: Vec<P> = Vec::new();
        // evals = {f_i(z^{2^i}), f_i(-z^{2^i})} \forall i \in F_i
        let mut evals: Vec<F> = Vec::new();
        let mut mtproofs: Vec<Vec<F>> = Vec::new();
        let mut fL_i: P = P::from_coefficients_vec(Vec::new());
        let mut fR_i: P = P::from_coefficients_vec(Vec::new());
        let mut i = 0;
        while f_i1.degree() >= 1 {
            f_is.push(f_i1.clone());
            let alpha_i = transcript.get_challenge(b"get alpha_i");

            let subdomain_evaluations: Vec<F> = cfg_into_iter!(0..eval_sub_domain.size())
                .map(|k| f_i1.evaluate(&eval_sub_domain.element(k)))
                .collect();

            // commit to f_{i+1}(x) = fL_i(x) + alpha_i * fR_i(x), commit to the evaluation domain
            let (cm_i, mt_i) = MerkleTree::<F, H>::commit(&subdomain_evaluations);
            commitments.push(cm_i);
            mts.push(mt_i);
            transcript.add(b"root_i", &cm_i);

            // evaluate f_i(z^{2^i}), f_i(-z^{2^i}), and open their commitment
            let z_2i = z.pow([2_u64.pow(i as u32)]); // z^{2^i} // TODO check usage of .pow(u64)
            let neg_z_2i = z_2i.neg();
            let eval_i = f_i1.evaluate(&z_2i);
            evals.push(eval_i);
            transcript.add(b"f_i(z^{2^i})", &eval_i);
            let eval_i = f_i1.evaluate(&neg_z_2i);
            evals.push(eval_i);
            transcript.add(b"f_i(-z^{2^i})", &eval_i);

            // gen the openings in the commitment to f_i(z^(2^i))
            let mtproof = mts[i].open(F::from(z_pos as u32));
            mtproofs.push(mtproof);

            (fL_i, fR_i) = Self::split(&f_i1);

            // compute f_{i+1}(x) = fL_i(x) + alpha_i * fR_i(x)
            let aux = DensePolynomial::from_coefficients_slice(fR_i.coeffs());
            f_i1 = fL_i.clone() + P::from_coefficients_slice(aux.mul(alpha_i).coeffs());

            // prepare next subdomain
            sub_order = sub_order / 2;
            eval_sub_domain = GeneralEvaluationDomain::new(sub_order).unwrap();

            i += 1;
        }
        if fL_i.coeffs().len() != 1 {
            panic!("fL_i not constant");
        }
        if fR_i.coeffs().len() != 1 {
            panic!("fR_i not constant");
        }
        let constant_fL_l: F = fL_i.coeffs()[0].clone();
        let constant_fR_l: F = fR_i.coeffs()[0].clone();

        (commitments, mtproofs, evals, [constant_fL_l, constant_fR_l])
    }

    // verify implements the verification of a FRI-low-degree-testing proof
    pub fn verify(
        degree: usize, // expected degree
        commitments: Vec<F>,
        mtproofs: Vec<Vec<F>>,
        evals: Vec<F>,
        constants: [F; 2],
    ) -> bool {
        // init transcript
        let mut transcript: Transcript<F> = Transcript::<F>::new();

        let sub_order = rho1 * degree; // TMP, TODO this will depend on rho parameter
        let eval_sub_domain: GeneralEvaluationDomain<F> =
            GeneralEvaluationDomain::new(sub_order).unwrap();

        let (z_pos, z) = transcript.get_challenge_in_eval_domain(eval_sub_domain, b"get z");

        if commitments.len() != (evals.len() / 2) {
            println!("sho commitments.len() != (evals.len() / 2) - 1");
            return false;
        }

        let mut i_z = 0;
        for i in (0..evals.len()).step_by(2) {
            let alpha_i = transcript.get_challenge(b"get alpha_i");

            // take f_i(z^2) from evals
            let z_2i = z.pow([2_u64.pow(i_z as u32)]); // z^{2^i}
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
                    println!(
                        "verify step i={}, should f_i+1(z^2) == evals.f_i+1(z^2) (=evals[i+2])",
                        i
                    );
                    return false;
                }
            }
            transcript.add(b"root_i", &commitments[i_z]);
            transcript.add(b"f_i(z^{2^i})", &evals[i]);
            transcript.add(b"f_i(-z^{2^i})", &evals[i + 1]);

            // check commitment opening
            if !MerkleTree::<F, H>::verify(
                commitments[i_z],
                F::from(z_pos as u32),
                evals[i],
                mtproofs[i_z].clone(),
            ) {
                println!("verify step i={}, MT::verify failed", i);
                return false;
            }

            // last iteration, check constant values equal to the obtained f_i^L(z^{2^i}),
            // f_i^R(z^{2^i})
            if i == evals.len() - 2 {
                if L != constants[0] {
                    println!("constant L not equal to the obtained one");
                    return false;
                }
                if R != constants[1] {
                    println!("constant R not equal to the obtained one");
                    return false;
                }
            }
            i_z += 1;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;
    use ark_std::UniformRand;
    // pub type Fr = ark_bn254::Fr; // scalar field
    use ark_bn254::Fr; // scalar field
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::Polynomial;
    use ark_std::log2;
    use merkletree::Keccak256Hash;

    #[test]
    fn test_split() {
        let mut rng = ark_std::test_rng();
        let deg = 7;
        let p = DensePolynomial::<Fr>::rand(deg, &mut rng);
        assert_eq!(p.degree(), deg);

        type FRID = FRI_LDT<Fr, DensePolynomial<Fr>, Keccak256Hash<Fr>>;
        let (pL, pR) = FRID::split(&p);

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

        let deg = 31;
        let p = DensePolynomial::<Fr>::rand(deg, &mut rng);
        assert_eq!(p.degree(), deg);
        // println!("p {:?}", p);

        type FRID = FRI_LDT<Fr, DensePolynomial<Fr>, Keccak256Hash<Fr>>;

        let (commitments, mtproofs, evals, constvals) = FRID::prove(&p);
        // commitments contains the commitments to each f_0, f_1, ..., f_n, with n=log2(d)
        assert_eq!(commitments.len(), log2(p.coeffs().len()) as usize);
        assert_eq!(evals.len(), 2 * log2(p.coeffs().len()) as usize);

        let v = FRID::verify(deg, commitments, mtproofs, evals, constvals);
        assert!(v);
    }
}
