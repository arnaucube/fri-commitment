# fri-commitment [![Test](https://github.com/arnaucube/fri-commitment/workflows/Test/badge.svg)](https://github.com/arnaucube/fri-commitment/actions?query=workflow%3ATest)

FRI low degree testing & FRI polynomial commitment using [[VP19]](https://eprint.iacr.org/2019/1020)'s trick. Implementation using arkworks libraries.

> *Note*: done in my free time to learn about FRI, do not use in production.


Thanks to [Vincenzo Iovino](https://sites.google.com/site/vincenzoiovinoit/) for explainations on [FRI](https://eccc.weizmann.ac.il/report/2017/134/) & [[VP19]](https://eprint.iacr.org/2019/1020).

## Usage

FRI-LDT:
```rust
type LDT = FRI_LDT<Fr, DensePolynomial<Fr>, Keccak256Hash<Fr>>;

let deg = 31;
let p = DensePolynomial::<Fr>::rand(deg, &mut ark_std::test_rng());

let proof = LDT::prove(&p);

let v = LDT::verify(proof, deg);
assert!(v);
```

FRI-PCS:
```rust
type PCS = FRI_PCS<Fr, DensePolynomial<Fr>, Keccak256Hash<Fr>>;

let deg = 31;
let mut rng = ark_std::test_rng();
let p = DensePolynomial::<Fr>::rand(deg, &mut rng);

let commitment = PCS::commit(&p);

let r = Fr::rand(&mut rng);

let (proof, claimed_y) = PCS::open(&p, r);

let v = PCS::verify(commitment, proof, r, claimed_y);
assert!(v);
```
