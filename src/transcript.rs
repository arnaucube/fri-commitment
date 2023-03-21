use ark_ff::PrimeField;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_serialize::CanonicalSerialize;
use merlin::Transcript as FSTranscript; // FS stands for Fiat-Shamir
use std::marker::PhantomData;

// This Transcript approach is a modified version from https://github.com/caulk-crypto/caulk ,
// using Merlin transcript (https://merlin.cool/).
pub struct Transcript<F: PrimeField> {
    phantom: PhantomData<F>,
    transcript: FSTranscript,
}

impl<F: PrimeField> Transcript<F> {
    pub fn new() -> Self {
        Self {
            phantom: PhantomData::default(),
            transcript: FSTranscript::new(b"FRI transcript"),
        }
    }
    pub fn add<T: CanonicalSerialize>(&mut self, label: &'static [u8], r: &T) {
        let mut buf = vec![];
        r.serialize_uncompressed(&mut buf).unwrap();
        self.transcript.append_message(label, buf.as_ref());
    }
    pub fn get_challenge(&mut self, label: &'static [u8]) -> F {
        let mut bytes = [0u8; 64];
        self.transcript.challenge_bytes(label, &mut bytes);
        let challenge = F::from_le_bytes_mod_order(bytes.as_ref());
        self.add(b"new challenge", &challenge);
        challenge
    }
    pub fn get_challenge_in_eval_domain(
        &mut self,
        eval_domain: GeneralEvaluationDomain<F>,
        label: &'static [u8],
    ) -> (usize, F) {
        let mut bytes = [0u8; 8];
        self.transcript.challenge_bytes(label, &mut bytes);
        let c: usize = usize::from_le_bytes(bytes);
        let size = eval_domain.size();
        let pos = c % size;
        let challenge = eval_domain.element(pos);
        self.add(b"new challenge", &challenge);
        (pos, challenge)
    }
}
