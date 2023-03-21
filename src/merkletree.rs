// merkletree.rs implements a simple binary insert-only merkletree in which the leafs positions is
// determined by the leaf value binary representation. Inspired by
// https://docs.iden3.io/publications/pdfs/Merkle-Tree.pdf (which can be found implemented in
// https://github.com/vocdoni/arbo).

use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalSerialize;
use ark_std::log2;
use ark_std::marker::PhantomData;
use sha3::{Digest, Keccak256};

// abstraction to set the hash function used
pub trait Hash<F>: Clone {
    fn hash(_in: &[F]) -> F;
}

#[derive(Clone, Copy, Debug)]
pub struct Keccak256Hash<F: PrimeField> {
    phantom: PhantomData<F>,
}
impl<F: PrimeField> Hash<F> for Keccak256Hash<F> {
    fn hash(_in: &[F]) -> F {
        let mut buf = vec![];
        _in.serialize_uncompressed(&mut buf).unwrap();

        let mut h = Keccak256::default();
        h.update(buf);
        let r = h.finalize();
        let out = F::from_le_bytes_mod_order(&r);
        out
    }
}

#[derive(Clone, Debug)]
pub struct Node<F: PrimeField, H: Hash<F>> {
    phantom: PhantomData<H>,
    hash: F,
    left: Option<Box<Node<F, H>>>,
    right: Option<Box<Node<F, H>>>,
    value: Option<F>,
}

impl<F: PrimeField, H: Hash<F>> Node<F, H> {
    pub fn new_leaf(v: F) -> Self {
        let h = H::hash(&[v]);
        Self {
            phantom: PhantomData::<H>,
            hash: h,
            left: None,
            right: None,
            value: Some(v),
        }
    }
    pub fn new_node(l: Self, r: Self) -> Self {
        let left = Box::new(l);
        let right = Box::new(r);
        let hash = H::hash(&[left.hash, right.hash]);
        Self {
            phantom: PhantomData::<H>,
            hash,
            left: Some(left),
            right: Some(right),
            value: None,
        }
    }
}

pub struct MerkleTree<F: PrimeField, H: Hash<F>> {
    pub root: Node<F, H>,
    nlevels: u32,
}

impl<F: PrimeField, H: Hash<F>> MerkleTree<F, H> {
    pub fn commit(values: &[F]) -> (F, Self) {
        // for the moment assume that values length is a power of 2.
        if (values.len() != 0) && (values.len() & (values.len() - 1) != 0) {
            panic!("values.len() should be a power of 2");
        }

        // prepare the leafs
        let mut leaf_nodes: Vec<Node<F, H>> = Vec::new();
        for i in 0..values.len() {
            let node = Node::<F, H>::new_leaf(values[i]);
            leaf_nodes.push(node);
        }
        // go up from the leafs to the root
        let top_nodes = Self::up_from_nodes(leaf_nodes);

        (
            top_nodes[0].hash,
            Self {
                root: top_nodes[0].clone(),
                nlevels: log2(values.len()),
            },
        )
    }
    fn up_from_nodes(nodes: Vec<Node<F, H>>) -> Vec<Node<F, H>> {
        if nodes.len() == 0 {
            return [Node::<F, H> {
                phantom: PhantomData::<H>,
                hash: F::from(0_u32),
                left: None,
                right: None,
                value: None,
            }]
            .to_vec();
        }
        if nodes.len() == 1 {
            return nodes;
        }
        let mut next_level_nodes: Vec<Node<F, H>> = Vec::new();
        for i in (0..nodes.len()).step_by(2) {
            let node = Node::<F, H>::new_node(nodes[i].clone(), nodes[i + 1].clone());
            next_level_nodes.push(node);
        }
        return Self::up_from_nodes(next_level_nodes);
    }
    fn get_path(num_levels: u32, value: F) -> Vec<bool> {
        let value_bytes = value.into_bigint().to_bytes_le();
        let mut path = Vec::new();
        for i in 0..num_levels {
            path.push(value_bytes[(i / 8) as usize] & (1 << (i % 8)) != 0);
        }
        path
    }
    pub fn open(&self, index: F) -> Vec<F> {
        // start from root, and go down to the index, while getting the siblings at each level
        let path = Self::get_path(self.nlevels, index);
        // reverse path as we're going from up to down
        let path_inv = path.iter().copied().rev().collect();
        let mut siblings: Vec<F> = Vec::new();
        siblings = Self::go_down(path_inv, self.root.clone(), siblings);
        return siblings;
    }
    fn go_down(path: Vec<bool>, node: Node<F, H>, mut siblings: Vec<F>) -> Vec<F> {
        if !node.value.is_none() {
            return siblings;
        }
        if !path[0] {
            siblings.push(node.right.unwrap().hash);
            return Self::go_down(path[1..].to_vec(), *node.left.unwrap(), siblings);
        } else {
            siblings.push(node.left.unwrap().hash);
            return Self::go_down(path[1..].to_vec(), *node.right.unwrap(), siblings);
        }
    }
    pub fn verify(root: F, index: F, value: F, siblings: Vec<F>) -> bool {
        let mut h = H::hash(&[value]);
        let path = Self::get_path(siblings.len() as u32, index);
        for i in 0..siblings.len() {
            if !path[i] {
                h = H::hash(&[h, siblings[siblings.len() - 1 - i]]);
            } else {
                h = H::hash(&[siblings[siblings.len() - 1 - i], h]);
            }
        }
        if h == root {
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::UniformRand;
    pub type Fr = ark_bn254::Fr; // scalar field

    #[test]
    fn test_path() {
        assert_eq!(
            MerkleTree::<Fr, Keccak256Hash<Fr>>::get_path(8, Fr::from(0_u32)),
            [false, false, false, false, false, false, false, false]
        );
        assert_eq!(
            MerkleTree::<Fr, Keccak256Hash<Fr>>::get_path(8, Fr::from(1_u32)),
            [true, false, false, false, false, false, false, false]
        );
        assert_eq!(
            MerkleTree::<Fr, Keccak256Hash<Fr>>::get_path(8, Fr::from(2_u32)),
            [false, true, false, false, false, false, false, false]
        );
        assert_eq!(
            MerkleTree::<Fr, Keccak256Hash<Fr>>::get_path(8, Fr::from(3_u32)),
            [true, true, false, false, false, false, false, false]
        );
        assert_eq!(
            MerkleTree::<Fr, Keccak256Hash<Fr>>::get_path(8, Fr::from(254_u32)),
            [false, true, true, true, true, true, true, true]
        );
        assert_eq!(
            MerkleTree::<Fr, Keccak256Hash<Fr>>::get_path(8, Fr::from(255_u32)),
            [true, true, true, true, true, true, true, true]
        );
    }

    #[test]
    fn test_new_empty_tree() {
        let (root, mt) = MerkleTree::<Fr, Keccak256Hash<Fr>>::commit(&[]);
        assert_eq!(mt.root.hash, Fr::from(0_u32));
        assert_eq!(root, Fr::from(0_u32));
    }

    #[test]
    fn test_proof() {
        type MT = MerkleTree<Fr, Keccak256Hash<Fr>>;

        let values = [
            Fr::from(0_u32),
            Fr::from(1_u32),
            Fr::from(2_u32),
            Fr::from(3_u32),
            Fr::from(200_u32),
            Fr::from(201_u32),
            Fr::from(202_u32),
            Fr::from(203_u32),
        ];

        let (root, mt) = MT::commit(&values);
        assert_eq!(
            root.to_string(),
            "6195952497672867974990959901930625199810318409246598214215524466855665265259"
        );

        let index = 3;
        let index_F = Fr::from(index as u32);
        let siblings = mt.open(index_F);

        assert!(MT::verify(root, index_F, values[index], siblings));
    }

    #[test]
    fn test_proofs() {
        type MT = MerkleTree<Fr, Keccak256Hash<Fr>>;
        let mut rng = ark_std::test_rng();

        let n_values = 64;
        let mut values: Vec<Fr> = Vec::new();
        for _i in 0..n_values {
            let v = Fr::rand(&mut rng);
            values.push(v);
        }

        let (root, mt) = MT::commit(&values);
        assert_eq!(mt.nlevels, 6);

        for i in 0..n_values {
            let i_Fr = Fr::from(i as u32);
            let siblings = mt.open(i_Fr);
            assert!(MT::verify(root, i_Fr, values[i], siblings));
        }
    }
}
