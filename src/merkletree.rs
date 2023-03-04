// merkletree.rs implements a simple binary insert-only merkletree in which the leafs positions is
// determined by the leaf value binary representation. Inspired by
// https://docs.iden3.io/publications/pdfs/Merkle-Tree.pdf (which can be found implemented in
// https://github.com/vocdoni/arbo).

use ark_ff::{BigInteger, PrimeField};
use ark_std::log2;
use arkworks_native_gadgets::poseidon;
use arkworks_native_gadgets::poseidon::FieldHasher;
use arkworks_utils::{
    bytes_matrix_to_f, bytes_vec_to_f, poseidon_params::setup_poseidon_params, Curve,
};

pub struct Params<F: PrimeField> {
    pub poseidon_hash: poseidon::Poseidon<F>,
}

#[derive(Clone, Debug)]
pub struct Node<F: PrimeField> {
    hash: F,
    left: Option<Box<Node<F>>>,
    right: Option<Box<Node<F>>>,
    value: Option<F>,
}

impl<F: PrimeField> Node<F> {
    pub fn new_leaf(params: &Params<F>, v: F) -> Self {
        let h = params.poseidon_hash.hash(&[v]).unwrap();
        Self {
            hash: h,
            left: None,
            right: None,
            value: Some(v),
        }
    }
    pub fn new_node(params: &Params<F>, l: Self, r: Self) -> Self {
        let left = Box::new(l);
        let right = Box::new(r);
        let hash = params.poseidon_hash.hash(&[left.hash, right.hash]).unwrap();
        Self {
            hash,
            left: Some(left),
            right: Some(right),
            value: None,
        }
    }
}

pub struct MerkleTree<F: PrimeField> {
    pub root: Node<F>,
    nlevels: u32,
}

impl<F: PrimeField> MerkleTree<F> {
    pub fn setup(poseidon_hash: &poseidon::Poseidon<F>) -> Params<F> {
        Params {
            poseidon_hash: poseidon_hash.clone(),
        }
    }
    pub fn new(params: &Params<F>, values: Vec<F>) -> Self {
        // for the moment assume that values length is a power of 2.
        if (values.len() != 0) && (values.len() & (values.len() - 1) != 0) {
            panic!("values.len() should be a power of 2");
        }

        // prepare the leafs
        let mut leaf_nodes: Vec<Node<F>> = Vec::new();
        for i in 0..values.len() {
            let node = Node::<F>::new_leaf(&params, values[i]);
            leaf_nodes.push(node);
        }
        // go up from the leafs to the root
        let top_nodes = Self::up_from_nodes(&params, leaf_nodes);

        Self {
            root: top_nodes[0].clone(),
            nlevels: log2(values.len()),
        }
    }
    fn up_from_nodes(params: &Params<F>, nodes: Vec<Node<F>>) -> Vec<Node<F>> {
        if nodes.len() == 0 {
            return [Node::<F> {
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
        let mut next_level_nodes: Vec<Node<F>> = Vec::new();
        for i in (0..nodes.len()).step_by(2) {
            let node = Node::<F>::new_node(&params, nodes[i].clone(), nodes[i + 1].clone());
            next_level_nodes.push(node);
        }
        return Self::up_from_nodes(params, next_level_nodes);
    }
    fn get_path(num_levels: u32, value: F) -> Vec<bool> {
        let value_bytes = value.into_repr().to_bytes_le();
        let mut path = Vec::new();
        for i in 0..num_levels {
            path.push(value_bytes[(i / 8) as usize] & (1 << (i % 8)) != 0);
        }
        path
    }
    pub fn gen_proof(&self, index: usize) -> Vec<F> {
        // start from root, and go down to the index, while getting the siblings at each level
        let path = Self::get_path(self.nlevels, F::from(index as u32));
        // reverse path as we're going from up to down
        let path_inv = path.iter().copied().rev().collect();
        let mut siblings: Vec<F> = Vec::new();
        siblings = Self::go_down(path_inv, self.root.clone(), siblings);
        return siblings;
    }
    fn go_down(path: Vec<bool>, node: Node<F>, mut siblings: Vec<F>) -> Vec<F> {
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
    pub fn verify(params: &Params<F>, root: F, index: usize, value: F, siblings: Vec<F>) -> bool {
        let mut h = params.poseidon_hash.hash(&[value]).unwrap();
        let path = Self::get_path(siblings.len() as u32, F::from(index as u32));
        for i in 0..siblings.len() {
            if !path[i] {
                h = params
                    .poseidon_hash
                    .hash(&[h, siblings[siblings.len() - 1 - i]])
                    .unwrap();
            } else {
                h = params
                    .poseidon_hash
                    .hash(&[siblings[siblings.len() - 1 - i], h])
                    .unwrap();
            }
        }
        if h == root {
            return true;
        }
        false
    }
}

pub struct MerkleTreePoseidon<F: PrimeField>(MerkleTree<F>);
impl<F: PrimeField> MerkleTreePoseidon<F> {
    pub fn commit(values: &[F]) -> (F, Self) {
        let poseidon_params = poseidon_setup_params::<F>(Curve::Bn254, 5, 4);
        let poseidon_hash = poseidon::Poseidon::new(poseidon_params);
        let params = MerkleTree::setup(&poseidon_hash);
        let mt = MerkleTree::new(&params, values.to_vec());
        (mt.root.hash, MerkleTreePoseidon(mt))
    }
    pub fn prove(&self, index: usize) -> Vec<F> {
        self.0.gen_proof(index)
    }
    pub fn verify(root: F, index: usize, value: F, siblings: Vec<F>) -> bool {
        let poseidon_params = poseidon_setup_params::<F>(Curve::Bn254, 5, 4);
        let poseidon_hash = poseidon::Poseidon::new(poseidon_params);
        let params = MerkleTree::setup(&poseidon_hash);
        MerkleTree::verify(&params, root, index, value, siblings)
    }
}

pub fn poseidon_setup_params<F: PrimeField>(
    curve: Curve,
    exp: i8,
    width: u8,
) -> poseidon::PoseidonParameters<F> {
    let pos_data = setup_poseidon_params(curve, exp, width).unwrap();

    let mds_f = bytes_matrix_to_f(&pos_data.mds);
    let rounds_f = bytes_vec_to_f(&pos_data.rounds);

    poseidon::PoseidonParameters {
        mds_matrix: mds_f,
        round_keys: rounds_f,
        full_rounds: pos_data.full_rounds,
        partial_rounds: pos_data.partial_rounds,
        sbox: poseidon::sbox::PoseidonSbox(pos_data.exp),
        width: pos_data.width,
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
            MerkleTree::get_path(8, Fr::from(0_u32)),
            [false, false, false, false, false, false, false, false]
        );
        assert_eq!(
            MerkleTree::get_path(8, Fr::from(1_u32)),
            [true, false, false, false, false, false, false, false]
        );
        assert_eq!(
            MerkleTree::get_path(8, Fr::from(2_u32)),
            [false, true, false, false, false, false, false, false]
        );
        assert_eq!(
            MerkleTree::get_path(8, Fr::from(3_u32)),
            [true, true, false, false, false, false, false, false]
        );
        assert_eq!(
            MerkleTree::get_path(8, Fr::from(254_u32)),
            [false, true, true, true, true, true, true, true]
        );
        assert_eq!(
            MerkleTree::get_path(8, Fr::from(255_u32)),
            [true, true, true, true, true, true, true, true]
        );
    }

    #[test]
    fn test_new_empty_tree() {
        let poseidon_params = poseidon_setup_params::<Fr>(Curve::Bn254, 5, 4);
        let poseidon_hash = poseidon::Poseidon::new(poseidon_params);

        let params = MerkleTree::setup(&poseidon_hash);
        let mt = MerkleTree::new(&params, Vec::new());
        assert_eq!(mt.root.hash, Fr::from(0_u32));
    }

    #[test]
    fn test_proof() {
        let poseidon_params = poseidon_setup_params::<Fr>(Curve::Bn254, 5, 4);
        let poseidon_hash = poseidon::Poseidon::new(poseidon_params);

        let params = MerkleTree::setup(&poseidon_hash);

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

        let mt = MerkleTree::new(&params, values.to_vec());
        assert_eq!(
            mt.root.hash.to_string(),
            "Fp256 \"(10E90845D7A113686E4F2F30D73B315BA891A5DB9A58782F1260C35F99660794)\""
        );

        let index = 3;
        let siblings = mt.gen_proof(index);

        assert!(MerkleTree::verify(
            &params,
            mt.root.hash,
            index,
            values[index],
            siblings
        ));
    }

    #[test]
    fn test_proofs() {
        let poseidon_params = poseidon_setup_params::<Fr>(Curve::Bn254, 5, 4);
        let poseidon_hash = poseidon::Poseidon::new(poseidon_params);

        let params = MerkleTree::setup(&poseidon_hash);

        let mut rng = ark_std::test_rng();

        let n_values = 256;
        let mut values: Vec<Fr> = Vec::new();
        for _i in 0..n_values {
            let v = Fr::rand(&mut rng);
            values.push(v);
        }

        let mt = MerkleTree::new(&params, values.to_vec());
        assert_eq!(mt.nlevels, 8);

        for i in 0..n_values {
            let siblings = mt.gen_proof(i);
            assert!(MerkleTree::verify(
                &params,
                mt.root.hash,
                i,
                values[i],
                siblings
            ));
        }
    }
}
