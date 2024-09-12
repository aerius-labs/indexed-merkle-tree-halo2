use halo2_base::utils::ScalarField;
use pse_poseidon::Poseidon;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IndexedMerkleTreeLeaf<F: ScalarField> {
    pub val: F,
    pub next_val: F,
    pub next_idx: F,
}

pub fn get_low_leaf_idx<F: ScalarField>(
    leaves: &Vec<IndexedMerkleTreeLeaf<F>>,
    new_val: F,
) -> usize {
    let mut low_leaf_idx = 0;
    for (i, node) in leaves.iter().enumerate() {
        if node.next_val == F::ZERO && i == 0 {
            low_leaf_idx = i;
            break;
        }
        if node.val < new_val && (node.next_val > new_val || node.next_val == F::ZERO) {
            low_leaf_idx = i;
            break;
        }
    }
    low_leaf_idx
}

pub fn update_sparse_idx_leaf<F: ScalarField>(
    leaves: &mut Vec<IndexedMerkleTreeLeaf<F>>,
    new_val: F,
    new_val_idx: u64,
) {
    for (i, node) in leaves.iter().enumerate() {
        if node.next_val == F::ZERO && i == 0 {
            leaves[i + 1].val = new_val;
            leaves[i].next_val = new_val;
            leaves[i].next_idx = F::from((i as u64) + 1);
            break;
        }
        if node.val < new_val && (node.next_val > new_val || node.next_val == F::ZERO) {
            leaves[new_val_idx as usize].val = new_val;
            leaves[new_val_idx as usize].next_val = leaves[i].next_val;
            leaves[new_val_idx as usize].next_idx = leaves[i].next_idx;
            leaves[i].next_val = new_val;
            leaves[i].next_idx = F::from(new_val_idx);
            break;
        }
    }
}

#[derive(Debug)]
pub struct IndexedMerkleTree<F: ScalarField, const T: usize, const RATE: usize> {
    pub nodes: Vec<Vec<F>>,
    pub root: F,
}

impl<'a, F: ScalarField, const T: usize, const RATE: usize> IndexedMerkleTree<F, T, RATE> {
    pub fn new_default_leaf(depth: usize) -> Self {
        let mut nodes = Vec::<Vec<F>>::new();
        for _ in 0..depth {
            let mut level_nodes = Vec::<F>::new();
            level_nodes.push(F::ZERO);
            nodes.push(level_nodes);
        }
        nodes.push(vec![F::ZERO]);

        IndexedMerkleTree {
            nodes,
            root: F::ZERO,
        }
    }

    pub fn get_leaf_at_index(&self, index: usize) -> F {
        self.nodes[0][index]
    }

    pub fn get_root(&self) -> F {
        self.root
    }

    pub fn insert_leaf(
        &mut self,
        hash: &'a mut Poseidon<F, T, RATE>,
        leaf: F,
        index: usize,
    ) -> (Vec<F>, Vec<F>) {
        let mut current_index = index;
        if self.nodes[0].len() >= index {
            self.nodes[0].push(F::ZERO);
        }

        self.nodes[0][index] = leaf;
        let mut cur_leaf = leaf;

        let mut proof = Vec::<F>::new();
        let mut proof_helper = Vec::<F>::new();

        for i in 0..self.nodes.len() - 1 {
            let level = &self.nodes[i];

            let is_left_node = current_index % 2 == 0;
            let sibling_index = if is_left_node {
                current_index + 1
            } else {
                current_index - 1
            };
            let sibling = if sibling_index < level.len() {
                level[sibling_index]
            } else {
                F::ZERO
            };
            proof.push(sibling);

            let parent_leaf_idx = current_index.clone() / 2;

            if self.nodes[i + 1].len() <= parent_leaf_idx {
                self.nodes[i + 1].push(F::ZERO);
            }

            self.nodes[i + 1][parent_leaf_idx] = if is_left_node {
                proof_helper.push(F::ONE);
                hash.update(&[cur_leaf, sibling]);
                hash.squeeze_and_reset()
            } else {
                proof_helper.push(F::ZERO);
                hash.update(&[sibling, cur_leaf]);
                hash.squeeze_and_reset()
            };

            current_index /= 2;
            cur_leaf = self.nodes[i + 1][parent_leaf_idx];
        }

        self.root = self.nodes.last().unwrap()[0];
        (proof, proof_helper)
    }

    pub fn get_proof(&self, index: usize) -> (Vec<F>, Vec<F>) {
        let mut proof = Vec::new();
        let mut proof_helper = Vec::new();
        let mut current_index = index;

        for i in 0..self.nodes.len() - 1 {
            let level = &self.nodes[i];
            let is_left_node = current_index % 2 == 0;
            let sibling_index = if is_left_node {
                current_index + 1
            } else {
                current_index - 1
            };

            let sibling = if sibling_index < level.len() {
                level[sibling_index]
            } else {
                F::ZERO
            };
            proof.push(sibling);
            proof_helper.push(if is_left_node { F::ONE } else { F::ZERO });

            current_index /= 2;
        }
        (proof, proof_helper)
    }

    pub fn verify_proof(
        &mut self,
        hash: &'a mut Poseidon<F, T, RATE>,
        index: usize,
        root: &F,
        proof: &[F],
    ) -> bool {
        let mut computed_hash = self.nodes[0][index];
        let mut current_index = index;

        for i in 0..proof.len() {
            let proof_element = &proof[i];
            let is_left_node = current_index % 2 == 0;

            computed_hash = if is_left_node {
                hash.update(&[computed_hash, *proof_element]);
                hash.squeeze_and_reset()
            } else {
                hash.update(&[*proof_element, computed_hash]);
                hash.squeeze_and_reset()
            };

            current_index /= 2;
        }

        computed_hash == *root
    }

    pub fn compute_merkle_root(
        &mut self,
        hash: &'a mut Poseidon<F, T, RATE>,
        leaf: &F,
        proof: &[F],
        proof_helper: &[F],
    ) -> F {
        let mut current = *leaf;

        for (&proof_element, &is_right) in proof.iter().zip(proof_helper.iter()) {
            if current == proof_element {
                current = F::ZERO;
            } else {
                let (left, right) = if is_right == F::ZERO {
                    (proof_element, current)
                } else {
                    (current, proof_element)
                };

                hash.update(&[left, right]);
                current = hash.squeeze_and_reset();
            }
        }

        current
    }

    pub fn print_tree(&mut self) {
        for level in self.nodes.iter() {
            for node in level {
                println!("{:?}  ---   ", node)
            }
            println!();
        }

        println!("depth --- {:?}", self.nodes.len());
    }

    pub fn hash_leaf(
        &mut self,
        hash: &'a mut Poseidon<F, T, RATE>,
        leaf: IndexedMerkleTreeLeaf<F>,
    ) -> F {
        hash.update(&[leaf.val, leaf.next_val, leaf.next_idx]);
        hash.squeeze_and_reset()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_base::{halo2_proofs::halo2curves::grumpkin::Fq as F, utils::biguint_to_fe};
    use num_bigint::BigUint;
    use num_traits::FromBytes;
    use pse_poseidon::Poseidon;

    #[test]
    fn test_native_merkle_root() {
        let leaf = F::from(99u64);

        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;
        let mut hash = Poseidon::<F, T, RATE>::new(R_F, R_P);

        let proof: [F; 5] = [
            F::from(1u64),
            F::from(5u64),
            F::from(6u64),
            F::from(9u64),
            F::from(9u64),
        ];

        let proof_helper: [F; 5] = [
            F::from(0u64),
            F::from(1u64),
            F::from(1u64),
            F::from(1u64),
            F::from(1u64),
        ];
        let depth = 3;
        let mut tree = IndexedMerkleTree::<F, 3, 2>::new_default_leaf(depth);
        tree.insert_leaf(&mut hash, F::from(1u64), 0);
        tree.insert_leaf(&mut hash, F::from(5u64), 0);
        tree.insert_leaf(&mut hash, F::from(6u64), 0);
        tree.insert_leaf(&mut hash, F::from(9u64), 0);
        tree.insert_leaf(&mut hash, F::from(9u64), 0);

        let root = tree.compute_merkle_root(&mut hash, &leaf, &proof, &proof_helper);

        let expected_root_bigint = BigUint::from_be_bytes(&[
            0x05, 0x5e, 0xc2, 0x46, 0xf4, 0xf1, 0x7b, 0xef, 0x9e, 0xeb, 0x24, 0xa6, 0xa3, 0x98,
            0x78, 0xfa, 0x43, 0x77, 0x29, 0x07, 0x23, 0xca, 0x68, 0xcd, 0x07, 0x18, 0xe9, 0x39,
            0x9d, 0xd9, 0x29, 0xa5,
        ]);
        let expected_root: F = biguint_to_fe(&expected_root_bigint);

        assert_eq!(root, expected_root);
    }
    #[test]
    fn test_insert_leaves_native() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;
        let mut hash = Poseidon::<F, T, RATE>::new(R_F, R_P);

        let depth = 3;
        let mut tree = IndexedMerkleTree::<F, 3, 2>::new_default_leaf(depth);

        tree.insert_leaf(&mut hash, F::from(5), 0);
        tree.insert_leaf(&mut hash, F::from(6), 1);
        tree.insert_leaf(&mut hash, F::from(9), 2);
        tree.insert_leaf(&mut hash, F::from(9), 3);

        assert_eq!(tree.get_leaf_at_index(0), F::from(5));
        assert_eq!(tree.get_leaf_at_index(1), F::from(6));
        assert_eq!(tree.get_leaf_at_index(2), F::from(9));
        assert_eq!(tree.get_leaf_at_index(3), F::from(9));

        let (proof, _) = tree.get_proof(3);

        let expected_root = tree.get_root();
        let result = tree.verify_proof(&mut hash, 3, &expected_root, &proof);
        assert_eq!(result, true);
    }
}
