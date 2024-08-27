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
                proof_helper.push(F::ONE);
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

    pub fn print_tree(&mut self) {
        for level in self.nodes.iter() {
            for node in level {
                println!("{:?}  ---   ", node)
            }
            println!();
        }

        println!("depth --- {:?}", self.nodes.len());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_base::halo2_proofs::halo2curves::grumpkin::Fq as F;
    use pse_poseidon::Poseidon;

    #[test]
    fn test_insert_leaves() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;
        let mut hash = Poseidon::<F, T, RATE>::new(R_F, R_P);

        let depth = 3;
        let mut tree = IndexedMerkleTree::<F, 3, 2>::new_default_leaf(depth);

        assert_eq!(tree.nodes.len(), depth + 1);

        tree.insert_leaf(&mut hash, F::from(10), 0);
        tree.insert_leaf(&mut hash, F::from(30), 1);
        tree.insert_leaf(&mut hash, F::from(50), 2);
        tree.insert_leaf(&mut hash, F::from(20), 3);

        assert_eq!(tree.get_leaf_at_index(0), F::from(10));
        assert_eq!(tree.get_leaf_at_index(1), F::from(30));
        assert_eq!(tree.get_leaf_at_index(2), F::from(50));
        assert_eq!(tree.get_leaf_at_index(3), F::from(20));
        // dbg!(tree);
        tree.print_tree();
    }
}
