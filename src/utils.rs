use halo2_base::utils::ScalarField;
use pse_poseidon::Poseidon;

#[derive(Debug)]
struct MerkleTree<'a, F: ScalarField, const T: usize, const RATE: usize> {
    hash: &'a mut Poseidon<F, T, RATE>,
    tree: Vec<Vec<F>>,
    root: F,
}

impl<'a, F: ScalarField, const T: usize, const RATE: usize> MerkleTree<'a, F, T, RATE> {
    fn new(
        hash: &'a mut Poseidon<F, T, RATE>,
        leaves: Vec<F>
    ) -> Result<MerkleTree<'a, F, T, RATE>, &'static str> {
        if leaves.is_empty() {
            return Err("Cannot create Merkle Tree with no leaves");
        }
        if leaves.len() == 1 {
            return Ok(MerkleTree {
                hash,
                tree: vec![leaves.clone()],
                root: leaves[0],
            });
        }
        if leaves.len() % 2 == 1 {
            return Err("Leaves must be even");
        }

        let mut tree = vec![leaves.clone()];
        let mut level = 0;
        let mut current_level = leaves.clone();

        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            for i in (0..current_level.len()).step_by(2) {
                let left = current_level[i];
                let right = current_level[i + 1];
                hash.update(&[left, right]);
                next_level.push(hash.squeeze());
            }
            tree.push(next_level.clone());
            current_level = next_level.clone();
            level += 1;
        }
        Ok(MerkleTree {
            hash,
            tree,
            root: current_level[0],
        })
    }

    fn get_root(&self) -> F {
        self.root
    }

    fn get_proof(&self, index: usize) -> (Vec<F>, Vec<bool>) {
        let mut proof = Vec::new();
        let mut proof_helper = Vec::new();
        let mut current_index = index;

        for i in 0..self.tree.len() - 1 {
            let level = &self.tree[i];
            let is_left_node = current_index % 2 == 0;
            let sibling_index = if is_left_node { current_index + 1 } else { current_index - 1 };
            let sibling = level[sibling_index];

            proof.push(sibling);
            proof_helper.push(is_left_node);

            current_index /= 2;
        }

        (proof, proof_helper)
    }

    fn verify_proof(&mut self, leaf: F, index: usize, root: F, proof: Vec<F>) -> bool {
        let mut computed_hash = leaf;
        let mut current_index = index;

        for i in 0..proof.len() {
            let proof_element = &proof[i];
            let is_left_node = current_index % 2 == 0;

            computed_hash = if is_left_node {
                self.hash.update(&[computed_hash, *proof_element]);
                self.hash.squeeze()
            } else {
                self.hash.update(&[*proof_element, computed_hash]);
                self.hash.squeeze()
            };

            current_index /= 2;
        }

        computed_hash == root
    }
}
