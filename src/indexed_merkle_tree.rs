use ark_std::One;
use halo2_base::{
    gates::{GateChip, GateInstructions, RangeChip, RangeInstructions},
    poseidon::hasher::PoseidonHasher,
    utils::{biguint_to_fe, fe_to_biguint, BigPrimeField, ScalarField},
    AssignedValue, Context,
};
use num_bigint::BigUint;

#[derive(Clone, Debug)]
pub struct IndexedMerkleTreeLeaf<F: BigPrimeField> {
    val: AssignedValue<F>,
    next_val: AssignedValue<F>,
    next_idx: AssignedValue<F>,
}
impl<F: BigPrimeField> IndexedMerkleTreeLeaf<F> {
    pub fn new(
        val: AssignedValue<F>,
        next_val: AssignedValue<F>,
        next_idx: AssignedValue<F>,
    ) -> Self {
        Self {
            val,
            next_val,
            next_idx,
        }
    }
}

// constrains s(a) + (1-s)(b) = output
pub(crate) fn select<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    one: AssignedValue<F>,
    s: AssignedValue<F>,
    a: AssignedValue<F>,
    b: AssignedValue<F>,
) -> AssignedValue<F> {
    gate.assert_bit(ctx, s);
    let a_s = gate.mul(ctx, a, s);
    let one_minus_s = gate.sub(ctx, one, s);
    gate.mul_add(ctx, one_minus_s, b, a_s)
}

pub(crate) fn dual_mux<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    a: &AssignedValue<F>,
    b: &AssignedValue<F>,
    switch: &AssignedValue<F>,
) -> [AssignedValue<F>; 2] {
    gate.assert_bit(ctx, *switch);

    let a_sub_b = gate.sub(ctx, *a, *b);
    let b_sub_a = gate.sub(ctx, *b, *a);

    let left = gate.mul_add(ctx, a_sub_b, *switch, *b); // left = (a-b)*s + b;
    let right = gate.mul_add(ctx, b_sub_a, *switch, *a); // right = (b-a)*s + a;

    [left, right]
}

pub fn verify_merkle_proof<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    root: &AssignedValue<F>,
    leaf: &AssignedValue<F>,
    proof: &[AssignedValue<F>],
    proof_helper: &[AssignedValue<F>],
    zero: &AssignedValue<F>,
    one: &AssignedValue<F>,
    is_intermediate: bool,
) {
    if is_intermediate {
        let computed_root =
            calculate_intermediate_root(ctx, range, hasher, leaf, proof, proof_helper, zero, one);
        ctx.constrain_equal(&computed_root, root);
    } else {
        let computed_root = calculate_merkle_root(ctx, range, hasher, leaf, proof, proof_helper);
        ctx.constrain_equal(&computed_root, root);
    }
}

pub fn calculate_merkle_root<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    leaf: &AssignedValue<F>,
    proof: &[AssignedValue<F>],
    proof_helper: &[AssignedValue<F>],
) -> AssignedValue<F> {
    let gate = range.gate();
    let mut computed_root = *leaf;

    for (proof_element, helper) in proof.iter().zip(proof_helper.iter()) {
        let inp = dual_mux(ctx, gate, &computed_root, proof_element, helper);
        computed_root = hasher.hash_fix_len_array(ctx, gate, &inp);
    }

    computed_root
}

pub fn calculate_intermediate_root<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    leaf: &AssignedValue<F>,
    proof: &[AssignedValue<F>],
    proof_helper: &[AssignedValue<F>],
    zero: &AssignedValue<F>,
    one: &AssignedValue<F>,
) -> AssignedValue<F> {
    let gate = range.gate();

    let mut computed_root = ctx.load_witness(*leaf.value());

    for (proof_element, helper) in proof.iter().zip(proof_helper.iter()) {
        let is_equal = gate.is_equal(ctx, computed_root, *proof_element);
        let inp = dual_mux(ctx, gate, &computed_root, proof_element, helper);
        let sibling_hash = hasher.hash_fix_len_array(ctx, gate, &inp);
        computed_root = select(ctx, gate, *one, is_equal, *zero, sibling_hash);
    }

    computed_root
}

pub fn is_less_than<F: BigPrimeField>(
    gate: &GateChip<F>,
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    a_q: AssignedValue<F>,
    a_r: AssignedValue<F>,
    b_q: AssignedValue<F>,
    b_r: AssignedValue<F>,
) -> AssignedValue<F> {
    let is_ll_msb_gr = range.is_less_than(ctx, a_q, b_q, 128);
    let are_msb_eq = gate.is_equal(ctx, a_q, b_q);

    let is_ll_lsb_gr = range.is_less_than(ctx, a_r, b_r, 128);
    let are_lsb_eq = gate.is_equal(ctx, a_r, b_r);

    let a = is_ll_msb_gr;
    let c_not = gate.not(ctx, are_msb_eq);
    let a_not = gate.not(ctx, a);
    let b = is_ll_lsb_gr;
    let c = gate.not(ctx, c_not);
    let d_not = gate.not(ctx, are_lsb_eq);

    let rhs = [b, c, d_not]
        .iter()
        .fold(a_not, |a_not, x| gate.and(ctx, a_not, *x));
    let lhs = gate.and(ctx, a, c_not);
    gate.or(ctx, lhs, rhs)
}

pub fn verify_non_inclusion<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    root: &AssignedValue<F>,
    low_leaf: &IndexedMerkleTreeLeaf<F>,
    low_leaf_proof: &[AssignedValue<F>],
    low_leaf_proof_helper: &[AssignedValue<F>],
    new_leaf_value: &AssignedValue<F>,
    zero: &AssignedValue<F>,
    one: &AssignedValue<F>,
) {
    let gate = range.gate();

    let is_zero = gate.is_equal(ctx, low_leaf.next_val, *zero);

    let nl_bu = fe_to_biguint(new_leaf_value.value());
    let ll_bu = fe_to_biguint(low_leaf.next_val.value());

    let pow_128: BigUint = BigUint::one() << 128;
    let (nl_q_bu, nl_r_bu) = (
        nl_bu.clone() / pow_128.clone(),
        nl_bu.clone() % pow_128.clone(),
    );
    let (ll_q_bu, ll_r_bu) = (
        ll_bu.clone() / pow_128.clone(),
        ll_bu.clone() % pow_128.clone(),
    );

    assert_eq!(
        ((nl_bu.clone() / pow_128.clone()) * (BigUint::one() << 128))
            + nl_bu.clone() % pow_128.clone(),
        nl_bu
    );
    assert_eq!(
        ((ll_bu.clone() / pow_128.clone()) * (BigUint::one() << 128))
            + ll_bu.clone() % pow_128.clone(),
        ll_bu
    );

    let [nl_q, nl_r, ll_q, ll_r] = [nl_q_bu, nl_r_bu, ll_q_bu, ll_r_bu].map(|x| {
        let f: F = biguint_to_fe(&x);
        ctx.load_witness(f)
    });
    let pow_128_assign = ctx.load_constant(biguint_to_fe(&pow_128));

    let valid_nl = gate.mul_add(ctx, nl_q, pow_128_assign, nl_r);
    ctx.constrain_equal(&valid_nl, &new_leaf_value);
    let valid_ll = gate.mul_add(ctx, ll_q, pow_128_assign, ll_r);
    ctx.constrain_equal(&valid_ll, &low_leaf.next_val);

    let is_next_val_greater = is_less_than(gate, ctx, range, nl_q, nl_r, ll_q, ll_r);

    let condition = gate.or(ctx, is_zero, is_next_val_greater);
    ctx.constrain_equal(&condition, one);

    let inp = [low_leaf.val, low_leaf.next_val, low_leaf.next_idx];
    let low_leaf_hash = hasher.hash_fix_len_array(ctx, gate, &inp);

    verify_merkle_proof(
        ctx,
        range,
        hasher,
        root,
        &low_leaf_hash,
        low_leaf_proof,
        low_leaf_proof_helper,
        &zero,
        &one,
        false,
    );

    let llv_bu = fe_to_biguint(low_leaf.val.value());

    let (llv_q_bu, llv_r_bu) = (
        llv_bu.clone() / pow_128.clone(),
        llv_bu.clone() % pow_128.clone(),
    );

    assert_eq!(
        ((llv_bu.clone() / pow_128.clone()) * (BigUint::one() << 128))
            + llv_bu.clone() % pow_128.clone(),
        llv_bu
    );

    let [llv_q, llv_r] = [llv_q_bu, llv_r_bu].map(|x| {
        let f: F = biguint_to_fe(&x);
        ctx.load_witness(f)
    });
    let valid_llv = gate.mul_add(ctx, llv_q, pow_128_assign, llv_r);
    ctx.constrain_equal(&valid_llv, &low_leaf.val);

    let check_less_than = is_less_than(gate, ctx, range, llv_q, llv_r, nl_q, nl_r);
    let one = ctx.load_constant(F::ONE);
    ctx.constrain_equal(&check_less_than, &one);
}

pub fn insert_leaf<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    old_root: &AssignedValue<F>,
    low_leaf: &IndexedMerkleTreeLeaf<F>,
    low_leaf_proof: &[AssignedValue<F>],
    low_leaf_proof_helper: &[AssignedValue<F>],
    new_root: &AssignedValue<F>,
    new_leaf: &IndexedMerkleTreeLeaf<F>,
    new_leaf_index: &AssignedValue<F>,
    new_leaf_proof: &[AssignedValue<F>],
    new_leaf_proof_helper: &[AssignedValue<F>],
) {
    let gate = range.gate();
    let zero = ctx.load_constant(F::ZERO);
    let one = ctx.load_constant(F::ONE);

    verify_non_inclusion(
        ctx,
        range,
        hasher,
        old_root,
        low_leaf,
        low_leaf_proof,
        low_leaf_proof_helper,
        &new_leaf.val,
        &zero,
        &one,
    );

    let new_low_leaf = IndexedMerkleTreeLeaf {
        val: low_leaf.val,
        next_val: new_leaf.val,
        next_idx: *new_leaf_index,
    };

    let new_low_leaf_hash = hasher.hash_fix_len_array(
        ctx,
        gate,
        &[
            new_low_leaf.val,
            new_low_leaf.next_val,
            new_low_leaf.next_idx,
        ],
    );

    let interim_root = calculate_intermediate_root(
        ctx,
        range,
        hasher,
        &new_low_leaf_hash,
        low_leaf_proof,
        low_leaf_proof_helper,
        &zero,
        &one,
    );

    verify_merkle_proof(
        ctx,
        range,
        hasher,
        &interim_root,
        &zero,
        new_leaf_proof,
        new_leaf_proof_helper,
        &zero,
        &one,
        true,
    );

    ctx.constrain_equal(&new_leaf.next_val, &low_leaf.next_val);
    ctx.constrain_equal(&new_leaf.next_idx, &low_leaf.next_idx);

    let new_leaf_hash = hasher.hash_fix_len_array(
        ctx,
        gate,
        &[new_leaf.val, new_leaf.next_val, new_leaf.next_idx],
    );

    let _new_root = calculate_merkle_root(
        ctx,
        range,
        hasher,
        &new_leaf_hash,
        new_leaf_proof,
        new_leaf_proof_helper,
    );
    ctx.constrain_equal(new_root, &_new_root);
}

#[cfg(test)]
mod test {

    use ark_std::One;
    use halo2_base::poseidon::hasher::spec::OptimizedPoseidonSpec;
    use halo2_base::poseidon::hasher::PoseidonHasher;
    use halo2_base::utils::testing::base_test;
    use halo2_base::utils::ScalarField;

    use halo2_base::{
        gates::{GateChip, RangeInstructions},
        halo2_proofs::halo2curves::grumpkin::Fq as Fr,
        Context,
    };
    use num_bigint::{BigUint, RandBigInt};
    use pse_poseidon::Poseidon;
    use rand::thread_rng;

    use crate::indexed_merkle_tree::{
        calculate_merkle_root, insert_leaf, verify_merkle_proof, verify_non_inclusion,
        IndexedMerkleTreeLeaf,
    };
    use crate::utils::{
        get_low_leaf_idx, update_sparse_idx_leaf, IndexedMerkleTree,
        IndexedMerkleTreeLeaf as IMTLeaf,
    };

    fn select_circuit<F: ScalarField>(ctx: &mut Context<F>, s: bool, a: F, b: F) {
        let gate = GateChip::<F>::default();

        let one = ctx.load_constant(F::ONE);
        let s = ctx.load_witness(F::from(s));
        let a = ctx.load_witness(a);
        let b = ctx.load_witness(b);

        let output = super::select(ctx, &gate, one, s, a, b);

        assert_eq!(output.value(), b.value());
    }

    #[test]
    fn test_select() {
        let s = false;
        let a = 69u64;
        let b = 420u64;

        base_test().k(9).expect_satisfied(true).run(|ctx, _| {
            select_circuit(ctx, s, Fr::from(a), Fr::from(b));
        })
    }

    #[test]
    fn test_calculate_merkle_root() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        let nullifier_preimages = [
            [Fr::from(10u64), Fr::from(20u64), Fr::from(1u64)],
            [Fr::from(20u64), Fr::from(30u64), Fr::from(2u64)],
            [Fr::from(30u64), Fr::from(0u64), Fr::from(0u64)],
        ];

        let mut tree = IndexedMerkleTree::<Fr, T, RATE>::new_default_leaf(8);
        let mut hash = Poseidon::<Fr, T, RATE>::new(R_F, R_P);

        let mut nullifier_hashes: [Fr; 3] = [Fr::default(); 3];

        for i in 0..nullifier_preimages.len() {
            hash.update(&[
                nullifier_preimages[i][0],
                nullifier_preimages[i][1],
                nullifier_preimages[i][2],
            ]);
            nullifier_hashes[i] = hash.squeeze_and_reset();
        }

        tree.insert_leaf(&mut hash, nullifier_hashes[0], 0);
        tree.insert_leaf(&mut hash, nullifier_hashes[1], 1);
        tree.insert_leaf(&mut hash, nullifier_hashes[2], 2);

        let (low_leaf_proof, low_leaf_proof_helper) = tree.get_proof(1);

        let leaf_value = nullifier_hashes[1];

        base_test().k(9).expect_satisfied(true).run(|ctx, range| {
            let mut hasher =
                PoseidonHasher::<Fr, T, RATE>::new(OptimizedPoseidonSpec::new::<R_F, R_P, 0>());
            let gate = range.gate();

            hasher.initialize_consts(ctx, gate);
            let leaf = ctx.load_witness(leaf_value);
            let proof_assigned = low_leaf_proof
                .iter()
                .map(|&x| ctx.load_witness(x))
                .collect::<Vec<_>>();

            let proof_helper_assigned = low_leaf_proof_helper
                .iter()
                .map(|&x| ctx.load_witness(x))
                .collect::<Vec<_>>();

            let zero_assigned = ctx.load_witness(Fr::zero());
            let one_assigned = ctx.load_witness(Fr::one());

            let computed_root = calculate_merkle_root::<Fr, T, RATE>(
                ctx,
                range,
                &hasher,
                &leaf,
                &proof_assigned,
                &proof_helper_assigned,
            );

            verify_merkle_proof(
                ctx,
                range,
                &hasher,
                &computed_root,
                &leaf,
                &proof_assigned,
                &proof_helper_assigned,
                &zero_assigned,
                &one_assigned,
                false,
            );
        });
    }

    #[test]
    fn test_verify_merkle_proof() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        let nullifier_preimages = [
            [Fr::from(10u64), Fr::from(20u64), Fr::from(1u64)],
            [Fr::from(20u64), Fr::from(30u64), Fr::from(2u64)],
            [Fr::from(30u64), Fr::from(0u64), Fr::from(0u64)],
        ];

        let mut tree = IndexedMerkleTree::<Fr, T, RATE>::new_default_leaf(8);
        let mut hash = Poseidon::<Fr, T, RATE>::new(R_F, R_P);

        let mut nullifier_hashes: [Fr; 3] = [Fr::default(); 3];

        for i in 0..nullifier_preimages.len() {
            hash.update(&[
                nullifier_preimages[i][0],
                nullifier_preimages[i][1],
                nullifier_preimages[i][2],
            ]);
            nullifier_hashes[i] = hash.squeeze_and_reset();
        }

        tree.insert_leaf(&mut hash, nullifier_hashes[0], 0);
        tree.insert_leaf(&mut hash, nullifier_hashes[1], 1);
        tree.insert_leaf(&mut hash, nullifier_hashes[2], 2);

        let (low_leaf_proof, low_leaf_proof_helper) = tree.get_proof(1);

        let leaf_value = nullifier_hashes[1];
        let root = tree.get_root();

        base_test().k(10).expect_satisfied(true).run(|ctx, range| {
            let mut hasher =
                PoseidonHasher::<Fr, T, RATE>::new(OptimizedPoseidonSpec::new::<R_F, R_P, 0>());
            let gate = range.gate();

            hasher.initialize_consts(ctx, gate);
            let leaf = ctx.load_witness(leaf_value);
            let root = ctx.load_witness(root);
            let proof_assigned = low_leaf_proof
                .iter()
                .map(|&x| ctx.load_witness(x))
                .collect::<Vec<_>>();

            let proof_helper_assigned = low_leaf_proof_helper
                .iter()
                .map(|&x| ctx.load_witness(x))
                .collect::<Vec<_>>();

            let zero_assigned = ctx.load_witness(Fr::zero());
            let one_assigned = ctx.load_witness(Fr::one());

            verify_merkle_proof(
                ctx,
                range,
                &hasher,
                &root,
                &leaf,
                &proof_assigned,
                &proof_helper_assigned,
                &zero_assigned,
                &one_assigned,
                false,
            );
        });
    }
    #[test]
    fn test_verify_non_inclusion() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        let nullifier_preimages = [
            [Fr::from(10u64), Fr::from(20u64), Fr::from(1u64)],
            [Fr::from(20u64), Fr::from(30u64), Fr::from(2u64)],
            [Fr::from(30u64), Fr::from(0u64), Fr::from(0u64)],
        ];

        let mut tree = IndexedMerkleTree::<Fr, T, RATE>::new_default_leaf(8);
        let mut hash = Poseidon::<Fr, T, RATE>::new(R_F, R_P);

        let mut nullifier_hashes: [Fr; 3] = [Fr::default(); 3];

        for i in 0..nullifier_preimages.len() {
            hash.update(&[
                nullifier_preimages[i][0],
                nullifier_preimages[i][1],
                nullifier_preimages[i][2],
            ]);
            nullifier_hashes[i] = hash.squeeze_and_reset();
        }

        tree.insert_leaf(&mut hash, nullifier_hashes[0], 0);
        tree.insert_leaf(&mut hash, nullifier_hashes[1], 1);
        tree.insert_leaf(&mut hash, nullifier_hashes[2], 2);

        let (low_leaf_proof, low_leaf_proof_helper) = tree.get_proof(1);

        let root = tree.get_root();
        let new_leaf_value = Fr::from(25);

        base_test().k(19).expect_satisfied(true).run(|ctx, range| {
            let mut hasher =
                PoseidonHasher::<Fr, T, RATE>::new(OptimizedPoseidonSpec::new::<R_F, R_P, 0>());
            let gate = range.gate();

            hasher.initialize_consts(ctx, gate);
            let root = ctx.load_witness(root);

            let new_leaf_value_assigned = ctx.load_witness(new_leaf_value);
            let low_leaf = IndexedMerkleTreeLeaf {
                val: ctx.load_witness(nullifier_preimages[1][0]),
                next_val: ctx.load_witness(nullifier_preimages[1][1]),
                next_idx: ctx.load_witness(nullifier_preimages[1][2]),
            };

            let proof_assigned = low_leaf_proof
                .iter()
                .map(|&x| ctx.load_witness(x))
                .collect::<Vec<_>>();

            let proof_helper_assigned = low_leaf_proof_helper
                .iter()
                .map(|&x| ctx.load_witness(x))
                .collect::<Vec<_>>();

            let zero_assigned = ctx.load_witness(Fr::zero());
            let one_assigned = ctx.load_witness(Fr::one());

            verify_non_inclusion(
                ctx,
                range,
                &hasher,
                &root,
                &low_leaf,
                &proof_assigned,
                &proof_helper_assigned,
                &new_leaf_value_assigned,
                &zero_assigned,
                &one_assigned,
            );
        });
    }
    #[test]
    fn test_insert_leaf() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        let depth = 30;

        let mut native_hasher = Poseidon::<Fr, T, RATE>::new(R_F, R_P);

        let mut nullifier_tree_preimages = vec![
            IMTLeaf {
                val: Fr::from(0u64),
                next_val: Fr::from(0u64),
                next_idx: Fr::from(0u64),
            },
            IMTLeaf {
                val: Fr::from(10u64),
                next_val: Fr::from(0u64),
                next_idx: Fr::from(0u64),
            },
        ];

        let mut tree = IndexedMerkleTree::<Fr, T, RATE>::new_default_leaf(depth);
        let init_idx_leaf = hash_leaf(&nullifier_tree_preimages[0]);

        tree.insert_leaf(&mut native_hasher, init_idx_leaf, 0);

        let old_root = tree.get_root();
        let new_val = Fr::from(74);

        let low_leaf_idx = 0;
        let idx_low_leaf = nullifier_tree_preimages[low_leaf_idx].clone();

        let (low_leaf_proof, low_leaf_proof_helper) = tree.get_proof(low_leaf_idx);

        update_sparse_idx_leaf(&mut nullifier_tree_preimages, new_val, 1);

        let new_low_leaf = hash_leaf(&nullifier_tree_preimages[low_leaf_idx]);

        tree.insert_leaf(&mut native_hasher, new_low_leaf, low_leaf_idx);

        let new_leaf_hash = hash_leaf(&nullifier_tree_preimages[1]);

        let (new_leaf_proof, new_leaf_proof_helper) =
            tree.insert_leaf(&mut native_hasher, new_leaf_hash, 1);

        let new_root = tree.get_root();

        base_test().k(19).expect_satisfied(true).run(|ctx, range| {
            let gate = range.gate();
            let mut hasher =
                PoseidonHasher::<Fr, 3, 2>::new(OptimizedPoseidonSpec::new::<8, 57, 0>());
            hasher.initialize_consts(ctx, gate);

            let old_root = ctx.load_witness(old_root);

            let low_leaf = IndexedMerkleTreeLeaf {
                val: ctx.load_witness(idx_low_leaf.val),
                next_val: ctx.load_witness(idx_low_leaf.next_val),
                next_idx: ctx.load_witness(idx_low_leaf.next_idx),
            };

            let low_leaf_proof = low_leaf_proof
                .iter()
                .map(|x| ctx.load_witness(*x))
                .collect::<Vec<_>>();

            let low_leaf_proof_helper = low_leaf_proof_helper
                .iter()
                .map(|x| ctx.load_witness(*x))
                .collect::<Vec<_>>();

            let new_root = ctx.load_witness(new_root);

            let new_leaf = IndexedMerkleTreeLeaf {
                val: ctx.load_witness(nullifier_tree_preimages[1].val),
                next_val: ctx.load_witness(nullifier_tree_preimages[1].next_val),
                next_idx: ctx.load_witness(nullifier_tree_preimages[1].next_idx),
            };

            let new_leaf_proof = new_leaf_proof
                .iter()
                .map(|x| ctx.load_witness(*x))
                .collect::<Vec<_>>();

            let new_leaf_proof_helper = new_leaf_proof_helper
                .iter()
                .map(|x| ctx.load_witness(*x))
                .collect::<Vec<_>>();

            let new_leaf_index = ctx.load_witness(Fr::from(1));

            insert_leaf::<Fr, 3, 2>(
                ctx,
                range,
                &hasher,
                &old_root,
                &low_leaf,
                &low_leaf_proof,
                &low_leaf_proof_helper,
                &new_root,
                &new_leaf,
                &new_leaf_index,
                &new_leaf_proof,
                &new_leaf_proof_helper,
            )
        });
    }
    #[test]
    fn test_limbs_logic() {
        let mut rng = thread_rng();

        for _ in 0..10000000 {
            let a_be = rng.gen_biguint(254);
            let b_be = rng.gen_biguint(254);

            let pow_128: BigUint = BigUint::one() << 128;
            let a_q = a_be.clone() / pow_128.clone();
            let a_r = a_be.clone() % pow_128.clone();

            let b_q = b_be.clone() / pow_128.clone();
            let b_r = b_be.clone() % pow_128.clone();

            let is_b_msb_gr = a_q < b_q;
            let are_msb_eq = a_q == b_q;

            let is_b_lsb_gr = a_r < b_r;
            let are_lsb_eq = a_r == b_q;

            let a = is_b_msb_gr;
            let c_not = !are_msb_eq;
            let a_not = !a;
            let b = is_b_lsb_gr;
            let c = !c_not;
            let d_not = !are_lsb_eq;

            let rhs = a_not & b & c & d_not;
            let lhs = a & c_not;
            assert_eq!(a_be < b_be, lhs | rhs);
        }
    }
    #[test]
    fn test_insert_leaf_multiple_round() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        let depth = 30;
        let new_vals = [
            Fr::from(74),
            Fr::from(58),
            Fr::from(77),
            Fr::from(95),
            Fr::from(60),
            Fr::from(9),
            Fr::from(79),
            Fr::from(10),
            Fr::from(30),
            Fr::from(57),
            Fr::from(56),
            Fr::from(51),
            Fr::from(44),
            Fr::from(11),
            Fr::from(1),
            Fr::from(22),
            Fr::from(55),
            Fr::from(13),
            Fr::from(90),
            Fr::from(26),
        ];

        let mut native_hasher = Poseidon::<Fr, T, RATE>::new(R_F, R_P);

        let mut nullifier_tree_preimages = (0..new_vals.len() + 1)
            .map(|_| IMTLeaf {
                val: Fr::from(0u64),
                next_val: Fr::from(0u64),
                next_idx: Fr::from(0u64),
            })
            .collect::<Vec<_>>();

        let mut low_leaf_idx;

        let mut tree = IndexedMerkleTree::<Fr, T, RATE>::new_default_leaf(depth);
        let init_idx_leaf = hash_leaf(&nullifier_tree_preimages[0]);

        tree.insert_leaf(&mut native_hasher, init_idx_leaf, 0);

        for (round, new_val) in new_vals.iter().enumerate() {
            println!("---------------round[{}]----------------", round);

            low_leaf_idx = get_low_leaf_idx(&nullifier_tree_preimages, *new_val);

            let idx_low_leaf = nullifier_tree_preimages[low_leaf_idx].clone();

            let (low_leaf_proof, low_leaf_proof_helper) = tree.get_proof(low_leaf_idx);

            let old_root = tree.get_root();

            update_sparse_idx_leaf(&mut nullifier_tree_preimages, *new_val, (round as u64) + 1);

            let new_low_leaf = hash_leaf(&nullifier_tree_preimages[low_leaf_idx]);

            tree.insert_leaf(&mut native_hasher, new_low_leaf, low_leaf_idx);

            let new_leaf_hash = hash_leaf(&nullifier_tree_preimages[round + 1]);

            let (new_leaf_proof, new_leaf_proof_helper) =
                tree.insert_leaf(&mut native_hasher, new_leaf_hash, round + 1);

            let new_root = tree.get_root();

            base_test()
                .k(19)
                .lookup_bits(18)
                .expect_satisfied(true)
                .run(|ctx, range| {
                    let gate = range.gate();
                    let mut hasher =
                        PoseidonHasher::<Fr, 3, 2>::new(OptimizedPoseidonSpec::new::<8, 57, 0>());
                    hasher.initialize_consts(ctx, gate);

                    let old_root = ctx.load_witness(old_root);

                    let low_leaf = IndexedMerkleTreeLeaf {
                        val: ctx.load_witness(idx_low_leaf.val),
                        next_val: ctx.load_witness(idx_low_leaf.next_val),
                        next_idx: ctx.load_witness(idx_low_leaf.next_idx),
                    };

                    let low_leaf_proof = low_leaf_proof
                        .iter()
                        .map(|x| ctx.load_witness(*x))
                        .collect::<Vec<_>>();

                    let low_leaf_proof_helper = low_leaf_proof_helper
                        .iter()
                        .map(|x| ctx.load_witness(*x))
                        .collect::<Vec<_>>();

                    let new_root = ctx.load_witness(new_root);

                    let new_leaf = IndexedMerkleTreeLeaf {
                        val: ctx.load_witness(*new_val),
                        next_val: ctx.load_witness(nullifier_tree_preimages[round + 1].next_val),
                        next_idx: ctx.load_witness(nullifier_tree_preimages[round + 1].next_idx),
                    };

                    let new_leaf_proof = new_leaf_proof
                        .iter()
                        .map(|x| ctx.load_witness(*x))
                        .collect::<Vec<_>>();

                    let new_leaf_proof_helper = new_leaf_proof_helper
                        .iter()
                        .map(|x| ctx.load_witness(*x))
                        .collect::<Vec<_>>();

                    let new_leaf_index = ctx.load_witness(Fr::from((round + 1) as u64));

                    insert_leaf::<Fr, 3, 2>(
                        ctx,
                        range,
                        &hasher,
                        &old_root,
                        &low_leaf,
                        &low_leaf_proof,
                        &low_leaf_proof_helper,
                        &new_root,
                        &new_leaf,
                        &new_leaf_index,
                        &new_leaf_proof,
                        &new_leaf_proof_helper,
                    )
                });
        }
    }

    fn hash_leaf(leaf: &IMTLeaf<Fr>) -> Fr {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;
        let mut native_hasher = Poseidon::<Fr, T, RATE>::new(R_F, R_P);
        native_hasher.update(&[leaf.val, leaf.next_val, leaf.next_idx]);
        return native_hasher.squeeze_and_reset();
    }

    fn hash_nullifier_pre_images(nullifier_tree_preimages: Vec<IMTLeaf<Fr>>) -> Vec<Fr> {
        let mut native_hasher = Poseidon::<Fr, 3, 2>::new(8, 57);
        nullifier_tree_preimages
            .iter()
            .map(|leaf| {
                native_hasher.update(&[leaf.val, leaf.next_val, leaf.next_idx]);
                native_hasher.squeeze_and_reset()
            })
            .collect::<Vec<_>>()
    }
    fn print_nullifier_leafs(node: Vec<IMTLeaf<Fr>>) {
        for (i, x) in node.iter().enumerate() {
            println!("val[{}]={:?}", i, x.val);
            println!("nxt_idx[{}]={:?}", i, x.next_idx);
            println!("next_val[{}]={:?}\n", i, x.next_val);
        }
    }

    #[test]
    fn test_hash_zero() {
        let mut native_hasher = Poseidon::<Fr, 3, 2>::new(8, 57);
        native_hasher.update(&[Fr::zero(), Fr::zero(), Fr::zero()]);
        println!("hash of zero ={:?}", native_hasher.squeeze_and_reset());
    }
}
