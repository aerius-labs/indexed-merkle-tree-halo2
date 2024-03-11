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

fn verify_merkle_proof<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    root: &AssignedValue<F>,
    leaf: &AssignedValue<F>,
    proof: &[AssignedValue<F>],
    proof_helper: &[AssignedValue<F>],
) {
    let computed_root = compute_merkle_root(ctx, range, hasher, leaf, proof, proof_helper);
    ctx.constrain_equal(&computed_root, root);
}

fn compute_merkle_root<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    leaf: &AssignedValue<F>,
    proof: &[AssignedValue<F>],
    proof_helper: &[AssignedValue<F>],
) -> AssignedValue<F> {
    let gate = range.gate();

    let mut computed_root = ctx.load_witness(*leaf.value());

    for (proof_element, helper) in proof.iter().zip(proof_helper.iter()) {
        let inp = dual_mux(ctx, gate, &computed_root, proof_element, helper);
        computed_root = hasher.hash_fix_len_array(ctx, gate, &inp);
    }

    computed_root
}

fn is_less_than<F:BigPrimeField>(
    gate: &GateChip<F>,
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    a_q:AssignedValue<F>,
    a_r:AssignedValue<F>,
    b_q:AssignedValue<F>,
    b_r:AssignedValue<F>,
)-> AssignedValue<F>{
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
    is_new_leaf_largest: &AssignedValue<F>,
) {
    let gate = range.gate();

    let one = ctx.load_constant(F::ONE);
    let zero = ctx.load_zero();

    let is_zero = gate.is_equal(ctx, low_leaf.next_val, zero);

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

    let is_next_val_greater=is_less_than(gate, ctx, range, nl_q, nl_r, ll_q, ll_r);

    let is_true = select(
        ctx,
        gate,
        one,
        *is_new_leaf_largest,
        is_zero,
        is_next_val_greater,
    );
    assert_eq!(is_true.value(), &F::ONE);
    ctx.constrain_equal(&is_true, &one);

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
    
    let check_less_than=is_less_than(gate, ctx, range, llv_q,llv_r,nl_q, nl_r);
    let one=ctx.load_constant(F::ONE);
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
    is_new_leaf_largest: &AssignedValue<F>,
) {
    let gate = range.gate();

    let zero = ctx.load_zero();

    verify_non_inclusion(
        ctx,
        range,
        hasher,
        old_root,
        low_leaf,
        low_leaf_proof,
        low_leaf_proof_helper,
        &new_leaf.val,
        is_new_leaf_largest,
    );

    let newlowleaf = IndexedMerkleTreeLeaf {
        val: low_leaf.val,
        next_idx: *new_leaf_index,
        next_val: new_leaf.val,
    };

    let new_low_leaf_hash = hasher.hash_fix_len_array(
        ctx,
        gate,
        &[newlowleaf.val, newlowleaf.next_val, newlowleaf.next_idx],
    );

    let interim_root = compute_merkle_root(
        ctx,
        range,
        hasher,
        &new_low_leaf_hash,
        low_leaf_proof,
        low_leaf_proof_helper,
    );

    verify_merkle_proof(
        ctx,
        range,
        hasher,
        &interim_root,
        &zero,
        new_leaf_proof,
        new_leaf_proof_helper,
    );

    ctx.constrain_equal(&new_leaf.next_val, &low_leaf.next_val);
    ctx.constrain_equal(&new_leaf.next_idx, &low_leaf.next_idx);

    let new_leaf_hash = hasher.hash_fix_len_array(
        ctx,
        gate,
        &[new_leaf.val, new_leaf.next_val, new_leaf.next_idx],
    );

    let _new_root = compute_merkle_root(
        ctx,
        range,
        hasher,
        &new_leaf_hash,
        new_leaf_proof,
        new_leaf_proof_helper,
    );
    ctx.constrain_equal(new_root, &_new_root);
}
//TODO
//Update the leaf of the indexed merkle tree

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use ark_std::One;
    use halo2_base::gates::RangeInstructions;
    use halo2_base::poseidon::hasher::PoseidonHasher;
    use halo2_base::utils::testing::base_test;
    use halo2_base::utils::{biguint_to_fe, ScalarField};

    use halo2_base::poseidon::hasher::spec::OptimizedPoseidonSpec;
    use halo2_base::{gates::GateChip, halo2_proofs::halo2curves::grumpkin::Fq as Fr, Context};
    use num_bigint::{BigInt, BigUint, RandBigInt};
    use num_traits::pow;
    use pse_poseidon::Poseidon;
    use rand::thread_rng;

    use crate::indexed_merkle_tree::{insert_leaf, IndexedMerkleTreeLeaf};
    use crate::utils::{IndexedMerkleTree, IndexedMerkleTreeLeaf as IMTLeaf};

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
    fn test_insert_leaf() {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        let tree_size = pow(2, 3);
        let mut leaves = Vec::<Fr>::new();

        let mut native_hasher = Poseidon::<Fr, T, RATE>::new(R_F, R_P);

        // Filling leaves with dfault values.
        for i in 0..tree_size {
            if i == 0 {
                native_hasher.update(&[Fr::from(0u64), Fr::from(0u64), Fr::from(0u64)]);
                leaves.push(native_hasher.squeeze_and_reset());
            } else {
                leaves.push(Fr::from(0u64));
            }
        }
        native_hasher.update(&[Fr::from(187u64)]);
        let new_val = native_hasher.squeeze_and_reset();
        let mut tree =
            IndexedMerkleTree::<Fr, T, RATE>::new(&mut native_hasher, leaves.clone()).unwrap();

        let mut rng = thread_rng();
        let a = rng.gen_biguint(254);
        let r = BigUint::from_str(
            "21888242871839275222246405745257275088548364400416034343698204186575808495617",
        )
        .unwrap();
        println!("a in BigUint={:?}", a);
        let a_gr_b = a > r;
        println!("is a greater than the r ={:?}", a_gr_b);
        let a = a.modpow(&BigUint::one(), &r);
        println!("updated a value={:?}", a);
        let a_fr: Fr = biguint_to_fe(&a);
        println!("a_fr in Fr ={:?}", a_fr);
        let new_val = a_fr;

        println!("new_val = {:?}", new_val);
        let old_root = tree.get_root();
        let low_leaf = IMTLeaf::<Fr> {
            val: Fr::from(0u64),
            next_val: Fr::from(0u64),
            next_idx: Fr::from(0u64),
        };
        let (low_leaf_proof, low_leaf_proof_helper) = tree.get_proof(0);
        assert_eq!(
            tree.verify_proof(&leaves[0], 0, &tree.get_root(), &low_leaf_proof),
            true
        );

        // compute interim state change
        let new_low_leaf = IMTLeaf::<Fr> {
            val: low_leaf.val,
            next_val: new_val,
            next_idx: Fr::from(1u64),
        };
        native_hasher.update(&[
            new_low_leaf.val,
            new_low_leaf.next_val,
            new_low_leaf.next_idx,
        ]);
        leaves[0] = native_hasher.squeeze_and_reset();
        tree = IndexedMerkleTree::<Fr, T, RATE>::new(&mut native_hasher, leaves.clone()).unwrap();
        let (new_leaf_proof, new_leaf_proof_helper) = tree.get_proof(1);
        assert_eq!(
            tree.verify_proof(&leaves[1], 1, &tree.get_root(), &new_leaf_proof),
            true
        );

        native_hasher.update(&[new_val, Fr::from(0u64), Fr::from(0u64)]);
        leaves[1] = native_hasher.squeeze_and_reset();
        tree = IndexedMerkleTree::<Fr, T, RATE>::new(&mut native_hasher, leaves.clone()).unwrap();

        let new_root = tree.get_root();
        let new_leaf = IMTLeaf::<Fr> {
            val: new_val,
            next_val: Fr::from(0u64),
            next_idx: Fr::from(0u64),
        };
        let new_leaf_index = Fr::from(1u64);
        let is_new_leaf_largest = Fr::from(true);

        base_test()
            .k(19)
            .lookup_bits(18)
            .expect_satisfied(true)
            .run(|ctx, range| {
                let gate = range.gate();
                let mut hasher =
                    PoseidonHasher::<Fr, T, RATE>::new(OptimizedPoseidonSpec::new::<R_F, R_P, 0>());
                hasher.initialize_consts(ctx, gate);

                let old_root = ctx.load_witness(old_root);
                let low_leaf = IndexedMerkleTreeLeaf {
                    val: ctx.load_witness(low_leaf.val),
                    next_val: ctx.load_witness(low_leaf.next_val),
                    next_idx: ctx.load_witness(low_leaf.next_idx),
                };
                let new_root = ctx.load_witness(new_root);
                let new_leaf = IndexedMerkleTreeLeaf {
                    val: ctx.load_witness(new_leaf.val),
                    next_val: ctx.load_witness(new_leaf.next_val),
                    next_idx: ctx.load_witness(new_leaf.next_idx),
                };
                let new_leaf_index = ctx.load_witness(new_leaf_index);
                let is_new_leaf_largest = ctx.load_witness(is_new_leaf_largest);

                let low_leaf_proof = low_leaf_proof
                    .iter()
                    .map(|x| ctx.load_witness(*x))
                    .collect::<Vec<_>>();
                let low_leaf_proof_helper = low_leaf_proof_helper
                    .iter()
                    .map(|x| ctx.load_witness(*x))
                    .collect::<Vec<_>>();
                let new_leaf_proof = new_leaf_proof
                    .iter()
                    .map(|x| ctx.load_witness(*x))
                    .collect::<Vec<_>>();
                let new_leaf_proof_helper = new_leaf_proof_helper
                    .iter()
                    .map(|x| ctx.load_witness(*x))
                    .collect::<Vec<_>>();

                insert_leaf::<Fr, T, RATE>(
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
                    &is_new_leaf_largest,
                )
            });
        let next_val_gr = new_val;

        // Inserting a leaf less than largest into the tree
        let new_val = Fr::from(42u64);

        let old_root = tree.get_root();
        let low_leaf = IMTLeaf::<Fr> {
            val: Fr::from(0u64),
            next_val: next_val_gr,
            next_idx: Fr::from(1u64),
        };
        let (low_leaf_proof, low_leaf_proof_helper) = tree.get_proof(0);

        // compute interim state change
        let new_low_leaf = IMTLeaf::<Fr> {
            val: low_leaf.val,
            next_val: new_val,
            next_idx: Fr::from(2u64),
        };
        native_hasher.update(&[
            new_low_leaf.val,
            new_low_leaf.next_val,
            new_low_leaf.next_idx,
        ]);
        leaves[0] = native_hasher.squeeze_and_reset();
        tree = IndexedMerkleTree::<Fr, T, RATE>::new(&mut native_hasher, leaves.clone()).unwrap();
        let (new_leaf_proof, new_leaf_proof_helper) = tree.get_proof(2);
        assert_eq!(
            tree.verify_proof(&leaves[2], 2, &tree.get_root(), &new_leaf_proof),
            true
        );

        native_hasher.update(&[new_val, next_val_gr, Fr::from(1u64)]);
        leaves[2] = native_hasher.squeeze_and_reset();
        tree = IndexedMerkleTree::<Fr, T, RATE>::new(&mut native_hasher, leaves.clone()).unwrap();

        let new_root = tree.get_root();
        let new_leaf = IMTLeaf::<Fr> {
            val: new_val,
            next_val: next_val_gr,
            next_idx: Fr::from(1u64),
        };
        let new_leaf_index = Fr::from(2u64);
        let is_new_leaf_largest = Fr::from(false);

        println!("--------------------------test2----------------------");

        base_test()
            .k(19)
            .lookup_bits(18)
            .expect_satisfied(true)
            .run(|ctx, range| {
                let gate = range.gate();
                let mut hasher =
                    PoseidonHasher::<Fr, T, RATE>::new(OptimizedPoseidonSpec::new::<R_F, R_P, 0>());
                hasher.initialize_consts(ctx, gate);

                let old_root = ctx.load_witness(old_root);
                let low_leaf = IndexedMerkleTreeLeaf {
                    val: ctx.load_witness(low_leaf.val),
                    next_val: ctx.load_witness(low_leaf.next_val),
                    next_idx: ctx.load_witness(low_leaf.next_idx),
                };
                let new_root = ctx.load_witness(new_root);
                let new_leaf = IndexedMerkleTreeLeaf {
                    val: ctx.load_witness(new_leaf.val),
                    next_val: ctx.load_witness(new_leaf.next_val),
                    next_idx: ctx.load_witness(new_leaf.next_idx),
                };
                let new_leaf_index = ctx.load_witness(new_leaf_index);
                let is_new_leaf_largest = ctx.load_witness(is_new_leaf_largest);

                let low_leaf_proof = low_leaf_proof
                    .iter()
                    .map(|x| ctx.load_witness(*x))
                    .collect::<Vec<_>>();
                let low_leaf_proof_helper = low_leaf_proof_helper
                    .iter()
                    .map(|x| ctx.load_witness(*x))
                    .collect::<Vec<_>>();
                let new_leaf_proof = new_leaf_proof
                    .iter()
                    .map(|x| ctx.load_witness(*x))
                    .collect::<Vec<_>>();
                let new_leaf_proof_helper = new_leaf_proof_helper
                    .iter()
                    .map(|x| ctx.load_witness(*x))
                    .collect::<Vec<_>>();

                insert_leaf::<Fr, T, RATE>(
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
                    &is_new_leaf_largest,
                )
            });
    }
    #[test]

    fn test_limbs_logic() {
        let mut rng = thread_rng();

        for _ in 0..10000000 {
            let a = rng.gen_biguint(254);
            let b = rng.gen_biguint(254);

            let pow_128: BigUint = BigUint::one() << 128;
            let a_q = a.clone() / pow_128.clone();
            let a_r = a.clone() % pow_128.clone();

            let b_q = b.clone() / pow_128.clone();
            let b_r = b.clone() % pow_128.clone();

            let mut a_great = true;

            if &a_q > &b_q {
                a_great = true;
            } else if &b_q > &a_q {
                a_great = false;
            } else {
                if &a_r > &b_r {
                    a_great = true;
                } else {
                    a_great = false;
                }
            }
            assert_eq!(a_great, a > b);
        }
    }
}
