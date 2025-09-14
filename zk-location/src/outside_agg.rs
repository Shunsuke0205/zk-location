use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_baby_bear::BabyBear;
use p3_matrix::dense::RowMajorMatrix;

use crate::{Challenger, Dft, MyCompress, MyConfig, MyHash, Perm, Pcs, Val, ValMmcs};
use p3_challenger::DuplexChallenger;
use p3_fri::create_test_fri_params_zk;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_matrix::Matrix;
use rand::rngs::SmallRng;
use rand::SeedableRng;

/// Placeholder aggregator AIR: checks parent = left + right (lane-wise) and enforces C consistency.
/// This is NOT cryptographic; it is to wire the API and tree builder until the recursive verifier is implemented.
#[allow(dead_code)]
pub struct OutsideAggAir;

impl<F: Field> BaseAir<F> for OutsideAggAir { fn width(&self) -> usize { 4 /*left*/ + 4 /*right*/ + 4 /*parent*/ + 4 /*C*/ + 4 /*left_C*/ + 4 /*right_C*/ } }

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for OutsideAggAir
where AB::F: Field + PrimeCharacteristicRing {
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let pvs: Vec<_> = builder.public_values().iter().cloned().collect();
        // Columns
        let base = 0;
        let left = (0..4).map(|i| row.get(0, base + i).unwrap()).collect::<Vec<_>>();
        let right = (0..4).map(|i| row.get(0, base + 4 + i).unwrap()).collect::<Vec<_>>();
        let parent = (0..4).map(|i| row.get(0, base + 8 + i).unwrap()).collect::<Vec<_>>();
        let ccols = (0..4).map(|i| row.get(0, base + 12 + i).unwrap()).collect::<Vec<_>>();
        let left_c = (0..4).map(|i| row.get(0, base + 16 + i).unwrap()).collect::<Vec<_>>();
        let right_c = (0..4).map(|i| row.get(0, base + 20 + i).unwrap()).collect::<Vec<_>>();
        // Bind PVs: [left(4), right(4), parent(4), C(4), left_C(4), right_C(4)]
        if pvs.len() >= 24 { for i in 0..24 { builder.assert_eq(row.get(0, i).unwrap(), pvs[i]); } }
        for i in 0..4 { builder.assert_eq(parent[i].clone(), left[i].clone() + right[i].clone()); }
        for i in 0..4 { builder.assert_eq(left_c[i].clone(), ccols[i].clone()); }
        for i in 0..4 { builder.assert_eq(right_c[i].clone(), ccols[i].clone()); }
    }
}

#[allow(dead_code)]
pub fn build_trace_outside_agg(left: [u32;4], right: [u32;4], c: [u32;4]) -> RowMajorMatrix<BabyBear> {
    let mut row = vec![BabyBear::ZERO; 24];
    const P: u128 = 0x7800_0001;
    #[inline] fn add_p(a: u32, b: u32) -> u32 { let mut s = (a as u128) + (b as u128); if s >= P { s -= P; } s as u32 }
    for i in 0..4 { row[i] = BabyBear::new(left[i]); }
    for i in 0..4 { row[4+i] = BabyBear::new(right[i]); }
    for i in 0..4 { row[8+i] = BabyBear::new(add_p(left[i], right[i])); }
    for i in 0..4 { row[12+i] = BabyBear::new(c[i]); }
    for i in 0..4 { row[16+i] = BabyBear::new(c[i]); }
    for i in 0..4 { row[20+i] = BabyBear::new(c[i]); }
    RowMajorMatrix::new_row(row)
}

#[allow(dead_code)]
pub fn flatten_pv_outside_agg(left: [u32;4], right: [u32;4], parent: [u32;4], c: [u32;4]) -> Vec<Val> {
    let mut out = Vec::with_capacity(24);
    for w in left { out.push(Val::new(w)); }
    for w in right { out.push(Val::new(w)); }
    for w in parent { out.push(Val::new(w)); }
    for w in c { out.push(Val::new(w)); }
    for w in c { out.push(Val::new(w)); } // left_C
    for w in c { out.push(Val::new(w)); } // right_C
    out
}

#[allow(dead_code)]
pub fn prove_outside_agg(left: [u32;4], right: [u32;4], c: [u32;4]) -> p3_uni_stark::Proof<MyConfig> {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = p3_commit::ExtensionMmcs::<_, _, MerkleTreeMmcs<_, _, _, _, 8>>::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger: Challenger = DuplexChallenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    let trace = build_trace_outside_agg(left, right, c);
    const P: u128 = 0x7800_0001;
    #[inline] fn add_p(a: u32, b: u32) -> u32 { let mut s = (a as u128) + (b as u128); if s >= P { s -= P; } s as u32 }
    let parent = [add_p(left[0], right[0]), add_p(left[1], right[1]), add_p(left[2], right[2]), add_p(left[3], right[3])];
    let pvs = flatten_pv_outside_agg(left, right, parent, c);
    p3_uni_stark::prove(&config, &OutsideAggAir, trace, &pvs)
}

#[allow(dead_code)]
pub fn verify_outside_agg(proof: &p3_uni_stark::Proof<MyConfig>, left: [u32;4], right: [u32;4], c: [u32;4]) -> bool {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = p3_commit::ExtensionMmcs::<_, _, MerkleTreeMmcs<_, _, _, _, 8>>::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger: Challenger = DuplexChallenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    const P: u128 = 0x7800_0001;
    #[inline] fn add_p(a: u32, b: u32) -> u32 { let mut s = (a as u128) + (b as u128); if s >= P { s -= P; } s as u32 }
    let parent = [add_p(left[0], right[0]), add_p(left[1], right[1]), add_p(left[2], right[2]), add_p(left[3], right[3])];
    let pvs = flatten_pv_outside_agg(left, right, parent, c);
    p3_uni_stark::verify(&config, &OutsideAggAir, proof, &pvs).is_ok()
}
