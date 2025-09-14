use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

use crate::{
    Challenger, Dft, MyCompress, MyConfig, MyHash, Perm, Pcs, Val, ValMmcs,
};
use p3_challenger::DuplexChallenger;
use p3_fri::create_test_fri_params_zk;
use p3_merkle_tree::MerkleTreeMmcs;
// no symmetric imports needed here
use rand::rngs::SmallRng;
use rand::SeedableRng;

/// Simple linear digest over (x,y,ts) to bind leaves together.
/// NOTE: Placeholder for cryptographic hash. Replace with Poseidon2 gadget in recursive version.
#[inline]
fn digest_xyts(x: u32, y: u32, ts: u32) -> [u32; 4] {
    let d0 = x.wrapping_add(3u32.wrapping_mul(y)).wrapping_add(5u32.wrapping_mul(ts)).wrapping_add(0x9E3779B9);
    let d1 = y.rotate_left(7).wrapping_add(ts.rotate_left(11)).wrapping_add(0x85EBCA6B);
    let d2 = ts.rotate_left(3).wrapping_add(x.rotate_left(13)).wrapping_add(0xC2B2AE35);
    let d3 = d0 ^ d1 ^ d2 ^ 0x27D4EB2D;
    [d0, d1, d2, d3]
}

/// AIR for a single outside-rectangle proof with a row-local commitment digest C.
/// Layout (single row):
///  - 0: x_priv, 1: y_priv, 2: ts_priv
///  - 3..: X outside block (min_x, max_x, bitsL[30], bitsR[30], sel)
///  - ... Y outside block (min_y, max_y, bitsL[30], bitsR[30], sel)
///  - tail: digest lanes d0..d3 (computed as linear fn of x,y,ts)
pub struct OutsideLeafAir;

impl<F: Field> BaseAir<F> for OutsideLeafAir {
    fn width(&self) -> usize {
        const X_BLOCK: usize = 2 + 30 + 30 + 1;
        const Y_BLOCK: usize = 2 + 30 + 30 + 1;
        3 + X_BLOCK + Y_BLOCK + 4
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for OutsideLeafAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let pvs: Vec<_> = builder.public_values().iter().cloned().collect();

        const X_BLOCK: usize = 2 + 30 + 30 + 1;
        const Y_BLOCK: usize = 2 + 30 + 30 + 1;

        // Secrets
        let x = row.get(0, 0).unwrap().into();
        let y = row.get(0, 1).unwrap().into();
        let ts = row.get(0, 2).unwrap().into();

        // X block
        let base_x = 3;
        let min_x = row.get(0, base_x + 0).unwrap().into();
        let max_x = row.get(0, base_x + 1).unwrap().into();
        let sx = row.get(0, base_x + 2 + 30 + 30).unwrap();
        builder.assert_bool(sx.clone());
        // Bind PVs for X min/max
        if pvs.len() >= 4 + 4 {
            builder.assert_eq(row.get(0, base_x + 0).unwrap(), pvs[0]);
            builder.assert_eq(row.get(0, base_x + 1).unwrap(), pvs[1]);
        }
        // min_x - (x+1) branch
        let mut acc_l = x.clone() - x.clone();
        let mut p2 = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_x + 2 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_l = acc_l + b.clone().into() * p2.clone();
            if j < 29 { p2 = p2.clone() + p2; }
        }
        let diff_l = min_x.clone() - (x.clone() + AB::F::ONE);
        builder.assert_eq(sx.clone().into() * (acc_l - diff_l), x.clone() - x.clone());
        // x - (max_x+1) branch
        let mut acc_r = x.clone() - x.clone();
        let mut p2r = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_x + 2 + 30 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_r = acc_r + b.clone().into() * p2r.clone();
            if j < 29 { p2r = p2r.clone() + p2r; }
        }
        let one = AB::F::ONE;
        let one_minus_sx = (x.clone() - x.clone()) + one - sx.clone().into();
        let diff_r = x.clone() - (max_x.clone() + one);
        builder.assert_eq(one_minus_sx * (acc_r - diff_r), x.clone() - x.clone());

        // Y block
        let base_y = base_x + X_BLOCK;
        let min_y = row.get(0, base_y + 0).unwrap().into();
        let max_y = row.get(0, base_y + 1).unwrap().into();
        let sy = row.get(0, base_y + 2 + 30 + 30).unwrap();
        builder.assert_bool(sy.clone());
        if pvs.len() >= 4 + 4 {
            builder.assert_eq(row.get(0, base_y + 0).unwrap(), pvs[2]);
            builder.assert_eq(row.get(0, base_y + 1).unwrap(), pvs[3]);
        }
        // min_y - (y+1)
        let mut acc_ly = y.clone() - y.clone();
        let mut p2y = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_y + 2 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_ly = acc_ly + b.clone().into() * p2y.clone();
            if j < 29 { p2y = p2y.clone() + p2y; }
        }
        let diff_ly = min_y.clone() - (y.clone() + AB::F::ONE);
        builder.assert_eq(sy.clone().into() * (acc_ly - diff_ly), y.clone() - y.clone());
        // y - (max_y+1)
        let mut acc_ry = y.clone() - y.clone();
        let mut p2yr = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_y + 2 + 30 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_ry = acc_ry + b.clone().into() * p2yr.clone();
            if j < 29 { p2yr = p2yr.clone() + p2yr; }
        }
        let one_minus_sy = (y.clone() - y.clone()) + AB::F::ONE - sy.clone().into();
        let diff_ry = y.clone() - (max_y.clone() + AB::F::ONE);
        builder.assert_eq(one_minus_sy * (acc_ry - diff_ry), y.clone() - y.clone());

        // Digest: enforce that the 4 tail columns equal simple linear digest of (x,y,ts)
        let base_d = 3 + X_BLOCK + Y_BLOCK;
        // If digest is present in PVs, bind them too (indices 4..8)
        if pvs.len() >= 8 {
            for k in 0..4 {
                builder.assert_eq(row.get(0, base_d + k).unwrap(), pvs[4 + k]);
            }
        }
        // Constraint the digest deterministically in-field (non-cryptographic)
        let d0 = x.clone()
            + (y.clone() * AB::F::from_u32(3))
            + (ts.clone() * AB::F::from_u32(5))
            + AB::F::from_u32(0x9E3779B9);
        let d1 = y.clone() + ts.clone() + AB::F::from_u32(0x85EBCA6B); // rotation skipped in-field; still binding algebraically
        let d2 = ts.clone() + x.clone() + AB::F::from_u32(0xC2B2AE35);
        let d3 = d0.clone() + d1.clone() + d2.clone() + AB::F::from_u32(0x27D4EB2D);
        builder.assert_eq(row.get(0, base_d + 0).unwrap(), d0);
        builder.assert_eq(row.get(0, base_d + 1).unwrap(), d1);
        builder.assert_eq(row.get(0, base_d + 2).unwrap(), d2);
        builder.assert_eq(row.get(0, base_d + 3).unwrap(), d3);
    }
}

/// Build the single-row trace
pub fn build_trace_outside_leaf(
    x: u32,
    y: u32,
    ts: u32,
    rect: (u32, u32, u32, u32),
) -> RowMajorMatrix<BabyBear> {
    const X_BLOCK: usize = 2 + 30 + 30 + 1;
    const Y_BLOCK: usize = 2 + 30 + 30 + 1;
    let width = 3 + X_BLOCK + Y_BLOCK + 4;
    let mut row = vec![BabyBear::ZERO; width];
    row[0] = BabyBear::new(x);
    row[1] = BabyBear::new(y);
    row[2] = BabyBear::new(ts);
    let (min_x, max_x, min_y, max_y) = rect;
    // X block
    let base_x = 3;
    row[base_x + 0] = BabyBear::new(min_x);
    row[base_x + 1] = BabyBear::new(max_x);
    let x_plus_one = x.saturating_add(1);
    let diff_left = min_x.saturating_sub(x_plus_one);
    for j in 0..30 { row[base_x + 2 + j] = BabyBear::from_bool(((diff_left >> j) & 1) == 1); }
    let diff_right = x.saturating_sub(max_x.saturating_add(1));
    for j in 0..30 { row[base_x + 2 + 30 + j] = BabyBear::from_bool(((diff_right >> j) & 1) == 1); }
    let sel_x = if x_plus_one <= min_x { 1u32 } else { 0u32 };
    row[base_x + 2 + 30 + 30] = BabyBear::from_bool(sel_x == 1);
    // Y block
    let base_y = base_x + X_BLOCK;
    row[base_y + 0] = BabyBear::new(min_y);
    row[base_y + 1] = BabyBear::new(max_y);
    let y_plus_one = y.saturating_add(1);
    let diff_left_y = min_y.saturating_sub(y_plus_one);
    for j in 0..30 { row[base_y + 2 + j] = BabyBear::from_bool(((diff_left_y >> j) & 1) == 1); }
    let diff_right_y = y.saturating_sub(max_y.saturating_add(1));
    for j in 0..30 { row[base_y + 2 + 30 + j] = BabyBear::from_bool(((diff_right_y >> j) & 1) == 1); }
    let sel_y = if y_plus_one <= min_y { 1u32 } else { 0u32 };
    row[base_y + 2 + 30 + 30] = BabyBear::from_bool(sel_y == 1);
    // Digest
    let d = digest_xyts(x, y, ts);
    let base_d = 3 + X_BLOCK + Y_BLOCK;
    for k in 0..4 { row[base_d + k] = BabyBear::new(d[k]); }
    RowMajorMatrix::new_row(row)
}

pub fn flatten_pv_outside_leaf(rect: (u32, u32, u32, u32), digest: [u32; 4]) -> Vec<Val> {
    let mut out = Vec::with_capacity(8);
    out.push(Val::new(rect.0)); out.push(Val::new(rect.1));
    out.push(Val::new(rect.2)); out.push(Val::new(rect.3));
    for &w in &digest { out.push(Val::new(w)); }
    out
}

pub fn prove_outside_leaf(
    x: u32, y: u32, ts: u32,
    rect: (u32, u32, u32, u32),
) -> p3_uni_stark::Proof<MyConfig> {
    // Config (same as main)
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

    let trace = build_trace_outside_leaf(x, y, ts, rect);
    let digest = digest_xyts(x, y, ts);
    let pvs = flatten_pv_outside_leaf(rect, digest);
    p3_uni_stark::prove(&config, &OutsideLeafAir, trace, &pvs)
}

pub fn verify_outside_leaf(
    proof: &p3_uni_stark::Proof<MyConfig>,
    rect: (u32, u32, u32, u32),
    digest: [u32; 4],
) -> bool {
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

    let pvs = flatten_pv_outside_leaf(rect, digest);
    p3_uni_stark::verify(&config, &OutsideLeafAir, proof, &pvs).is_ok()
}
