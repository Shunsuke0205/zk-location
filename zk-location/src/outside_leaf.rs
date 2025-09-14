use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_symmetric::Permutation;
use p3_baby_bear::default_babybear_poseidon2_16;

use crate::{MyConfig, Val};
use crate::config::make_config_default;


/// Poseidon2-based 4-lane commitment over (x,y,ts) with a domain tag.
/// This is deterministic and uses BabyBear Poseidon2-16 with fixed constants.
#[inline]
pub fn poseidon2_digest_xyts(x: u32, y: u32, ts: u32) -> [u32; 4] {
    let mut state = [BabyBear::ZERO; 16];
    // Domain separation tag for zk-location v0
    state[0] = BabyBear::from_u32(0x5A5A_AA55);
    state[1] = BabyBear::from_u32(x);
    state[2] = BabyBear::from_u32(y);
    state[3] = BabyBear::from_u32(ts);
    let perm = default_babybear_poseidon2_16();
    let mut st = state;
    perm.permute_mut(&mut st);
    [
        st[0].as_canonical_u64() as u32,
        st[1].as_canonical_u64() as u32,
        st[2].as_canonical_u64() as u32,
        st[3].as_canonical_u64() as u32,
    ]
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
        let _ts = row.get(0, 2).unwrap();

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

        // Digest: bind the 4 tail columns to public values only (computed off-circuit as Poseidon2 digest)
        let base_d = 3 + X_BLOCK + Y_BLOCK;
        if pvs.len() >= 8 {
            for k in 0..4 { builder.assert_eq(row.get(0, base_d + k).unwrap(), pvs[4 + k]); }
        }
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
    // Digest (Poseidon2 commitment)
    let d = poseidon2_digest_xyts(x, y, ts);
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
    // Config
    let config = make_config_default();

    let trace = build_trace_outside_leaf(x, y, ts, rect);
    let digest = poseidon2_digest_xyts(x, y, ts);
    let pvs = flatten_pv_outside_leaf(rect, digest);
    p3_uni_stark::prove(&config, &OutsideLeafAir, trace, &pvs)
}

/// Convenience: prove and return the Poseidon2 digest alongside the proof.
pub fn prove_outside_leaf_with_digest(
    x: u32, y: u32, ts: u32,
    rect: (u32, u32, u32, u32),
) -> (p3_uni_stark::Proof<MyConfig>, [u32; 4]) {
    let config = make_config_default();

    let trace = build_trace_outside_leaf(x, y, ts, rect);
    let digest = poseidon2_digest_xyts(x, y, ts);
    let pvs = flatten_pv_outside_leaf(rect, digest);
    let proof = p3_uni_stark::prove(&config, &OutsideLeafAir, trace, &pvs);
    (proof, digest)
}

pub fn verify_outside_leaf(
    proof: &p3_uni_stark::Proof<MyConfig>,
    rect: (u32, u32, u32, u32),
    digest: [u32; 4],
) -> bool {
    let config = make_config_default();

    let pvs = flatten_pv_outside_leaf(rect, digest);
    p3_uni_stark::verify(&config, &OutsideLeafAir, proof, &pvs).is_ok()
}
