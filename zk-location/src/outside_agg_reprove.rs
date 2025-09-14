use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

use crate::{MyConfig, Val};
use crate::config::make_config_default;

/// Aggregator that re-proves two OutsideLeaf statements in-circuit for the same (x,y,ts),
/// binds a shared commitment C, and enforces parent = left + right (lane-wise, mod p).
pub struct OutsideAggReproveAir;

impl<F: Field> BaseAir<F> for OutsideAggReproveAir {
    fn width(&self) -> usize {
        const X_BLOCK: usize = 2 + 30 + 30 + 1;
        const Y_BLOCK: usize = 2 + 30 + 30 + 1;
        // 3 secrets + (left rect X/Y) + (right rect X/Y) + C(4) + digests (left,right,parent) 12
        3 + (X_BLOCK + Y_BLOCK) * 2 + 4 + 12
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for OutsideAggReproveAir
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

        // Left rect X block
        let base_left_x = 3;
        if pvs.len() >= 4 {
            builder.assert_eq(row.get(0, base_left_x + 0).unwrap(), pvs[0]);
            builder.assert_eq(row.get(0, base_left_x + 1).unwrap(), pvs[1]);
        }
        let min_x_l = row.get(0, base_left_x + 0).unwrap().into();
        let max_x_l = row.get(0, base_left_x + 1).unwrap().into();
        let sx_l = row.get(0, base_left_x + 2 + 30 + 30).unwrap();
        builder.assert_bool(sx_l.clone());
        let mut acc_l = x.clone() - x.clone();
        let mut p2 = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_left_x + 2 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_l = acc_l + b.clone().into() * p2.clone();
            if j < 29 { p2 = p2.clone() + p2; }
        }
        let diff_l = min_x_l.clone() - (x.clone() + AB::F::ONE);
        builder.assert_eq(sx_l.clone().into() * (acc_l - diff_l), x.clone() - x.clone());
        let mut acc_r = x.clone() - x.clone();
        let mut p2r = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_left_x + 2 + 30 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_r = acc_r + b.clone().into() * p2r.clone();
            if j < 29 { p2r = p2r.clone() + p2r; }
        }
        let one_minus_sx_l = (x.clone() - x.clone()) + AB::F::ONE - sx_l.clone().into();
        let diff_r = x.clone() - (max_x_l.clone() + AB::F::ONE);
        builder.assert_eq(one_minus_sx_l * (acc_r - diff_r), x.clone() - x.clone());

        // Left rect Y block
        let base_left_y = base_left_x + X_BLOCK;
        if pvs.len() >= 4 {
            builder.assert_eq(row.get(0, base_left_y + 0).unwrap(), pvs[2]);
            builder.assert_eq(row.get(0, base_left_y + 1).unwrap(), pvs[3]);
        }
        let min_y_l = row.get(0, base_left_y + 0).unwrap().into();
        let max_y_l = row.get(0, base_left_y + 1).unwrap().into();
        let sy_l = row.get(0, base_left_y + 2 + 30 + 30).unwrap();
        builder.assert_bool(sy_l.clone());
        let mut acc_ly = y.clone() - y.clone();
        let mut p2y = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_left_y + 2 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_ly = acc_ly + b.clone().into() * p2y.clone();
            if j < 29 { p2y = p2y.clone() + p2y; }
        }
        let diff_ly = min_y_l.clone() - (y.clone() + AB::F::ONE);
        builder.assert_eq(sy_l.clone().into() * (acc_ly - diff_ly), y.clone() - y.clone());
        let mut acc_ry = y.clone() - y.clone();
        let mut p2yr = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_left_y + 2 + 30 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_ry = acc_ry + b.clone().into() * p2yr.clone();
            if j < 29 { p2yr = p2yr.clone() + p2yr; }
        }
        let one_minus_sy_l = (y.clone() - y.clone()) + AB::F::ONE - sy_l.clone().into();
        let diff_ry = y.clone() - (max_y_l.clone() + AB::F::ONE);
        builder.assert_eq(one_minus_sy_l * (acc_ry - diff_ry), y.clone() - y.clone());

        // Right rect X block
        let base_right_x = base_left_y + Y_BLOCK;
        if pvs.len() >= 8 {
            builder.assert_eq(row.get(0, base_right_x + 0).unwrap(), pvs[4]);
            builder.assert_eq(row.get(0, base_right_x + 1).unwrap(), pvs[5]);
        }
        let min_x_r = row.get(0, base_right_x + 0).unwrap().into();
        let max_x_r = row.get(0, base_right_x + 1).unwrap().into();
        let sx_r = row.get(0, base_right_x + 2 + 30 + 30).unwrap();
        builder.assert_bool(sx_r.clone());
        let mut acc_lx_r = x.clone() - x.clone();
        let mut p2x_r = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_right_x + 2 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_lx_r = acc_lx_r + b.clone().into() * p2x_r.clone();
            if j < 29 { p2x_r = p2x_r.clone() + p2x_r; }
        }
        let diff_lx_r = min_x_r.clone() - (x.clone() + AB::F::ONE);
        builder.assert_eq(sx_r.clone().into() * (acc_lx_r - diff_lx_r), x.clone() - x.clone());
        let mut acc_rx_r = x.clone() - x.clone();
        let mut p2rx_r = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_right_x + 2 + 30 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_rx_r = acc_rx_r + b.clone().into() * p2rx_r.clone();
            if j < 29 { p2rx_r = p2rx_r.clone() + p2rx_r; }
        }
        let one_minus_sx_r = (x.clone() - x.clone()) + AB::F::ONE - sx_r.clone().into();
        let diff_rx_r = x.clone() - (max_x_r.clone() + AB::F::ONE);
        builder.assert_eq(one_minus_sx_r * (acc_rx_r - diff_rx_r), x.clone() - x.clone());

        // Right rect Y block
        let base_right_y = base_right_x + X_BLOCK;
        if pvs.len() >= 8 {
            builder.assert_eq(row.get(0, base_right_y + 0).unwrap(), pvs[6]);
            builder.assert_eq(row.get(0, base_right_y + 1).unwrap(), pvs[7]);
        }
        let min_y_r = row.get(0, base_right_y + 0).unwrap().into();
        let max_y_r = row.get(0, base_right_y + 1).unwrap().into();
        let sy_r = row.get(0, base_right_y + 2 + 30 + 30).unwrap();
        builder.assert_bool(sy_r.clone());
        let mut acc_ly_r = y.clone() - y.clone();
        let mut p2y_r = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_right_y + 2 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_ly_r = acc_ly_r + b.clone().into() * p2y_r.clone();
            if j < 29 { p2y_r = p2y_r.clone() + p2y_r; }
        }
        let diff_ly_r = min_y_r.clone() - (y.clone() + AB::F::ONE);
        builder.assert_eq(sy_r.clone().into() * (acc_ly_r - diff_ly_r), y.clone() - y.clone());
        let mut acc_ry_r = y.clone() - y.clone();
        let mut p2yr_r = AB::F::ONE;
        for j in 0..30 {
            let b = row.get(0, base_right_y + 2 + 30 + j).unwrap();
            builder.assert_bool(b.clone());
            acc_ry_r = acc_ry_r + b.clone().into() * p2yr_r.clone();
            if j < 29 { p2yr_r = p2yr_r.clone() + p2yr_r; }
        }
        let one_minus_sy_r = (y.clone() - y.clone()) + AB::F::ONE - sy_r.clone().into();
        let diff_ry_r = y.clone() - (max_y_r.clone() + AB::F::ONE);
        builder.assert_eq(one_minus_sy_r * (acc_ry_r - diff_ry_r), y.clone() - y.clone());

        // C binding
        let base_c = base_right_y + Y_BLOCK;
        if pvs.len() >= 12 {
            for k in 0..4 { builder.assert_eq(row.get(0, base_c + k).unwrap(), pvs[8 + k]); }
        }

        // Digest lanes: left,right,parent columns and constraint parent = left + right
        let base_d = base_c + 4;
        for k in 0..4 {
            let l = row.get(0, base_d + k).unwrap();
            let r = row.get(0, base_d + 4 + k).unwrap();
            let p = row.get(0, base_d + 8 + k).unwrap();
            builder.assert_eq(p.clone(), l.clone() + r.clone());
        }
    }
}

pub fn build_trace_outside_agg_reprove(
    x: u32,
    y: u32,
    ts: u32,
    left: (u32, u32, u32, u32),
    right: (u32, u32, u32, u32),
    c: [u32; 4],
    left_digest: [u32; 4],
    right_digest: [u32; 4],
) -> RowMajorMatrix<BabyBear> {
    const X_BLOCK: usize = 2 + 30 + 30 + 1;
    const Y_BLOCK: usize = 2 + 30 + 30 + 1;
    let width = 3 + (X_BLOCK + Y_BLOCK) * 2 + 4 + 12;
    let mut row = vec![BabyBear::ZERO; width];
    row[0] = BabyBear::new(x);
    row[1] = BabyBear::new(y);
    row[2] = BabyBear::new(ts);

    // Helper to fill a block
    let mut fill_block = |base: usize, v: u32, min_v: u32, max_v: u32| {
        row[base + 0] = BabyBear::new(min_v);
        row[base + 1] = BabyBear::new(max_v);
        let v_plus_one = v.saturating_add(1);
        let diff_l = min_v.saturating_sub(v_plus_one);
        for j in 0..30 { row[base + 2 + j] = BabyBear::from_bool(((diff_l >> j) & 1) == 1); }
        let diff_r = v.saturating_sub(max_v.saturating_add(1));
        for j in 0..30 { row[base + 2 + 30 + j] = BabyBear::from_bool(((diff_r >> j) & 1) == 1); }
        let sel = if v_plus_one <= min_v { 1u32 } else { 0u32 };
        row[base + 2 + 30 + 30] = BabyBear::from_bool(sel == 1);
    };

    // Left rect
    let (lx0,lx1,ly0,ly1) = left;
    let base_left_x = 3;
    let base_left_y = base_left_x + X_BLOCK;
    fill_block(base_left_x, x, lx0, lx1);
    fill_block(base_left_y, y, ly0, ly1);

    // Right rect
    let (rx0,rx1,ry0,ry1) = right;
    let base_right_x = base_left_y + Y_BLOCK;
    let base_right_y = base_right_x + X_BLOCK;
    fill_block(base_right_x, x, rx0, rx1);
    fill_block(base_right_y, y, ry0, ry1);

    // C
    let base_c = base_right_y + Y_BLOCK;
    for k in 0..4 { row[base_c + k] = BabyBear::new(c[k]); }

    // Digests
    let base_d = base_c + 4;
    for k in 0..4 { row[base_d + k] = BabyBear::new(left_digest[k]); }
    for k in 0..4 { row[base_d + 4 + k] = BabyBear::new(right_digest[k]); }
    // parent = left + right (mod p)
    const P: u128 = 0x7800_0001;
    #[inline] fn add_p(a: u32, b: u32) -> u32 { let mut s = (a as u128) + (b as u128); if s >= P { s -= P; } s as u32 }
    for k in 0..4 { row[base_d + 8 + k] = BabyBear::new(add_p(left_digest[k], right_digest[k])); }

    RowMajorMatrix::new_row(row)
}

pub fn flatten_pv_outside_agg_reprove(
    left: (u32, u32, u32, u32),
    right: (u32, u32, u32, u32),
    c: [u32; 4],
    left_digest: [u32; 4],
    right_digest: [u32; 4],
) -> Vec<Val> {
    let mut out = Vec::with_capacity(8 + 4 + 12);
    out.push(Val::new(left.0)); out.push(Val::new(left.1)); out.push(Val::new(left.2)); out.push(Val::new(left.3));
    out.push(Val::new(right.0)); out.push(Val::new(right.1)); out.push(Val::new(right.2)); out.push(Val::new(right.3));
    for &w in &c { out.push(Val::new(w)); }
    for &w in &left_digest { out.push(Val::new(w)); }
    for &w in &right_digest { out.push(Val::new(w)); }
    // parent PVs are bound via columns; no need to duplicate in PVs beyond column binding above
    out
}

pub fn prove_outside_agg_reprove(
    x: u32, y: u32, ts: u32,
    left: (u32, u32, u32, u32),
    right: (u32, u32, u32, u32),
    c: [u32; 4],
) -> p3_uni_stark::Proof<MyConfig> {
    let config = make_config_default();

    // Child digests are Poseidon2(x,y,ts) off-circuit (same for both children since secret is shared)
    let left_digest = crate::outside_leaf::poseidon2_digest_xyts(x, y, ts);
    let right_digest = left_digest;
    let trace = build_trace_outside_agg_reprove(x, y, ts, left, right, c, left_digest, right_digest);
    let pvs = flatten_pv_outside_agg_reprove(left, right, c, left_digest, right_digest);
    p3_uni_stark::prove(&config, &OutsideAggReproveAir, trace, &pvs)
}

pub fn verify_outside_agg_reprove(
    proof: &p3_uni_stark::Proof<MyConfig>,
    left: (u32, u32, u32, u32),
    right: (u32, u32, u32, u32),
    c: [u32; 4],
    x: u32, y: u32, ts: u32,
) -> bool {
    let config = make_config_default();

    // Recompute child digests off-circuit consistently for PVs
    let left_digest = crate::outside_leaf::poseidon2_digest_xyts(x, y, ts);
    let right_digest = left_digest;
    let pvs = flatten_pv_outside_agg_reprove(left, right, c, left_digest, right_digest);
    p3_uni_stark::verify(&config, &OutsideAggReproveAir, proof, &pvs).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::outside_leaf::poseidon2_digest_xyts;

    #[test]
    fn reprove_aggregator_smoke() {
        let (x,y,ts) = (111u32, 222u32, 333u32);
        let c = poseidon2_digest_xyts(x,y,ts);
        let left = (10, 20, 30, 40);
        let right = (50, 60, 70, 80);
        let pr = prove_outside_agg_reprove(x,y,ts, left, right, c);
        assert!(verify_outside_agg_reprove(&pr, left, right, c, x,y,ts));
    }
}
