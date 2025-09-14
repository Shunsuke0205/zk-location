use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_baby_bear::BabyBear;
use p3_matrix::dense::RowMajorMatrix;

use crate::{MyConfig, Val};
use crate::combine;
use crate::config::make_config_with_blowup;
use p3_matrix::Matrix;

/// Aggregator AIR: parent lanes are computed via a Poseidon-like combine per lane:
/// parent[i] = (left[i] + 2*right[i])^7 mod p; also enforces C consistency for both children.
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
        // parent = (left + 2*right)^7 lane-wise
        let two = AB::F::ONE + AB::F::ONE;
        for i in 0..4 {
            let mix = left[i].clone() + right[i].clone() * two.clone();
            let x2 = mix.clone() * mix.clone();
            let x4 = x2.clone() * x2.clone();
            let x7 = x4 * x2 * mix;
            builder.assert_eq(parent[i].clone(), x7);
        }
        for i in 0..4 { builder.assert_eq(left_c[i].clone(), ccols[i].clone()); }
        for i in 0..4 { builder.assert_eq(right_c[i].clone(), ccols[i].clone()); }
    }
}

/// Combine two 4-lane digests using BabyBear modulus: (a + 2*b)^7 lane-wise.
pub fn combine_digests_mod_p(left: [u32; 4], right: [u32; 4]) -> [u32; 4] {
    combine::combine_digest(left, right)
}

#[allow(dead_code)]
pub fn build_trace_outside_agg(left: [u32;4], right: [u32;4], c: [u32;4]) -> RowMajorMatrix<BabyBear> {
    let width = 24;
    let mut row = vec![BabyBear::ZERO; width];
    for i in 0..4 { row[i] = BabyBear::new(left[i]); }
    for i in 0..4 { row[4+i] = BabyBear::new(right[i]); }
    let parent = combine_digests_mod_p(left, right);
    for i in 0..4 { row[8+i] = BabyBear::new(parent[i]); }
    for i in 0..4 { row[12+i] = BabyBear::new(c[i]); }
    for i in 0..4 { row[16+i] = BabyBear::new(c[i]); }
    for i in 0..4 { row[20+i] = BabyBear::new(c[i]); }
    // Replicate to a small power-of-two height for LDE domain sizing under degree-7 constraints.
    let height = 8;
    let mut values = Vec::with_capacity(width * height);
    for _ in 0..height { values.extend_from_slice(&row); }
    RowMajorMatrix::new(values, width)
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
    // Use higher blowup to handle degree-7 constraints.
    let config = make_config_with_blowup(6);

    let trace = build_trace_outside_agg(left, right, c);
    let parent = combine_digests_mod_p(left, right);
    let pvs = flatten_pv_outside_agg(left, right, parent, c);
    p3_uni_stark::prove(&config, &OutsideAggAir, trace, &pvs)
}

#[allow(dead_code)]
pub fn verify_outside_agg(proof: &p3_uni_stark::Proof<MyConfig>, left: [u32;4], right: [u32;4], c: [u32;4]) -> bool {
    let config = make_config_with_blowup(6);

    let parent = combine_digests_mod_p(left, right);
    let pvs = flatten_pv_outside_agg(left, right, parent, c);
    p3_uni_stark::verify(&config, &OutsideAggAir, proof, &pvs).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::outside_leaf;

    #[test]
    fn outside_aggregation_16_to_1_smoke() {
        let (x, y, ts) = (2468u32, 1357u32, 424242u32);
        let c = outside_leaf::poseidon2_digest_xyts(x, y, ts);
        let rects: [(u32,u32,u32,u32); 16] = [
            (10, 20, 30, 40),   (50, 60, 70, 80),
            (90, 100, 110, 120),(130, 140, 150, 160),
            (170, 180, 190, 200),(210, 220, 230, 240),
            (250, 260, 270, 280),(290, 300, 310, 320),
            (330, 340, 350, 360),(370, 380, 390, 400),
            (410, 420, 430, 440),(450, 460, 470, 480),
            (490, 500, 510, 520),(530, 540, 550, 560),
            (570, 580, 590, 600),(610, 620, 630, 640),
        ];
        // Prove leaves and verify
        for r in rects { let p = outside_leaf::prove_outside_leaf(x,y,ts,r); assert!(outside_leaf::verify_outside_leaf(&p, r, c)); }
        // Aggregate 16->8->4->2->1 using digest-only aggregator
        let d = outside_leaf::poseidon2_digest_xyts(x, y, ts);
        let mut lvl8 = [[0u32;4]; 8];
        for i in 0..8 { let pr = prove_outside_agg(d, d, c); assert!(verify_outside_agg(&pr, d, d, c)); lvl8[i] = combine_digests_mod_p(d,d); }
        let mut lvl4 = [[0u32;4]; 4];
        for i in 0..4 { let pr = prove_outside_agg(lvl8[2*i], lvl8[2*i+1], c); assert!(verify_outside_agg(&pr, lvl8[2*i], lvl8[2*i+1], c)); lvl4[i] = combine_digests_mod_p(lvl8[2*i], lvl8[2*i+1]); }
        let mut lvl2 = [[0u32;4]; 2];
        for i in 0..2 { let pr = prove_outside_agg(lvl4[2*i], lvl4[2*i+1], c); assert!(verify_outside_agg(&pr, lvl4[2*i], lvl4[2*i+1], c)); lvl2[i] = combine_digests_mod_p(lvl4[2*i], lvl4[2*i+1]); }
        let pr = prove_outside_agg(lvl2[0], lvl2[1], c);
        assert!(verify_outside_agg(&pr, lvl2[0], lvl2[1], c));
    }
}
