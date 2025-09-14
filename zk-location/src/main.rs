use p3_field::Field;
use p3_baby_bear::BabyBear;
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix};
use p3_field::PrimeCharacteristicRing; // for ONE constant

// --- Plonky3 proof generation for RangeCheckAirK30 ---
use p3_uni_stark::{prove, verify, StarkConfig};

use p3_baby_bear::{Poseidon2BabyBear};
use p3_field::extension::BinomialExtensionField;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_fri::HidingFriPcs;
use p3_challenger::DuplexChallenger;
use rand::rngs::SmallRng;
// use rand::SeedableRng; // no longer needed here after config refactor
use std::time::Instant;

mod recursive; // scaffolding for recursive aggregation API
mod outside_leaf; // single-rectangle outside leaf
mod outside_agg;  // placeholder digest-only aggregator
mod outside_agg_reprove; // aggregator that re-proves two leaves in-circuit
mod merkle_path; // PoC Merkle path verifier (non-commutative combine)
mod config; // common config helpers (PCS/Challenger/Fri)
mod combine; // shared (a + 2*b)^7 combine utilities



type Val = BabyBear;
type Perm = Poseidon2BabyBear<16>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs = MerkleTreeMmcs<<Val as p3_field::Field>::Packing, <Val as p3_field::Field>::Packing, MyHash, MyCompress, 8>;
type Challenge = BinomialExtensionField<Val, 4>;
type ChallengeMmcs = p3_commit::ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
type Dft = p3_dft::Radix2DitParallel<Val>;
type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, SmallRng>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;



// all the comments should be in English

// --- Micro-degree helpers with unsigned bias (API boundary conversions) ---
// SCALE: 1e6 (micro-degrees)
// Latitude bias: +90_000_000 to map [-90e6, +90e6] -> [0, 180e6] (fits in < 2^28)
// Longitude bias: +180_000_000 to map [-180e6, +180e6] -> [0, 360e6] (fits in < 2^29)
#[allow(dead_code)]
const MICRO_SCALE: i64 = 1_000_000;
#[allow(dead_code)]
const LAT_BIAS: i64 = 90_000_000;
#[allow(dead_code)]
const LON_BIAS: i64 = 180_000_000;

#[allow(dead_code)]
#[inline]
fn lat_deg_to_micro_biased(lat_deg: f64) -> u32 {
    let scaled = (lat_deg * MICRO_SCALE as f64).round() as i64;
    let clamped = scaled.clamp(-LAT_BIAS, LAT_BIAS);
    (clamped + LAT_BIAS) as u32
}

#[allow(dead_code)]
#[inline]
fn lon_deg_to_micro_biased(lon_deg: f64) -> u32 {
    let scaled = (lon_deg * MICRO_SCALE as f64).round() as i64;
    let half_turn = LON_BIAS;
    let clamped = scaled.clamp(-half_turn, half_turn);
    (clamped + LON_BIAS) as u32
}

#[allow(dead_code)]
#[inline]
fn micro_biased_to_lat_deg(micro: u32) -> f64 {
    let signed = micro as i64 - LAT_BIAS;
    (signed as f64) / (MICRO_SCALE as f64)
}

#[allow(dead_code)]
#[inline]
fn micro_biased_to_lon_deg(micro: u32) -> f64 {
    let signed = micro as i64 - LON_BIAS;
    (signed as f64) / (MICRO_SCALE as f64)
}





/// InsideBoxAir: proves (min_x <= x_private <= max_x) && (min_y <= y_private <= max_y) && (min_ts <= ts_private <= max_ts)
/// Each dimension uses RangeCheckAirK30 logic (K=30 bits per diff)
pub struct InsideBoxAir;

impl<F: Field> BaseAir<F> for InsideBoxAir {
    fn width(&self) -> usize {
        // x: 3 + 30 + 30
        // y: 3 + 30 + 30
        // ts: 3 + 30 + 30
        3 * (3 + 30 + 30)
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for InsideBoxAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let pvs_owned: Vec<_> = builder.public_values().iter().cloned().collect();
        // x block
        let x_private = row.get(0, 0).unwrap().into();
        let min_x = row.get(0, 1).unwrap().into();
        let max_x = row.get(0, 2).unwrap().into();
        // y block
        let y_private = row.get(0, 63).unwrap().into();
        let min_y = row.get(0, 64).unwrap().into();
        let max_y = row.get(0, 65).unwrap().into();
        // ts block
        let ts_private = row.get(0, 126).unwrap().into();
        let min_ts = row.get(0, 127).unwrap().into();
        let max_ts = row.get(0, 128).unwrap().into();

        // --- public bindings (if provided) ---
        if pvs_owned.len() >= 6 {
            builder.assert_eq(row.get(0, 1).unwrap(), pvs_owned[0]);
            builder.assert_eq(row.get(0, 2).unwrap(), pvs_owned[1]);
            builder.assert_eq(row.get(0, 64).unwrap(), pvs_owned[2]);
            builder.assert_eq(row.get(0, 65).unwrap(), pvs_owned[3]);
            builder.assert_eq(row.get(0, 127).unwrap(), pvs_owned[4]);
            builder.assert_eq(row.get(0, 128).unwrap(), pvs_owned[5]);
        }

        // --- x range check ---
        let diff1_x = x_private.clone() - min_x.clone();
        let mut acc1_x = diff1_x.clone() - diff1_x.clone(); // ZERO
        let mut pow2_1_x = AB::F::ONE;
        for j in 0..30 {
            let bit_expr = row.get(0, 3 + j).unwrap();
            builder.assert_bool(bit_expr.clone());
            acc1_x = acc1_x + bit_expr.clone().into() * pow2_1_x.clone();
            if j < 29 { pow2_1_x = pow2_1_x.clone() + pow2_1_x; }
        }
        builder.assert_eq(acc1_x, diff1_x);

        let diff2_x = max_x.clone() - x_private.clone();
        let mut acc2_x = diff2_x.clone() - diff2_x.clone(); // ZERO
        let mut pow2_2_x = AB::F::ONE;
        for j in 0..30 {
            let bit_expr = row.get(0, 33 + j).unwrap();
            builder.assert_bool(bit_expr.clone());
            acc2_x = acc2_x + bit_expr.clone().into() * pow2_2_x.clone();
            if j < 29 { pow2_2_x = pow2_2_x.clone() + pow2_2_x; }
        }
        builder.assert_eq(acc2_x, diff2_x);

        // --- y range check ---
        let diff1_y = y_private.clone() - min_y.clone();
        let mut acc1_y = diff1_y.clone() - diff1_y.clone(); // ZERO
        let mut pow2_1_y = AB::F::ONE;
        for j in 0..30 {
            let bit_expr = row.get(0, 66 + j).unwrap();
            builder.assert_bool(bit_expr.clone());
            acc1_y = acc1_y + bit_expr.clone().into() * pow2_1_y.clone();
            if j < 29 { pow2_1_y = pow2_1_y.clone() + pow2_1_y; }
        }
        builder.assert_eq(acc1_y, diff1_y);

        let diff2_y = max_y.clone() - y_private.clone();
        let mut acc2_y = diff2_y.clone() - diff2_y.clone(); // ZERO
        let mut pow2_2_y = AB::F::ONE;
        for j in 0..30 {
            let bit_expr = row.get(0, 96 + j).unwrap();
            builder.assert_bool(bit_expr.clone());
            acc2_y = acc2_y + bit_expr.clone().into() * pow2_2_y.clone();
            if j < 29 { pow2_2_y = pow2_2_y.clone() + pow2_2_y; }
        }
        builder.assert_eq(acc2_y, diff2_y);

        // --- ts range check ---
        let diff1_ts = ts_private.clone() - min_ts.clone();
        let mut acc1_ts = diff1_ts.clone() - diff1_ts.clone(); // ZERO
        let mut pow2_1_ts = AB::F::ONE;
        for j in 0..30 {
            let bit_expr = row.get(0, 129 + j).unwrap();
            builder.assert_bool(bit_expr.clone());
            acc1_ts = acc1_ts + bit_expr.clone().into() * pow2_1_ts.clone();
            if j < 29 { pow2_1_ts = pow2_1_ts.clone() + pow2_1_ts; }
        }
        builder.assert_eq(acc1_ts, diff1_ts);

        let diff2_ts = max_ts.clone() - ts_private.clone();
        let mut acc2_ts = diff2_ts.clone() - diff2_ts.clone(); // ZERO
        let mut pow2_2_ts = AB::F::ONE;
        for j in 0..30 {
            let bit_expr = row.get(0, 159 + j).unwrap();
            builder.assert_bool(bit_expr.clone());
            acc2_ts = acc2_ts + bit_expr.clone().into() * pow2_2_ts.clone();
            if j < 29 { pow2_2_ts = pow2_2_ts.clone() + pow2_2_ts; }
        }
        builder.assert_eq(acc2_ts, diff2_ts);
    }
}





/// OutsideBoxAggregateAir: shared private (x, y, ts) and multiple public claims (min_x,max_x,min_y,max_y) with one global ts range.
/// Proves for each claim i that: (x < min_x_i OR x > max_x_i OR y < min_y_i OR y > max_y_i) AND (min_ts <= ts <= max_ts) with global ts.
/// Implemented as: a per-claim selector t chooses which dimension (X or Y) must be outside; if both are outside either is valid.
/// Layout (single-row trace):
/// - cols 0..2: [x_priv, y_priv, ts_priv]
/// - per claim i (order: t, X block, Y block, then TS block):
///   t: 1 bit selecting which dimension to enforce as outside (1 -> X, 0 -> Y)
///   X block: [min_x, max_x, bits_left[30] for (min_x - (x+1)), bits_right[30] for (x - (max_x+1)), selector_sx]
///   Y block: [min_y, max_y, bits_left[30] for (min_y - (y+1)), bits_right[30] for (y - (max_y+1)), selector_sy]
///   TS block: [min_ts, max_ts, bits_ge_min[30] for (ts - min_ts), bits_le_max[30] for (max_ts - ts)]
/// Public values per claim: [min_x, max_x, min_y, max_y, min_ts, max_ts]
pub struct OutsideBoxAggregateAir { pub n_claims: usize }

impl<F: Field> BaseAir<F> for OutsideBoxAggregateAir {
    fn width(&self) -> usize {
    const CLAIM_SEL: usize = 1; // per-claim OR selector (X vs Y)
    const X_BLOCK: usize = 2 + 30 + 30 + 1; // min,max,bitsL,bitsR,selector
    const Y_BLOCK: usize = 2 + 30 + 30 + 1; // min,max,bitsL,bitsR,selector
    const TS_BLOCK: usize = 2 + 30 + 30; // min,max,bits1,bits2 (GLOBAL)
    3 + TS_BLOCK + self.n_claims * (CLAIM_SEL + X_BLOCK + Y_BLOCK)
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for OutsideBoxAggregateAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let pvs: Vec<_> = builder.public_values().iter().cloned().collect();

        let x_priv = row.get(0, 0).unwrap().into();
        let y_priv = row.get(0, 1).unwrap().into();
        let ts_priv = row.get(0, 2).unwrap().into();

        const CLAIM_SEL: usize = 1;
        const X_BLOCK: usize = 2 + 30 + 30 + 1;
        const Y_BLOCK: usize = 2 + 30 + 30 + 1;
        const TS_BLOCK: usize = 2 + 30 + 30;

        // Global TS block
        let base_ts = 3;
        let min_ts_g = row.get(0, base_ts + 0).unwrap().into();
        let max_ts_g = row.get(0, base_ts + 1).unwrap().into();
        if pvs.len() >= 2 {
            builder.assert_eq(row.get(0, base_ts + 0).unwrap(), pvs[0]);
            builder.assert_eq(row.get(0, base_ts + 1).unwrap(), pvs[1]);
        }
        let mut acc_ts1 = ts_priv.clone() - ts_priv.clone();
        let mut p2t1 = AB::F::ONE;
        for j in 0..30 {
            let bit = row.get(0, base_ts + 2 + j).unwrap();
            builder.assert_bool(bit.clone());
            acc_ts1 = acc_ts1 + bit.clone().into() * p2t1.clone();
            if j < 29 { p2t1 = p2t1.clone() + p2t1; }
        }
        builder.assert_eq(acc_ts1, ts_priv.clone() - min_ts_g.clone());
        let mut acc_ts2 = ts_priv.clone() - ts_priv.clone();
        let mut p2t2 = AB::F::ONE;
        for j in 0..30 {
            let bit = row.get(0, base_ts + 32 + j).unwrap();
            builder.assert_bool(bit.clone());
            acc_ts2 = acc_ts2 + bit.clone().into() * p2t2.clone();
            if j < 29 { p2t2 = p2t2.clone() + p2t2; }
        }
        builder.assert_eq(acc_ts2, max_ts_g.clone() - ts_priv.clone());

        for i in 0..self.n_claims {
            let base = 3 + TS_BLOCK + i * (CLAIM_SEL + X_BLOCK + Y_BLOCK);
            // Claim-level OR selector: t=1 -> enforce X-outside, t=0 -> enforce Y-outside
            let t = row.get(0, base + 0).unwrap();
            builder.assert_bool(t.clone());

            // X block
            let base_x = base + CLAIM_SEL;
            let min_x = row.get(0, base_x + 0).unwrap().into();
            let max_x = row.get(0, base_x + 1).unwrap().into();
            let s = row.get(0, base_x + 2 + 30 + 30).unwrap(); // selector bit at end of X block
            builder.assert_bool(s.clone());

            // Bind PVs if present
            if pvs.len() >= 2 + (i + 1) * 4 {
                builder.assert_eq(row.get(0, base_x + 0).unwrap(), pvs[2 + 4 * i + 0]);
                builder.assert_eq(row.get(0, base_x + 1).unwrap(), pvs[2 + 4 * i + 1]);
            }

            // Prepare 1 as Expr
            let zero_expr = x_priv.clone() - x_priv.clone();
            let one_expr = AB::F::ONE;

            // Compute acc_left = sum bits_left * 2^j for min_x - (x+1)
            let mut acc_left = zero_expr.clone();
            let mut pow2 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_x + 2 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_left = acc_left + bit.clone().into() * pow2.clone();
                if j < 29 { pow2 = pow2.clone() + pow2; }
            }
            // t * s * (min_x - (x+1)) == t * s * acc_left
            let diff_left = min_x.clone() - (x_priv.clone() + one_expr.clone());
            builder.assert_eq(t.clone().into() * s.clone().into() * (acc_left - diff_left), x_priv.clone() - x_priv.clone());

            // Right branch: acc_right = sum bits_right * 2^j for x - (max_x+1)
            let mut acc_right = zero_expr.clone();
            let mut pow2r = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_x + 2 + 30 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_right = acc_right + bit.clone().into() * pow2r.clone();
                if j < 29 { pow2r = pow2r.clone() + pow2r; }
            }
            let one_expr_r = zero_expr.clone() + AB::F::ONE;
            let one_minus_s = one_expr_r.clone() - s.clone().into();
            let diff_right = x_priv.clone() - (max_x.clone() + one_expr_r.clone());
            // t * (1-s) * (x - (max_x+1)) == t * (1-s) * acc_right
            builder.assert_eq(t.clone().into() * one_minus_s.clone() * (acc_right - diff_right), x_priv.clone() - x_priv.clone());

            // Y block
            let base_y = base + CLAIM_SEL + X_BLOCK;
            let min_y = row.get(0, base_y + 0).unwrap().into();
            let max_y = row.get(0, base_y + 1).unwrap().into();
            let sy = row.get(0, base_y + 2 + 30 + 30).unwrap();
            builder.assert_bool(sy.clone());
            if pvs.len() >= 2 + (i + 1) * 4 {
                builder.assert_eq(row.get(0, base_y + 0).unwrap(), pvs[2 + 4 * i + 2]);
                builder.assert_eq(row.get(0, base_y + 1).unwrap(), pvs[2 + 4 * i + 3]);
            }
            // Left branch for y: min_y - (y+1)
            let mut acc_left_y = y_priv.clone() - y_priv.clone();
            let mut pow2y1 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_y + 2 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_left_y = acc_left_y + bit.clone().into() * pow2y1.clone();
                if j < 29 { pow2y1 = pow2y1.clone() + pow2y1; }
            }
            let diff_left_y = min_y.clone() - (y_priv.clone() + AB::F::ONE);
            // (1 - t) * sy * ...
            let zero_expr_y = y_priv.clone() - y_priv.clone();
            let one_expr_y = zero_expr_y.clone() + AB::F::ONE;
            let one_minus_t_y = one_expr_y.clone() - t.clone().into();
            builder.assert_eq(one_minus_t_y.clone() * sy.clone().into() * (acc_left_y - diff_left_y), y_priv.clone() - y_priv.clone());

            // Right branch for y: y - (max_y+1)
            let mut acc_right_y = y_priv.clone() - y_priv.clone();
            let mut pow2y2 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_y + 2 + 30 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_right_y = acc_right_y + bit.clone().into() * pow2y2.clone();
                if j < 29 { pow2y2 = pow2y2.clone() + pow2y2; }
            }
            let one_minus_sy = one_expr_y.clone() - sy.clone().into();
            let diff_right_y = y_priv.clone() - (max_y.clone() + AB::F::ONE);
            // (1 - t) * (1 - sy) * ...
            builder.assert_eq(one_minus_t_y.clone() * one_minus_sy.clone() * (acc_right_y - diff_right_y), y_priv.clone() - y_priv.clone());

        }
    }
}

/// OutsideInsideAggregateAir: shared private (x,y,ts), N outside claims with (x OR y) outside and ts inside,
/// plus one inside claim with (x,y,ts) all inside.
pub struct OutsideInsideAggregateAir { pub n_outside: usize }

impl<F: Field> BaseAir<F> for OutsideInsideAggregateAir {
    fn width(&self) -> usize {
        const CLAIM_SEL: usize = 1;
        const OUTSIDE_X_BLOCK: usize = 2 + 30 + 30 + 1;
        const OUTSIDE_Y_BLOCK: usize = 2 + 30 + 30 + 1;
        const TS_BLOCK: usize = 2 + 30 + 30; // global
        const INSIDE_BLOCK: usize = 2 + 30 + 30; // per dimension (x/y) for inside claim

        3 + TS_BLOCK + self.n_outside * (CLAIM_SEL + OUTSIDE_X_BLOCK + OUTSIDE_Y_BLOCK) + 2 * INSIDE_BLOCK
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for OutsideInsideAggregateAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let pvs: Vec<_> = builder.public_values().iter().cloned().collect();

        let x_priv = row.get(0, 0).unwrap().into();
        let y_priv = row.get(0, 1).unwrap().into();
        let ts_priv = row.get(0, 2).unwrap().into();

        const CLAIM_SEL: usize = 1;
        const X_BLOCK: usize = 2 + 30 + 30 + 1;
        const Y_BLOCK: usize = 2 + 30 + 30 + 1;
        const TS_BLOCK: usize = 2 + 30 + 30;
        const BLOCK_DIM: usize = 2 + 30 + 30;

        // --- Global TS block (shared across outside and inside claims) ---
        let base_ts_global = 3;
        let min_ts_g = row.get(0, base_ts_global + 0).unwrap().into();
        let max_ts_g = row.get(0, base_ts_global + 1).unwrap().into();
        if pvs.len() >= 2 {
            builder.assert_eq(row.get(0, base_ts_global + 0).unwrap(), pvs[0]);
            builder.assert_eq(row.get(0, base_ts_global + 1).unwrap(), pvs[1]);
        }
        // ts - min_ts_g >= 0
        let mut acc_ts1 = ts_priv.clone() - ts_priv.clone();
        let mut p2t1 = AB::F::ONE;
        for j in 0..30 {
            let bit = row.get(0, base_ts_global + 2 + j).unwrap();
            builder.assert_bool(bit.clone());
            acc_ts1 = acc_ts1 + bit.clone().into() * p2t1.clone();
            if j < 29 { p2t1 = p2t1.clone() + p2t1; }
        }
        builder.assert_eq(acc_ts1, ts_priv.clone() - min_ts_g.clone());
        // max_ts_g - ts >= 0
        let mut acc_ts2 = ts_priv.clone() - ts_priv.clone();
        let mut p2t2 = AB::F::ONE;
        for j in 0..30 {
            let bit = row.get(0, base_ts_global + 32 + j).unwrap();
            builder.assert_bool(bit.clone());
            acc_ts2 = acc_ts2 + bit.clone().into() * p2t2.clone();
            if j < 29 { p2t2 = p2t2.clone() + p2t2; }
        }
        builder.assert_eq(acc_ts2, max_ts_g.clone() - ts_priv.clone());

        // Outside claims
        for i in 0..self.n_outside {
            let base = 3 + TS_BLOCK + i * (CLAIM_SEL + X_BLOCK + Y_BLOCK);
            let t = row.get(0, base + 0).unwrap();
            builder.assert_bool(t.clone());

            // X block
            let base_x = base + CLAIM_SEL;
            let min_x = row.get(0, base_x + 0).unwrap().into();
            let max_x = row.get(0, base_x + 1).unwrap().into();
            let sx = row.get(0, base_x + 2 + 30 + 30).unwrap();
            builder.assert_bool(sx.clone());
            if pvs.len() >= 2 + (i + 1) * 4 {
                builder.assert_eq(row.get(0, base_x + 0).unwrap(), pvs[2 + 4 * i + 0]);
                builder.assert_eq(row.get(0, base_x + 1).unwrap(), pvs[2 + 4 * i + 1]);
            }
            let zero = x_priv.clone() - x_priv.clone();
            let mut acc_l = zero.clone();
            let mut p2 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_x + 2 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_l = acc_l + bit.clone().into() * p2.clone();
                if j < 29 { p2 = p2.clone() + p2; }
            }
            let diff_l = min_x.clone() - (x_priv.clone() + AB::F::ONE);
            builder.assert_eq(t.clone().into() * sx.clone().into() * (acc_l - diff_l), zero.clone());
            let mut acc_r = zero.clone();
            let mut p2r = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_x + 2 + 30 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_r = acc_r + bit.clone().into() * p2r.clone();
                if j < 29 { p2r = p2r.clone() + p2r; }
            }
            let one = zero.clone() + AB::F::ONE;
            let one_minus_sx = one.clone() - sx.clone().into();
            let diff_r = x_priv.clone() - (max_x.clone() + one.clone());
            builder.assert_eq(t.clone().into() * one_minus_sx.clone() * (acc_r - diff_r), zero.clone());

            // Y block
            let base_y = base + CLAIM_SEL + X_BLOCK;
            let min_y = row.get(0, base_y + 0).unwrap().into();
            let max_y = row.get(0, base_y + 1).unwrap().into();
            let sy = row.get(0, base_y + 2 + 30 + 30).unwrap();
            builder.assert_bool(sy.clone());
            if pvs.len() >= 2 + (i + 1) * 4 {
                builder.assert_eq(row.get(0, base_y + 0).unwrap(), pvs[2 + 4 * i + 2]);
                builder.assert_eq(row.get(0, base_y + 1).unwrap(), pvs[2 + 4 * i + 3]);
            }
            let mut acc_ly = y_priv.clone() - y_priv.clone();
            let mut p2y1 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_y + 2 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_ly = acc_ly + bit.clone().into() * p2y1.clone();
                if j < 29 { p2y1 = p2y1.clone() + p2y1; }
            }
            let diff_ly = min_y.clone() - (y_priv.clone() + AB::F::ONE);
            let one_minus_t = one.clone() - t.clone().into();
            builder.assert_eq(one_minus_t.clone() * sy.clone().into() * (acc_ly - diff_ly), y_priv.clone() - y_priv.clone());
            let mut acc_ry = y_priv.clone() - y_priv.clone();
            let mut p2y2 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_y + 2 + 30 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_ry = acc_ry + bit.clone().into() * p2y2.clone();
                if j < 29 { p2y2 = p2y2.clone() + p2y2; }
            }
            let one_minus_sy = one.clone() - sy.clone().into();
            let diff_ry = y_priv.clone() - (max_y.clone() + AB::F::ONE);
            builder.assert_eq(one_minus_t.clone() * one_minus_sy.clone() * (acc_ry - diff_ry), y_priv.clone() - y_priv.clone());
        }

        // Inside claim (one), only X and Y blocks (TS enforced globally)
        let base_inside = 3 + TS_BLOCK + self.n_outside * (CLAIM_SEL + X_BLOCK + Y_BLOCK);
        if pvs.len() >= 2 + self.n_outside * 4 + 4 {
            builder.assert_eq(row.get(0, base_inside + 0).unwrap(), pvs[2 + self.n_outside * 4 + 0]);
            builder.assert_eq(row.get(0, base_inside + 1).unwrap(), pvs[2 + self.n_outside * 4 + 1]);
            builder.assert_eq(row.get(0, base_inside + BLOCK_DIM + 0).unwrap(), pvs[2 + self.n_outside * 4 + 2]);
            builder.assert_eq(row.get(0, base_inside + BLOCK_DIM + 1).unwrap(), pvs[2 + self.n_outside * 4 + 3]);
        }

        // X inside
        let min_x_in = row.get(0, base_inside + 0).unwrap().into();
        let max_x_in = row.get(0, base_inside + 1).unwrap().into();
        let mut acc1_x = x_priv.clone() - x_priv.clone();
        let mut p2x1 = AB::F::ONE;
        for j in 0..30 {
            let bit = row.get(0, base_inside + 2 + j).unwrap();
            builder.assert_bool(bit.clone());
            acc1_x = acc1_x + bit.clone().into() * p2x1.clone();
            if j < 29 { p2x1 = p2x1.clone() + p2x1; }
        }
        builder.assert_eq(acc1_x, x_priv.clone() - min_x_in.clone());
        let mut acc2_x = x_priv.clone() - x_priv.clone();
        let mut p2x2 = AB::F::ONE;
        for j in 0..30 {
            let bit = row.get(0, base_inside + 32 + j).unwrap();
            builder.assert_bool(bit.clone());
            acc2_x = acc2_x + bit.clone().into() * p2x2.clone();
            if j < 29 { p2x2 = p2x2.clone() + p2x2; }
        }
        builder.assert_eq(acc2_x, max_x_in.clone() - x_priv.clone());

        // Y inside
        let base_in_y = base_inside + BLOCK_DIM;
        let min_y_in = row.get(0, base_in_y + 0).unwrap().into();
        let max_y_in = row.get(0, base_in_y + 1).unwrap().into();
        let mut acc1_y = y_priv.clone() - y_priv.clone();
        let mut p2y1b = AB::F::ONE;
        for j in 0..30 {
            let bit = row.get(0, base_in_y + 2 + j).unwrap();
            builder.assert_bool(bit.clone());
            acc1_y = acc1_y + bit.clone().into() * p2y1b.clone();
            if j < 29 { p2y1b = p2y1b.clone() + p2y1b; }
        }
        builder.assert_eq(acc1_y, y_priv.clone() - min_y_in.clone());
        let mut acc2_y = y_priv.clone() - y_priv.clone();
        let mut p2y2b = AB::F::ONE;
        for j in 0..30 {
            let bit = row.get(0, base_in_y + 32 + j).unwrap();
            builder.assert_bool(bit.clone());
            acc2_y = acc2_y + bit.clone().into() * p2y2b.clone();
            if j < 29 { p2y2b = p2y2b.clone() + p2y2b; }
        }
        builder.assert_eq(acc2_y, max_y_in.clone() - y_priv.clone());
    }
}

/// Build a single-row trace for OutsideInsideAggregateAir
fn build_trace_outside_inside_shared_private(
    x_private: u32,
    y_private: u32,
    ts_private: u32,
    global_ts: (u32, u32),
    outside_claims: &[(u32, u32, u32, u32)],
    inside_claim: (u32, u32, u32, u32),
) -> RowMajorMatrix<BabyBear> {
    const CLAIM_SEL: usize = 1;
    const X_BLOCK: usize = 2 + 30 + 30 + 1;
    const Y_BLOCK: usize = 2 + 30 + 30 + 1;
    const TS_BLOCK: usize = 2 + 30 + 30; // global
    const BLOCK_DIM: usize = 2 + 30 + 30; // for x and y inside

    let n = outside_claims.len();
    let width = 3 + TS_BLOCK + n * (CLAIM_SEL + X_BLOCK + Y_BLOCK) + 2 * BLOCK_DIM;
    let mut row = vec![BabyBear::ZERO; width];
    row[0] = BabyBear::new(x_private);
    row[1] = BabyBear::new(y_private);
    row[2] = BabyBear::new(ts_private);

    // Global TS block
    let (min_ts, max_ts) = global_ts;
    let base_ts = 3;
    row[base_ts + 0] = BabyBear::new(min_ts);
    row[base_ts + 1] = BabyBear::new(max_ts);
    let diff_ts1 = ts_private.saturating_sub(min_ts);
    for j in 0..30 { row[base_ts + 2 + j] = BabyBear::from_bool(((diff_ts1 >> j) & 1) == 1); }
    let diff_ts2 = max_ts.saturating_sub(ts_private);
    for j in 0..30 { row[base_ts + 32 + j] = BabyBear::from_bool(((diff_ts2 >> j) & 1) == 1); }

    // Outside claims
    for (i, &(min_x, max_x, min_y, max_y)) in outside_claims.iter().enumerate() {
        let base = 3 + TS_BLOCK + i * (CLAIM_SEL + X_BLOCK + Y_BLOCK);
        let x_outside = x_private < min_x || x_private > max_x;
        let t_choose_x = if x_outside { 1u32 } else { 0u32 };
        row[base + 0] = BabyBear::from_bool(t_choose_x == 1);

        // X block
        let base_x = base + CLAIM_SEL;
        row[base_x + 0] = BabyBear::new(min_x);
        row[base_x + 1] = BabyBear::new(max_x);
        let x_plus_one = x_private.saturating_add(1);
        let diff_left = min_x.saturating_sub(x_plus_one);
        for j in 0..30 { row[base_x + 2 + j] = BabyBear::from_bool(((diff_left >> j) & 1) == 1); }
        let max_x_plus_one = max_x.saturating_add(1);
        let diff_right = x_private.saturating_sub(max_x_plus_one);
        for j in 0..30 { row[base_x + 2 + 30 + j] = BabyBear::from_bool(((diff_right >> j) & 1) == 1); }
        let sel = if x_plus_one <= min_x { 1u32 } else { 0u32 };
        row[base_x + 2 + 30 + 30] = BabyBear::from_bool(sel == 1);

        // Y block
        let base_y = base + CLAIM_SEL + X_BLOCK;
        row[base_y + 0] = BabyBear::new(min_y);
        row[base_y + 1] = BabyBear::new(max_y);
        let y_plus_one = y_private.saturating_add(1);
        let diff_left_y = min_y.saturating_sub(y_plus_one);
        for j in 0..30 { row[base_y + 2 + j] = BabyBear::from_bool(((diff_left_y >> j) & 1) == 1); }
        let max_y_plus_one = max_y.saturating_add(1);
        let diff_right_y = y_private.saturating_sub(max_y_plus_one);
        for j in 0..30 { row[base_y + 2 + 30 + j] = BabyBear::from_bool(((diff_right_y >> j) & 1) == 1); }
        let sel_y = if y_plus_one <= min_y { 1u32 } else { 0u32 };
        row[base_y + 2 + 30 + 30] = BabyBear::from_bool(sel_y == 1);

    }

    // Inside claim
    let (i_min_x, i_max_x, i_min_y, i_max_y) = inside_claim;
    let base_inside = 3 + TS_BLOCK + outside_claims.len() * (CLAIM_SEL + X_BLOCK + Y_BLOCK);
    // X inside
    row[base_inside + 0] = BabyBear::new(i_min_x);
    row[base_inside + 1] = BabyBear::new(i_max_x);
    let diff1_x = x_private.saturating_sub(i_min_x);
    for j in 0..30 { row[base_inside + 2 + j] = BabyBear::from_bool(((diff1_x >> j) & 1) == 1); }
    let diff2_x = i_max_x.saturating_sub(x_private);
    for j in 0..30 { row[base_inside + 32 + j] = BabyBear::from_bool(((diff2_x >> j) & 1) == 1); }
    // Y inside
    let base_in_y = base_inside + BLOCK_DIM;
    row[base_in_y + 0] = BabyBear::new(i_min_y);
    row[base_in_y + 1] = BabyBear::new(i_max_y);
    let diff1_y = y_private.saturating_sub(i_min_y);
    for j in 0..30 { row[base_in_y + 2 + j] = BabyBear::from_bool(((diff1_y >> j) & 1) == 1); }
    let diff2_y = i_max_y.saturating_sub(y_private);
    for j in 0..30 { row[base_in_y + 32 + j] = BabyBear::from_bool(((diff2_y >> j) & 1) == 1); }

    RowMajorMatrix::new_row(row)
}

fn flatten_public_bounds_outside_inside(
    global_ts: (u32, u32),
    outside_claims: &[(u32, u32, u32, u32)],
    inside_claim: (u32, u32, u32, u32),
) -> Vec<Val> {
    let mut out = Vec::with_capacity(2 + outside_claims.len() * 4 + 4);
    out.push(Val::new(global_ts.0));
    out.push(Val::new(global_ts.1));
    for &(min_x, max_x, min_y, max_y) in outside_claims {
        out.push(Val::new(min_x));
        out.push(Val::new(max_x));
        out.push(Val::new(min_y));
        out.push(Val::new(max_y));
    }
    let (ix0, ix1, iy0, iy1) = inside_claim;
    out.push(Val::new(ix0)); out.push(Val::new(ix1));
    out.push(Val::new(iy0)); out.push(Val::new(iy1));
    out
}

fn prove_outside_inside_shared_private_aggregate(
    x_private: u32,
    y_private: u32,
    ts_private: u32,
    global_ts: (u32, u32),
    outside_claims: &[(u32, u32, u32, u32)],
    inside_claim: (u32, u32, u32, u32),
) -> p3_uni_stark::Proof<MyConfig> {
    // Setup Plonky3 config (ZK PCS)
    let config = crate::config::make_config_default();

    let trace = build_trace_outside_inside_shared_private(x_private, y_private, ts_private, global_ts, outside_claims, inside_claim);
    let public_values = flatten_public_bounds_outside_inside(global_ts, outside_claims, inside_claim);
    let air = OutsideInsideAggregateAir { n_outside: outside_claims.len() };
    prove(&config, &air, trace, &public_values)
}

fn verify_outside_inside_shared_private_aggregate(
    proof: &p3_uni_stark::Proof<MyConfig>,
    global_ts: (u32, u32),
    outside_claims: &[(u32, u32, u32, u32)],
    inside_claim: (u32, u32, u32, u32),
) -> bool {
    // Setup Plonky3 config (ZK PCS)
    let config = crate::config::make_config_default();

    let public_values = flatten_public_bounds_outside_inside(global_ts, outside_claims, inside_claim);
    let air = OutsideInsideAggregateAir { n_outside: outside_claims.len() };
    verify(&config, &air, proof, &public_values).is_ok()
}
/// Build a single-row trace for OutsideBoxAggregateAir.
fn build_trace_outside_box_shared_private(
    x_private: u32,
    y_private: u32,
    ts_private: u32,
    global_ts: (u32, u32), // shared ts
    claims: &[(u32, u32, u32, u32)], // (min_x, max_x, min_y, max_y)
) -> RowMajorMatrix<BabyBear> {
    const CLAIM_SEL: usize = 1;
    const X_BLOCK: usize = 2 + 30 + 30 + 1;
    const Y_BLOCK: usize = 2 + 30 + 30 + 1;
    const TS_BLOCK: usize = 2 + 30 + 30; // global
    let n = claims.len();
    let width = 3 + TS_BLOCK + n * (CLAIM_SEL + X_BLOCK + Y_BLOCK);
    let mut row = vec![BabyBear::ZERO; width];
    row[0] = BabyBear::new(x_private);
    row[1] = BabyBear::new(y_private);
    row[2] = BabyBear::new(ts_private);

    // Fill global TS block
    let (min_ts, max_ts) = global_ts;
    let base_ts = 3;
    row[base_ts + 0] = BabyBear::new(min_ts);
    row[base_ts + 1] = BabyBear::new(max_ts);
    let diff_ts1 = ts_private.saturating_sub(min_ts);
    for j in 0..30 { row[base_ts + 2 + j] = BabyBear::from_bool(((diff_ts1 >> j) & 1) == 1); }
    let diff_ts2 = max_ts.saturating_sub(ts_private);
    for j in 0..30 { row[base_ts + 32 + j] = BabyBear::from_bool(((diff_ts2 >> j) & 1) == 1); }

    for (i, &(min_x, max_x, min_y, max_y)) in claims.iter().enumerate() {
        let base = 3 + TS_BLOCK + i * (CLAIM_SEL + X_BLOCK + Y_BLOCK);

        // Choose which dimension to use to satisfy outside: prefer X if outside; otherwise Y.
        let x_outside = x_private < min_x || x_private > max_x;
    let t_choose_x = if x_outside { 1u32 } else { 0u32 }; // if both outside, X chosen
        // If neither is outside, witness still fills bits for both, but proof will fail due to gating; we set t by preferring X.
        row[base + 0] = BabyBear::from_bool(t_choose_x == 1);

        // X block
        let base_x = base + CLAIM_SEL;
        row[base_x + 0] = BabyBear::new(min_x);
        row[base_x + 1] = BabyBear::new(max_x);
        let x_plus_one = x_private.saturating_add(1);
        let diff_left = min_x.saturating_sub(x_plus_one);
        for j in 0..30 {
            row[base_x + 2 + j] = BabyBear::from_bool(((diff_left >> j) & 1) == 1);
        }
        let max_x_plus_one = max_x.saturating_add(1);
        let diff_right = x_private.saturating_sub(max_x_plus_one);
        for j in 0..30 {
            row[base_x + 2 + 30 + j] = BabyBear::from_bool(((diff_right >> j) & 1) == 1);
        }
        let sel = if x_plus_one <= min_x { 1u32 } else { 0u32 };
        row[base_x + 2 + 30 + 30] = BabyBear::from_bool(sel == 1);

        // Y block
        let base_y = base + CLAIM_SEL + X_BLOCK;
        row[base_y + 0] = BabyBear::new(min_y);
        row[base_y + 1] = BabyBear::new(max_y);
        let y_plus_one = y_private.saturating_add(1);
        let diff_left_y = min_y.saturating_sub(y_plus_one);
        for j in 0..30 {
            row[base_y + 2 + j] = BabyBear::from_bool(((diff_left_y >> j) & 1) == 1);
        }
        let max_y_plus_one = max_y.saturating_add(1);
        let diff_right_y = y_private.saturating_sub(max_y_plus_one);
        for j in 0..30 {
            row[base_y + 2 + 30 + j] = BabyBear::from_bool(((diff_right_y >> j) & 1) == 1);
        }
        let sel_y = if y_plus_one <= min_y { 1u32 } else { 0u32 };
        row[base_y + 2 + 30 + 30] = BabyBear::from_bool(sel_y == 1);
    }

    RowMajorMatrix::new_row(row)
}

fn flatten_public_bounds_outside(global_ts: (u32, u32), claims: &[(u32, u32, u32, u32)]) -> Vec<Val> {
    let mut out = Vec::with_capacity(2 + claims.len() * 4);
    out.push(Val::new(global_ts.0));
    out.push(Val::new(global_ts.1));
    for &(min_x, max_x, min_y, max_y) in claims {
        out.push(Val::new(min_x));
        out.push(Val::new(max_x));
        out.push(Val::new(min_y));
        out.push(Val::new(max_y));
    }
    out
}

fn prove_outside_box_shared_private_aggregate(
    x_private: u32,
    y_private: u32,
    ts_private: u32,
    global_ts: (u32, u32),
    claims: &[(u32, u32, u32, u32)],
) -> p3_uni_stark::Proof<MyConfig> {
    // Setup Plonky3 config (ZK PCS)
    let config = crate::config::make_config_default();

    let trace = build_trace_outside_box_shared_private(x_private, y_private, ts_private, global_ts, claims);
    let public_values = flatten_public_bounds_outside(global_ts, claims);
    let air = OutsideBoxAggregateAir { n_claims: claims.len() };
    prove(&config, &air, trace, &public_values)
}

fn verify_outside_box_shared_private_aggregate(
    proof: &p3_uni_stark::Proof<MyConfig>,
    global_ts: (u32, u32),
    claims: &[(u32, u32, u32, u32)],
) -> bool {
    // Setup Plonky3 config (ZK PCS)
    let config = crate::config::make_config_default();

    let public_values = flatten_public_bounds_outside(global_ts, claims);
    let air = OutsideBoxAggregateAir { n_claims: claims.len() };
    verify(&config, &air, proof, &public_values).is_ok()
}




/// Build a trace for InsideBoxAir with variable height (n_rows >= 1, power of two recommended)
fn build_trace_inside_box_air(
    x_private: u32, min_x: u32, max_x: u32,
    y_private: u32, min_y: u32, max_y: u32,
    ts_private: u32, min_ts: u32, max_ts: u32,
    n_rows: usize
) -> RowMajorMatrix<BabyBear> {
    const BLOCK: usize = 3 + 30 + 30;
    const W: usize = 3 * BLOCK;
    let mut values = Vec::with_capacity(W * n_rows);
    for _ in 0..n_rows {
        let mut row = vec![BabyBear::ZERO; W];
        // x block
        row[0] = BabyBear::new(x_private);
        row[1] = BabyBear::new(min_x);
        row[2] = BabyBear::new(max_x);
        let diff1_x = x_private.saturating_sub(min_x);
        for j in 0..30 {
            let bit = (diff1_x >> j) & 1;
            row[3 + j] = BabyBear::from_bool(bit == 1);
        }
        let diff2_x = max_x.saturating_sub(x_private);
        for j in 0..30 {
            let bit = (diff2_x >> j) & 1;
            row[33 + j] = BabyBear::from_bool(bit == 1);
        }
        // y block
        let base_y = BLOCK;
        row[base_y + 0] = BabyBear::new(y_private);
        row[base_y + 1] = BabyBear::new(min_y);
        row[base_y + 2] = BabyBear::new(max_y);
        let diff1_y = y_private.saturating_sub(min_y);
        for j in 0..30 {
            let bit = (diff1_y >> j) & 1;
            row[base_y + 3 + j] = BabyBear::from_bool(bit == 1);
        }
        let diff2_y = max_y.saturating_sub(y_private);
        for j in 0..30 {
            let bit = (diff2_y >> j) & 1;
            row[base_y + 33 + j] = BabyBear::from_bool(bit == 1);
        }
        // ts block
        let base_ts = 2 * BLOCK;
        row[base_ts + 0] = BabyBear::new(ts_private);
        row[base_ts + 1] = BabyBear::new(min_ts);
        row[base_ts + 2] = BabyBear::new(max_ts);
        let diff1_ts = ts_private.saturating_sub(min_ts);
        for j in 0..30 {
            let bit = (diff1_ts >> j) & 1;
            row[base_ts + 3 + j] = BabyBear::from_bool(bit == 1);
        }
        let diff2_ts = max_ts.saturating_sub(ts_private);
        for j in 0..30 {
            let bit = (diff2_ts >> j) & 1;
            row[base_ts + 33 + j] = BabyBear::from_bool(bit == 1);
        }
        values.extend(row);
    }
    RowMajorMatrix::new(values, W)
}



/// Generate a STARK proof for InsideBoxAir (3D box: x, y, ts)
fn prove_inside_box(
    x_private: u32, min_x: u32, max_x: u32,
    y_private: u32, min_y: u32, max_y: u32,
    ts_private: u32, min_ts: u32, max_ts: u32,
    trace_height: usize,
) -> p3_uni_stark::Proof<MyConfig> {
    // Setup Plonky3 config
    let config = crate::config::make_config_default();

    // Build trace
    let trace = build_trace_inside_box_air(
        x_private, min_x, max_x,
        y_private, min_y, max_y,
        ts_private, min_ts, max_ts,
        trace_height
    );

    // Public values: [min_x, max_x, min_y, max_y, min_ts, max_ts]
    let public_values = vec![
        Val::new(min_x), Val::new(max_x),
        Val::new(min_y), Val::new(max_y),
        Val::new(min_ts), Val::new(max_ts)
    ];

    // Generate proof
    let proof = prove(&config, &InsideBoxAir, trace, &public_values);
    proof
}

/// Verify a STARK proof for InsideBoxAir (3D box: x, y, ts)
fn verify_inside_box(
    proof: &p3_uni_stark::Proof<MyConfig>,
    min_x: u32, max_x: u32,
    min_y: u32, max_y: u32,
    min_ts: u32, max_ts: u32,
) -> bool {
    // Setup Plonky3 config (must match prover)
    let config = crate::config::make_config_default();

    // Public values: [min_x, max_x, min_y, max_y, min_ts, max_ts]
    let public_values = vec![
        Val::new(min_x), Val::new(max_x),
        Val::new(min_y), Val::new(max_y),
        Val::new(min_ts), Val::new(max_ts)
    ];

    // Verify proof
    let result = verify(&config, &InsideBoxAir, proof, &public_values);
    result.is_ok()
}









/// RangeCheckAirK30: proves min_x <= x_private <= max_x using two GteAirK30 constraints.
pub struct RangeCheckAirK30;

impl<F: Field> BaseAir<F> for RangeCheckAirK30 {
    fn width(&self) -> usize {
        // col0: x_private, col1: min_x, col2: max_x
        // col3..32: bits(x_private - min_x) (K=30)
        // col33..62: bits(max_x - x_private) (K=30)
        3 + 30 + 30
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for RangeCheckAirK30
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let pvs_owned: Vec<_> = builder.public_values().iter().cloned().collect();
        let x_private = row.get(0, 0).unwrap().into();
        let min_x = row.get(0, 1).unwrap().into();
        let max_x = row.get(0, 2).unwrap().into();

        // Bind columns to public inputs if provided
        if pvs_owned.len() >= 2 {
            builder.assert_eq(row.get(0, 1).unwrap(), pvs_owned[0]);
            builder.assert_eq(row.get(0, 2).unwrap(), pvs_owned[1]);
        }

        // --- x_private >= min_x ---
        let diff1 = x_private.clone() - min_x.clone();
        let mut acc1 = diff1.clone() - diff1.clone(); // ZERO
        let mut pow2_1 = AB::F::ONE;
        for j in 0..30 {
            let bit_expr = row.get(0, 3 + j).unwrap();
            builder.assert_bool(bit_expr.clone());
            acc1 = acc1 + bit_expr.clone().into() * pow2_1.clone();
            if j < 29 { pow2_1 = pow2_1.clone() + pow2_1; }
        }
        builder.assert_eq(acc1, diff1);

        // --- max_x >= x_private ---
        let diff2 = max_x.clone() - x_private.clone();
        let mut acc2 = diff2.clone() - diff2.clone(); // ZERO
        let mut pow2_2 = AB::F::ONE;
        for j in 0..30 {
            let bit_expr = row.get(0, 33 + j).unwrap();
            builder.assert_bool(bit_expr.clone());
            acc2 = acc2 + bit_expr.clone().into() * pow2_2.clone();
            if j < 29 { pow2_2 = pow2_2.clone() + pow2_2; }
        }
        builder.assert_eq(acc2, diff2);
    }
}



fn main() {
    /* 
    {
        println!("--- Log-depth aggregation demo: 16 leaves -> 8 -> 4 -> 2 -> 1 ---");
        // Shared secret and commitment C
        let (x_priv, y_priv, ts_priv) = (2468u32, 1357u32, 424242u32);
        let c = outside_leaf::poseidon2_digest_xyts(x_priv, y_priv, ts_priv);
        // Prepare 16 rectangles where the point is outside
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
        // Prove/verify all leaves
        let mut all_ok = true;
        for r in rects {
            let p = outside_leaf::prove_outside_leaf(x_priv, y_priv, ts_priv, r);
            all_ok &= outside_leaf::verify_outside_leaf(&p, r, c);
        }
        println!("Leaf verifications (16): {}", all_ok);
        // Compute leaf digest (same for all since secret is the same)
        let d = outside_leaf::poseidon2_digest_xyts(x_priv, y_priv, ts_priv);
        // Level 1: 16 -> 8
        let mut lvl8: [[u32;4]; 8] = [[0;4]; 8];
        let mut ok_lvl8 = true;
        for i in 0..8 {
            let pr = outside_agg::prove_outside_agg(d, d, c);
            ok_lvl8 &= outside_agg::verify_outside_agg(&pr, d, d, c);
            lvl8[i] = outside_agg::combine_digests_mod_p(d, d);
        }
        println!("Level-1 (16->8) aggregations: {}", ok_lvl8);
        // Level 2: 8 -> 4
        let mut lvl4: [[u32;4]; 4] = [[0;4]; 4];
        let mut ok_lvl4 = true;
        for i in 0..4 {
            let left = lvl8[2*i]; let right = lvl8[2*i+1];
            let pr = outside_agg::prove_outside_agg(left, right, c);
            ok_lvl4 &= outside_agg::verify_outside_agg(&pr, left, right, c);
            lvl4[i] = outside_agg::combine_digests_mod_p(left, right);
        }
        println!("Level-2 (8->4) aggregations: {}", ok_lvl4);
        // Level 3: 4 -> 2
        let mut lvl2: [[u32;4]; 2] = [[0;4]; 2];
        let mut ok_lvl2 = true;
        for i in 0..2 {
            let left = lvl4[2*i]; let right = lvl4[2*i+1];
            let pr = outside_agg::prove_outside_agg(left, right, c);
            ok_lvl2 &= outside_agg::verify_outside_agg(&pr, left, right, c);
            lvl2[i] = outside_agg::combine_digests_mod_p(left, right);
        }
        println!("Level-3 (4->2) aggregations: {}", ok_lvl2);
        // Level 4: 2 -> 1
        let left = lvl2[0]; let right = lvl2[1];
        let pr = outside_agg::prove_outside_agg(left, right, c);
        let ok_root = outside_agg::verify_outside_agg(&pr, left, right, c);
        let _root = outside_agg::combine_digests_mod_p(left, right);
        println!("Level-4 (2->1) root: {}", ok_root);
    }
    */
    {
        println!("--- PoC Merkle path verification demo (depth=4, combine: left+3*right mod p) ---");
        // Use the leaf digest of our secret as a leaf
        let (x_priv, y_priv, ts_priv) = (111u32, 222u32, 333u32);
        let leaf = outside_leaf::poseidon2_digest_xyts(x_priv, y_priv, ts_priv);
        // Build a fake path of depth 4 with arbitrary siblings and directions
        let siblings: [[u32;4]; 4] = [
            [1,2,3,4],
            [5,6,7,8],
            [9,10,11,12],
            [13,14,15,16],
        ];
        let dirs: [u32;4] = [0, 1, 0, 1]; // mix of left/right order
        let root = merkle_path::compute_merkle_root_poc(leaf, &siblings, &dirs);
        let t0 = Instant::now();
        let proof = merkle_path::prove_merkle_path(leaf, &siblings, &dirs, root);
        let t_prove = t0.elapsed();
        let t1 = Instant::now();
        let ok = merkle_path::verify_merkle_path(&proof, siblings.len(), root);
        let t_verify = t1.elapsed();
        println!(
            "PoC Merkle path verification: {} (prove: {:?}, verify: {:?})",
            ok, t_prove, t_verify
        );
        assert!(ok, "Merkle PoC verification failed");
    }
    {
        println!("--- Combined Outside+Inside Aggregate demo ---");
        let (x_priv, y_priv, ts_priv) = (42u32, 7u32, 1000u32);
        // Global TS (shared)
        let global_ts = (800u32, 2000u32);
        // Outside claims (x OR y outside)
        let outside = vec![
            (10, 20, 10, 20),  // x right, y below
            (43, 60, 0, 5),    // x left, y above
        ];
        // Inside claim (x,y inside)
        let inside = (0u32, 100u32, 0u32, 50u32);
        let proof = prove_outside_inside_shared_private_aggregate(x_priv, y_priv, ts_priv, global_ts, &outside, inside);
        let ok = verify_outside_inside_shared_private_aggregate(&proof, global_ts, &outside, inside);
        println!("Outside+Inside aggregate verification: {} ({} outside + 1 inside)", ok, outside.len());
    }
    {
        println!("--- Tokyo micro-degree demo: inside rectangle + 6 outside boxes ---");
        // Assume x = longitude (E), y = latitude (N). Convert degrees to micro-biased u32.
        let tokyo_pt_lat = 35.681236_f64; // Tokyo Station
        let tokyo_pt_lon = 139.767125_f64;
        let y_priv = lat_deg_to_micro_biased(tokyo_pt_lat);
        let x_priv = lon_deg_to_micro_biased(tokyo_pt_lon);
        let ts_priv: u32 = 1_700_000_000; // arbitrary timestamp within global range below
        println!(
            "Private point (deg): lon={:.6}, lat={:.6}",
            tokyo_pt_lon, tokyo_pt_lat
        );

        // Define a rectangle that contains mainland Tokyo (approx):
        let lat_min_deg = 35.20; let lat_max_deg = 35.95;
        let lon_min_deg = 139.40; let lon_max_deg = 139.95;
        let y_min = lat_deg_to_micro_biased(lat_min_deg);
        let y_max = lat_deg_to_micro_biased(lat_max_deg);
        let x_min = lon_deg_to_micro_biased(lon_min_deg);
        let x_max = lon_deg_to_micro_biased(lon_max_deg);
        println!(
            "Inside box (deg): lon in [{:.4}, {:.4}], lat in [{:.4}, {:.4}]",
            lon_min_deg, lon_max_deg, lat_min_deg, lat_max_deg
        );

        // Inside proof for Tokyo rectangle (x,y,ts inside)
        let min_ts = 1_600_000_000; let max_ts = 1_800_000_000; // global-ish window
        let proof_inside = prove_inside_box(
            x_priv, x_min, x_max,
            y_priv, y_min, y_max,
            ts_priv, min_ts, max_ts,
            8,
        );
        let ok_inside = verify_inside_box(&proof_inside, x_min, x_max, y_min, y_max, min_ts, max_ts);
        println!("Tokyo inside-rectangle verification: {}", ok_inside);

        // Build 6 outside rectangles that cover the frame outside the Tokyo rectangle.
        // Frame (degrees)
        let frame_lat_min = 34.0; let frame_lat_max = 37.0;
        let frame_lon_min = 138.0; let frame_lon_max = 141.0;
        let eps = 0.01; // 0.01 degree margin
        let north_lat_min = (lat_max_deg + eps).min(frame_lat_max); // north band starts just above tokyo
        let south_lat_max = (lat_min_deg - eps).max(frame_lat_min); // south band ends just below tokyo
        let west_lon_max = (lon_min_deg - eps).max(frame_lon_min);  // west band
        let east_lon_min = (lon_max_deg + eps).min(frame_lon_max);  // east band
        println!("Outside boxes (deg):");
        println!(
            "  North band   lon:[{:.2},{:.2}] lat:[{:.2},{:.2}]",
            frame_lon_min, frame_lon_max, north_lat_min, frame_lat_max
        );
        println!(
            "  South band   lon:[{:.2},{:.2}] lat:[{:.2},{:.2}]",
            frame_lon_min, frame_lon_max, frame_lat_min, south_lat_max
        );
        println!(
            "  West band    lon:[{:.2},{:.2}] lat:[{:.2},{:.2}]",
            frame_lon_min, west_lon_max, lat_min_deg, lat_max_deg
        );
        println!(
            "  East band    lon:[{:.2},{:.2}] lat:[{:.2},{:.2}]",
            east_lon_min, frame_lon_max, lat_min_deg, lat_max_deg
        );
        println!(
            "  NW corner    lon:[{:.2},{:.2}] lat:[{:.2},{:.2}]",
            frame_lon_min, west_lon_max, north_lat_min, frame_lat_max
        );
        println!(
            "  SE corner    lon:[{:.2},{:.2}] lat:[{:.2},{:.2}]",
            east_lon_min, frame_lon_max, frame_lat_min, south_lat_max
        );

        // 6 Outside rectangles (min_x, max_x, min_y, max_y) in biased micro-units
        let (fx_min, fx_max) = (lon_deg_to_micro_biased(frame_lon_min), lon_deg_to_micro_biased(frame_lon_max));
        let (fy_min, fy_max) = (lat_deg_to_micro_biased(frame_lat_min), lat_deg_to_micro_biased(frame_lat_max));
        let (nx_min, nx_max) = (fx_min, fx_max);
        let (ny_min, ny_max) = (lat_deg_to_micro_biased(north_lat_min), fy_max);
        let (sx_min, sx_max) = (fx_min, fx_max);
        let (sy_min, sy_max) = (fy_min, lat_deg_to_micro_biased(south_lat_max));
        let (wx_min, wx_max) = (fx_min, lon_deg_to_micro_biased(west_lon_max));
        let (wy_min, wy_max) = (y_min, y_max);
        let (ex_min, ex_max) = (lon_deg_to_micro_biased(east_lon_min), fx_max);
        let (ey_min, ey_max) = (y_min, y_max);
        // Corners:
        let (nwx_min, nwx_max) = (fx_min, lon_deg_to_micro_biased(west_lon_max));
        let (nwy_min, nwy_max) = (lat_deg_to_micro_biased(north_lat_min), fy_max);
        let (sex_min, sex_max) = (lon_deg_to_micro_biased(east_lon_min), fx_max);
        let (sey_min, sey_max) = (fy_min, lat_deg_to_micro_biased(south_lat_max));

        let outside_boxes: Vec<(u32, u32, u32, u32)> = vec![
            // North band
            (nx_min, nx_max, ny_min, ny_max),
            // South band
            (sx_min, sx_max, sy_min, sy_max),
            // West band
            (wx_min, wx_max, wy_min, wy_max),
            // East band
            (ex_min, ex_max, ey_min, ey_max),
            // Northwest corner
            (nwx_min, nwx_max, nwy_min, nwy_max),
            // Southeast corner
            (sex_min, sex_max, sey_min, sey_max),
        ];

        // Global TS for outside-aggregate
        let global_ts = (min_ts, max_ts);
        let proof_outside = prove_outside_box_shared_private_aggregate(
            x_priv, y_priv, ts_priv, global_ts, &outside_boxes
        );
        let ok_outside = verify_outside_box_shared_private_aggregate(&proof_outside, global_ts, &outside_boxes);
        println!("Tokyo 6-outside-boxes verification: {} ({} boxes)", ok_outside, outside_boxes.len());

        // Combined aggregate (outside OR + inside) using the same rectangles and TS
        let inside_claim = (x_min, x_max, y_min, y_max);
        let proof_combined = prove_outside_inside_shared_private_aggregate(
            x_priv, y_priv, ts_priv, global_ts, &outside_boxes, inside_claim
        );
        let ok_combined = verify_outside_inside_shared_private_aggregate(
            &proof_combined, global_ts, &outside_boxes, inside_claim
        );
        println!(
            "Tokyo combined aggregate verification: {} ({} outside + 1 inside)",
            ok_combined, outside_boxes.len()
        );
    }
    {
        // Optional heavy demo: 2^12 identical OutsideBox claims to test AIR scalability.
        // Enable by setting env RUN_OUTSIDE_4096=1 before running.
        if std::env::var("RUN_OUTSIDE").ok().is_some() {
            println!("--- Large Outside demo: 4096 identical boxes (gated) ---");
            // Reuse Tokyo-like coordinate system (micro-degree biased)
            let tokyo_pt_lat = 35.681236_f64; // Tokyo Station
            let tokyo_pt_lon = 139.767125_f64;
            let y_priv = lat_deg_to_micro_biased(tokyo_pt_lat);
            let x_priv = lon_deg_to_micro_biased(tokyo_pt_lon);
            let ts_priv: u32 = 1_700_000_000;

            // Frame and a single outside rectangle we will replicate 4096 times.
            let frame_lat_max: f64 = 37.0;
            let frame_lon_min: f64 = 138.0; let frame_lon_max: f64 = 141.0;

            // Choose the "north band" rectangle: lat range entirely above the Tokyo inside box, full lon frame.
            let eps: f64 = 0.01; // small margin
            let north_lat_min: f64 = (35.95_f64 + eps).min(frame_lat_max);
            let (fx_min, fx_max) = (lon_deg_to_micro_biased(frame_lon_min), lon_deg_to_micro_biased(frame_lon_max));
            let (ny_min, ny_max) = (lat_deg_to_micro_biased(north_lat_min), lat_deg_to_micro_biased(frame_lat_max));
            let rect_north: (u32, u32, u32, u32) = (fx_min, fx_max, ny_min, ny_max);

            // Global TS range (same as earlier Tokyo demo)
            let min_ts = 1_600_000_000; let max_ts = 1_800_000_000;
            let global_ts = (min_ts, max_ts);

            let shift = std::env::var("RUN_OUTSIDE")
                .ok()
                .and_then(|v| v.parse::<u32>().ok())
                .unwrap_or(0);
            println!("Building 2^{} = {} identical outside boxes", shift, 1<<shift);
            // Build 2^12 identical claims
            let n: usize = 1 << shift;
            let outside_boxes: Vec<(u32, u32, u32, u32)> = vec![rect_north; n];

            // Quick report on trace width to anticipate memory
            const CLAIM_SEL: usize = 1;
            const X_BLOCK: usize = 2 + 30 + 30 + 1;
            const Y_BLOCK: usize = 2 + 30 + 30 + 1;
            const TS_BLOCK: usize = 2 + 30 + 30;
            let width = 3 + TS_BLOCK + n * (CLAIM_SEL + X_BLOCK + Y_BLOCK);
            println!("Trace width ~ {} columns (single row)", width);

            let t0 = Instant::now();
            let proof = prove_outside_box_shared_private_aggregate(
                x_priv, y_priv, ts_priv, global_ts, &outside_boxes
            );
            let t_prove = t0.elapsed();
            let t1 = Instant::now();
            let ok = verify_outside_box_shared_private_aggregate(
                &proof, global_ts, &outside_boxes
            );
            let t_verify = t1.elapsed();
            println!(
                "{}-outside verification: {} (prove: {:?}, verify: {:?})",
                outside_boxes.len(), ok, t_prove, t_verify
            );
        } else {
            println!("--- Skipping large-outside demo (set RUN_OUTSIDE=1 to run) ---");
        }
    }
    // (recursion scaffolding present; demo omitted to avoid feature gating changes)
}
