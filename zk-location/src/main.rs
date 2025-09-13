use p3_field::Field;
use p3_baby_bear::BabyBear;
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_field::PrimeCharacteristicRing; // for ONE constant

// --- Plonky3 proof generation for RangeCheckAirK30 ---
use p3_uni_stark::{prove, verify, StarkConfig};

use p3_baby_bear::{Poseidon2BabyBear};
use p3_field::extension::BinomialExtensionField;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_fri::{HidingFriPcs, create_test_fri_params_zk};
use p3_challenger::DuplexChallenger;
use rand::rngs::SmallRng;
use rand::SeedableRng;



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



/// Generate a STARK proof for min_x <= x_private <= max_x
fn prove_range_check(
    x_private: u32,
    min_x: u32,
    max_x: u32,
    trace_height: usize,
) -> p3_uni_stark::Proof<MyConfig> {
    // Setup Plonky3 config
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // Build trace with variable height
    let trace = build_trace_range_check_k30_many(x_private, min_x, max_x, trace_height);

    // Public values: [min_x, max_x]
    let public_values = vec![Val::new(min_x), Val::new(max_x)];

    // Generate proof
    let proof = prove(&config, &RangeCheckAirK30, trace, &public_values);
    proof
}


/// Verify a STARK proof for min_x <= x_private <= max_x
fn verify_range_check(
    proof: &p3_uni_stark::Proof<MyConfig>,
    min_x: u32,
    max_x: u32,
) -> bool {
    // Setup Plonky3 config (must match prover)
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // Public values: [min_x, max_x]
    let public_values = vec![Val::new(min_x), Val::new(max_x)];

    // Verify proof
    let result = verify(&config, &RangeCheckAirK30, proof, &public_values);
    result.is_ok()
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





/// InsideBoxAggregateAir: proves a single shared private (x, y, ts) lies inside each of N public boxes.
/// Layout (single-row trace recommended):
/// - cols 0..2: [x_priv, y_priv, ts_priv]
/// - for each claim i in [0..n_claims):
///   - per dimension uses 2 bounds + 30 + 30 bits = 62 columns
///   - order per claim: X block, then Y block, then TS block
/// Public values: concatenation of all per-claim bounds as
///   [min_x0, max_x0, min_y0, max_y0, min_ts0, max_ts0, min_x1, max_x1, ...]
pub struct InsideBoxAggregateAir { pub n_claims: usize }

impl<F: Field> BaseAir<F> for InsideBoxAggregateAir {
    fn width(&self) -> usize {
        const BLOCK_DIM: usize = 2 + 30 + 30; // min,max,bits1[30],bits2[30]
        3 + self.n_claims * 3 * BLOCK_DIM
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for InsideBoxAggregateAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let pvs: Vec<_> = builder.public_values().iter().cloned().collect();
        // Shared private
        let x_priv = row.get(0, 0).unwrap().into();
        let y_priv = row.get(0, 1).unwrap().into();
        let ts_priv = row.get(0, 2).unwrap().into();

        const BLOCK_DIM: usize = 2 + 30 + 30;

        // If public values provided, they should be 6 per claim. We don't assert the length here
        // to avoid depending on field conversions; instead we only bind if enough PVs are present.

        for i in 0..self.n_claims {
            let base_claim = 3 + i * 3 * BLOCK_DIM;

            // --- X dimension ---
            let base_x = base_claim;
            let min_x = row.get(0, base_x + 0).unwrap().into();
            let max_x = row.get(0, base_x + 1).unwrap().into();

            // Bind to public values if provided
            if pvs.len() >= (i + 1) * 6 {
                builder.assert_eq(row.get(0, base_x + 0).unwrap(), pvs[6 * i + 0]);
                builder.assert_eq(row.get(0, base_x + 1).unwrap(), pvs[6 * i + 1]);
            }

            // x_priv >= min_x
            let diff1_x = x_priv.clone() - min_x.clone();
            let mut acc1_x = diff1_x.clone() - diff1_x.clone(); // ZERO
            let mut pow2_1_x = AB::F::ONE;
            for j in 0..30 {
                let bit_expr = row.get(0, base_x + 2 + j).unwrap();
                builder.assert_bool(bit_expr.clone());
                acc1_x = acc1_x + bit_expr.clone().into() * pow2_1_x.clone();
                if j < 29 { pow2_1_x = pow2_1_x.clone() + pow2_1_x; }
            }
            builder.assert_eq(acc1_x, diff1_x);

            // max_x >= x_priv
            let diff2_x = max_x.clone() - x_priv.clone();
            let mut acc2_x = diff2_x.clone() - diff2_x.clone(); // ZERO
            let mut pow2_2_x = AB::F::ONE;
            for j in 0..30 {
                let bit_expr = row.get(0, base_x + 32 + j).unwrap();
                builder.assert_bool(bit_expr.clone());
                acc2_x = acc2_x + bit_expr.clone().into() * pow2_2_x.clone();
                if j < 29 { pow2_2_x = pow2_2_x.clone() + pow2_2_x; }
            }
            builder.assert_eq(acc2_x, diff2_x);

            // --- Y dimension ---
            let base_y = base_claim + BLOCK_DIM;
            let min_y = row.get(0, base_y + 0).unwrap().into();
            let max_y = row.get(0, base_y + 1).unwrap().into();
            if pvs.len() >= (i + 1) * 6 {
                builder.assert_eq(row.get(0, base_y + 0).unwrap(), pvs[6 * i + 2]);
                builder.assert_eq(row.get(0, base_y + 1).unwrap(), pvs[6 * i + 3]);
            }
            let diff1_y = y_priv.clone() - min_y.clone();
            let mut acc1_y = diff1_y.clone() - diff1_y.clone();
            let mut pow2_1_y = AB::F::ONE;
            for j in 0..30 {
                let bit_expr = row.get(0, base_y + 2 + j).unwrap();
                builder.assert_bool(bit_expr.clone());
                acc1_y = acc1_y + bit_expr.clone().into() * pow2_1_y.clone();
                if j < 29 { pow2_1_y = pow2_1_y.clone() + pow2_1_y; }
            }
            builder.assert_eq(acc1_y, diff1_y);

            let diff2_y = max_y.clone() - y_priv.clone();
            let mut acc2_y = diff2_y.clone() - diff2_y.clone();
            let mut pow2_2_y = AB::F::ONE;
            for j in 0..30 {
                let bit_expr = row.get(0, base_y + 32 + j).unwrap();
                builder.assert_bool(bit_expr.clone());
                acc2_y = acc2_y + bit_expr.clone().into() * pow2_2_y.clone();
                if j < 29 { pow2_2_y = pow2_2_y.clone() + pow2_2_y; }
            }
            builder.assert_eq(acc2_y, diff2_y);

            // --- TS dimension ---
            let base_ts = base_claim + 2 * BLOCK_DIM;
            let min_ts = row.get(0, base_ts + 0).unwrap().into();
            let max_ts = row.get(0, base_ts + 1).unwrap().into();
            if pvs.len() >= (i + 1) * 6 {
                builder.assert_eq(row.get(0, base_ts + 0).unwrap(), pvs[6 * i + 4]);
                builder.assert_eq(row.get(0, base_ts + 1).unwrap(), pvs[6 * i + 5]);
            }
            let diff1_ts = ts_priv.clone() - min_ts.clone();
            let mut acc1_ts = diff1_ts.clone() - diff1_ts.clone();
            let mut pow2_1_ts = AB::F::ONE;
            for j in 0..30 {
                let bit_expr = row.get(0, base_ts + 2 + j).unwrap();
                builder.assert_bool(bit_expr.clone());
                acc1_ts = acc1_ts + bit_expr.clone().into() * pow2_1_ts.clone();
                if j < 29 { pow2_1_ts = pow2_1_ts.clone() + pow2_1_ts; }
            }
            builder.assert_eq(acc1_ts, diff1_ts);

            let diff2_ts = max_ts.clone() - ts_priv.clone();
            let mut acc2_ts = diff2_ts.clone() - diff2_ts.clone();
            let mut pow2_2_ts = AB::F::ONE;
            for j in 0..30 {
                let bit_expr = row.get(0, base_ts + 32 + j).unwrap();
                builder.assert_bool(bit_expr.clone());
                acc2_ts = acc2_ts + bit_expr.clone().into() * pow2_2_ts.clone();
                if j < 29 { pow2_2_ts = pow2_2_ts.clone() + pow2_2_ts; }
            }
            builder.assert_eq(acc2_ts, diff2_ts);
        }
    }
}


/// Build a single-row trace for InsideBoxAggregateAir.
/// - shared private: (x, y, ts)
/// - per-claim public bounds: [(min_x, max_x, min_y, max_y, min_ts, max_ts)]
fn build_trace_inside_box_shared_private(
    x_private: u32,
    y_private: u32,
    ts_private: u32,
    claims: &[(u32, u32, u32, u32, u32, u32)],
) -> RowMajorMatrix<BabyBear> {
    const BLOCK_DIM: usize = 2 + 30 + 30; // per dimension
    let n = claims.len();
    let width = 3 + n * 3 * BLOCK_DIM;
    let mut row = vec![BabyBear::ZERO; width];
    // shared private header
    row[0] = BabyBear::new(x_private);
    row[1] = BabyBear::new(y_private);
    row[2] = BabyBear::new(ts_private);

    for (i, &(min_x, max_x, min_y, max_y, min_ts, max_ts)) in claims.iter().enumerate() {
        let base_claim = 3 + i * 3 * BLOCK_DIM;

        // X block
        let base_x = base_claim;
        row[base_x + 0] = BabyBear::new(min_x);
        row[base_x + 1] = BabyBear::new(max_x);
        let diff1_x = x_private.saturating_sub(min_x);
        for j in 0..30 { row[base_x + 2 + j] = BabyBear::from_bool(((diff1_x >> j) & 1) == 1); }
        let diff2_x = max_x.saturating_sub(x_private);
        for j in 0..30 { row[base_x + 32 + j] = BabyBear::from_bool(((diff2_x >> j) & 1) == 1); }

        // Y block
        let base_y = base_claim + BLOCK_DIM;
        row[base_y + 0] = BabyBear::new(min_y);
        row[base_y + 1] = BabyBear::new(max_y);
        let diff1_y = y_private.saturating_sub(min_y);
        for j in 0..30 { row[base_y + 2 + j] = BabyBear::from_bool(((diff1_y >> j) & 1) == 1); }
        let diff2_y = max_y.saturating_sub(y_private);
        for j in 0..30 { row[base_y + 32 + j] = BabyBear::from_bool(((diff2_y >> j) & 1) == 1); }

        // TS block
        let base_ts = base_claim + 2 * BLOCK_DIM;
        row[base_ts + 0] = BabyBear::new(min_ts);
        row[base_ts + 1] = BabyBear::new(max_ts);
        let diff1_ts = ts_private.saturating_sub(min_ts);
        for j in 0..30 { row[base_ts + 2 + j] = BabyBear::from_bool(((diff1_ts >> j) & 1) == 1); }
        let diff2_ts = max_ts.saturating_sub(ts_private);
        for j in 0..30 { row[base_ts + 32 + j] = BabyBear::from_bool(((diff2_ts >> j) & 1) == 1); }
    }

    RowMajorMatrix::new_row(row)
}

/// Helper to flatten public values for aggregate proof in the expected order per-claim.
fn flatten_public_bounds(claims: &[(u32, u32, u32, u32, u32, u32)]) -> Vec<Val> {
    let mut out = Vec::with_capacity(claims.len() * 6);
    for &(min_x, max_x, min_y, max_y, min_ts, max_ts) in claims {
        out.push(Val::new(min_x));
        out.push(Val::new(max_x));
        out.push(Val::new(min_y));
        out.push(Val::new(max_y));
        out.push(Val::new(min_ts));
        out.push(Val::new(max_ts));
    }
    out
}

/// Generate a STARK proof aggregating many InsideBox claims with a shared private input.
fn prove_inside_box_shared_private_aggregate(
    x_private: u32,
    y_private: u32,
    ts_private: u32,
    claims: &[(u32, u32, u32, u32, u32, u32)],
) -> p3_uni_stark::Proof<MyConfig> {
    // Setup Plonky3 config (ZK PCS)
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    let trace = build_trace_inside_box_shared_private(x_private, y_private, ts_private, claims);
    let public_values = flatten_public_bounds(claims);

    let air = InsideBoxAggregateAir { n_claims: claims.len() };
    prove(&config, &air, trace, &public_values)
}

/// Verify a STARK proof for the shared-private aggregate.
fn verify_inside_box_shared_private_aggregate(
    proof: &p3_uni_stark::Proof<MyConfig>,
    claims: &[(u32, u32, u32, u32, u32, u32)],
) -> bool {
    // Setup Plonky3 config (ZK PCS)
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    let public_values = flatten_public_bounds(claims);
    let air = InsideBoxAggregateAir { n_claims: claims.len() };
    verify(&config, &air, proof, &public_values).is_ok()
}



/// OutsideBoxAggregateAir: shared private (x, ts) and multiple public claims (min_x,max_x,min_ts,max_ts).
/// Proves for each claim i that: (x < min_x_i OR x > max_x_i) AND (min_ts_i <= ts <= max_ts_i).
/// Layout (single-row trace):
/// - cols 0..1: [x_priv, ts_priv]
/// - per claim i (order: X block then TS block):
///   X block: [min_x, max_x, bits_left[30] for (min_x - (x+1)), bits_right[30] for (x - (max_x+1)), selector_s]
///   TS block: [min_ts, max_ts, bits_ge_min[30] for (ts - min_ts), bits_le_max[30] for (max_ts - ts)]
/// Public values per claim: [min_x, max_x, min_ts, max_ts]
pub struct OutsideBoxAggregateAir { pub n_claims: usize }

impl<F: Field> BaseAir<F> for OutsideBoxAggregateAir {
    fn width(&self) -> usize {
        const X_BLOCK: usize = 2 + 30 + 30 + 1; // min,max,bitsL,bitsR,selector
        const TS_BLOCK: usize = 2 + 30 + 30; // min,max,bits1,bits2
        2 + self.n_claims * (X_BLOCK + TS_BLOCK)
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
        let ts_priv = row.get(0, 1).unwrap().into();

        const X_BLOCK: usize = 2 + 30 + 30 + 1;
        const TS_BLOCK: usize = 2 + 30 + 30;

        for i in 0..self.n_claims {
            let base = 2 + i * (X_BLOCK + TS_BLOCK);

            // X block
            let min_x = row.get(0, base + 0).unwrap().into();
            let max_x = row.get(0, base + 1).unwrap().into();
            let s = row.get(0, base + 2 + 30 + 30).unwrap(); // selector bit at end of X block
            builder.assert_bool(s.clone());

            // Bind PVs if present
            if pvs.len() >= (i + 1) * 4 {
                builder.assert_eq(row.get(0, base + 0).unwrap(), pvs[4 * i + 0]);
                builder.assert_eq(row.get(0, base + 1).unwrap(), pvs[4 * i + 1]);
            }

            // Prepare 1 as Expr
            let zero_expr = x_priv.clone() - x_priv.clone();
            let one_expr = AB::F::ONE;

            // Compute acc_left = sum bits_left * 2^j for min_x - (x+1)
            let mut acc_left = zero_expr.clone();
            let mut pow2 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base + 2 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_left = acc_left + bit.clone().into() * pow2.clone();
                if j < 29 { pow2 = pow2.clone() + pow2; }
            }
            // s * (min_x - (x+1)) == s * acc_left
            let diff_left = min_x.clone() - (x_priv.clone() + one_expr.clone());
            builder.assert_eq(s.clone().into() * (acc_left - diff_left), x_priv.clone() - x_priv.clone());

            // Right branch: acc_right = sum bits_right * 2^j for x - (max_x+1)
            let mut acc_right = zero_expr.clone();
            let mut pow2r = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base + 2 + 30 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_right = acc_right + bit.clone().into() * pow2r.clone();
                if j < 29 { pow2r = pow2r.clone() + pow2r; }
            }
            let one_expr_r = zero_expr.clone() + AB::F::ONE;
            let one_minus_s = one_expr_r.clone() - s.clone().into();
            let diff_right = x_priv.clone() - (max_x.clone() + one_expr_r.clone());
            builder.assert_eq(one_minus_s.clone() * (acc_right - diff_right), x_priv.clone() - x_priv.clone());

            // TS block
            let base_ts = base + X_BLOCK;
            let min_ts = row.get(0, base_ts + 0).unwrap().into();
            let max_ts = row.get(0, base_ts + 1).unwrap().into();
            if pvs.len() >= (i + 1) * 4 {
                builder.assert_eq(row.get(0, base_ts + 0).unwrap(), pvs[4 * i + 2]);
                builder.assert_eq(row.get(0, base_ts + 1).unwrap(), pvs[4 * i + 3]);
            }

            // ts - min_ts >= 0
            let mut acc_ts1 = ts_priv.clone() - ts_priv.clone();
            let mut pow2t1 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_ts + 2 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_ts1 = acc_ts1 + bit.clone().into() * pow2t1.clone();
                if j < 29 { pow2t1 = pow2t1.clone() + pow2t1; }
            }
            builder.assert_eq(acc_ts1, ts_priv.clone() - min_ts.clone());

            // max_ts - ts >= 0
            let mut acc_ts2 = ts_priv.clone() - ts_priv.clone();
            let mut pow2t2 = AB::F::ONE;
            for j in 0..30 {
                let bit = row.get(0, base_ts + 32 + j).unwrap();
                builder.assert_bool(bit.clone());
                acc_ts2 = acc_ts2 + bit.clone().into() * pow2t2.clone();
                if j < 29 { pow2t2 = pow2t2.clone() + pow2t2; }
            }
            builder.assert_eq(acc_ts2, max_ts.clone() - ts_priv.clone());
        }
    }
}

/// Build a single-row trace for OutsideBoxAggregateAir.
fn build_trace_outside_box_shared_private(
    x_private: u32,
    ts_private: u32,
    claims: &[(u32, u32, u32, u32)], // (min_x, max_x, min_ts, max_ts)
) -> RowMajorMatrix<BabyBear> {
    const X_BLOCK: usize = 2 + 30 + 30 + 1;
    const TS_BLOCK: usize = 2 + 30 + 30;
    let n = claims.len();
    let width = 2 + n * (X_BLOCK + TS_BLOCK);
    let mut row = vec![BabyBear::ZERO; width];
    row[0] = BabyBear::new(x_private);
    row[1] = BabyBear::new(ts_private);

    for (i, &(min_x, max_x, min_ts, max_ts)) in claims.iter().enumerate() {
        let base = 2 + i * (X_BLOCK + TS_BLOCK);
        // X block
        row[base + 0] = BabyBear::new(min_x);
        row[base + 1] = BabyBear::new(max_x);
        let x_plus_one = x_private.saturating_add(1);
        let diff_left = min_x.saturating_sub(x_plus_one);
        for j in 0..30 { row[base + 2 + j] = BabyBear::from_bool(((diff_left >> j) & 1) == 1); }
        let max_x_plus_one = max_x.saturating_add(1);
        let diff_right = x_private.saturating_sub(max_x_plus_one);
        for j in 0..30 { row[base + 2 + 30 + j] = BabyBear::from_bool(((diff_right >> j) & 1) == 1); }
        let sel = if x_plus_one <= min_x { 1u32 } else { 0u32 }; // choose left branch iff x < min_x
        row[base + 2 + 30 + 30] = BabyBear::from_bool(sel == 1);

        // TS block
        let base_ts = base + X_BLOCK;
        row[base_ts + 0] = BabyBear::new(min_ts);
        row[base_ts + 1] = BabyBear::new(max_ts);
        let diff_ts1 = ts_private.saturating_sub(min_ts);
        for j in 0..30 { row[base_ts + 2 + j] = BabyBear::from_bool(((diff_ts1 >> j) & 1) == 1); }
        let diff_ts2 = max_ts.saturating_sub(ts_private);
        for j in 0..30 { row[base_ts + 32 + j] = BabyBear::from_bool(((diff_ts2 >> j) & 1) == 1); }
    }

    RowMajorMatrix::new_row(row)
}

fn flatten_public_bounds_outside(claims: &[(u32, u32, u32, u32)]) -> Vec<Val> {
    let mut out = Vec::with_capacity(claims.len() * 4);
    for &(min_x, max_x, min_ts, max_ts) in claims {
        out.push(Val::new(min_x));
        out.push(Val::new(max_x));
        out.push(Val::new(min_ts));
        out.push(Val::new(max_ts));
    }
    out
}

fn prove_outside_box_shared_private_aggregate(
    x_private: u32,
    ts_private: u32,
    claims: &[(u32, u32, u32, u32)],
) -> p3_uni_stark::Proof<MyConfig> {
    // Setup Plonky3 config (ZK PCS)
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    let trace = build_trace_outside_box_shared_private(x_private, ts_private, claims);
    let public_values = flatten_public_bounds_outside(claims);
    let air = OutsideBoxAggregateAir { n_claims: claims.len() };
    prove(&config, &air, trace, &public_values)
}

fn verify_outside_box_shared_private_aggregate(
    proof: &p3_uni_stark::Proof<MyConfig>,
    claims: &[(u32, u32, u32, u32)],
) -> bool {
    // Setup Plonky3 config (ZK PCS)
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    let public_values = flatten_public_bounds_outside(claims);
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
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

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
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

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
    {
        println!("--- InsideBoxAir: 3D box (x, y, ts) range proof demo ---");
        let x_private = 15;
        let min_x = 10;
        let max_x = 20;
        let y_private = 25;
        let min_y = 20;
        let max_y = 30;
        let ts_private = 1000;
        let min_ts = 900;
        let max_ts = 1100;
        let trace_height = 8;
        let proof = prove_inside_box(
            x_private, min_x, max_x,
            y_private, min_y, max_y,
            ts_private, min_ts, max_ts,
            trace_height,
        );
        println!("InsideBoxAir proof generated for (x={}, y={}, ts={}) in box:", x_private, y_private, ts_private);
        println!("  x in [{} , {}]", min_x, max_x);
        println!("  y in [{} , {}]", min_y, max_y);
        println!("  ts in [{} , {}]", min_ts, max_ts);

        let verified = verify_inside_box(
            &proof,
            min_x, max_x,
            min_y, max_y,
            min_ts, max_ts,
            // log_final_poly_len
        );
        println!("InsideBoxAir proof verification result: {}", verified);
    }

    {
        println!("--- InsideBoxAggregateAir demo: shared private, multiple public boxes ---");
        // Shared private point
        let (x_priv, y_priv, ts_priv) = (15u32, 25u32, 1000u32);
        // Multiple public boxes; each: (min_x, max_x, min_y, max_y, min_ts, max_ts)
        let boxes = vec![
            (10, 20, 20, 30, 900, 1100),
            (14, 16, 24, 30, 950, 1050),
            (0, 100, 10, 40, 800, 2000),
        ];

        let proof = prove_inside_box_shared_private_aggregate(x_priv, y_priv, ts_priv, &boxes);
        let ok = verify_inside_box_shared_private_aggregate(&proof, &boxes);
        println!("InsideBoxAggregateAir verification result: {} ({} boxes)", ok, boxes.len());
    }
    {
         // --- Plonky3 proof generation example ---
        let x_private = 15;
        let min_x = 10;
        let max_x = 20;
        let trace_height = 8; // must be >= 2^log_final_poly_len + blowup
        let proof = prove_range_check(x_private, min_x, max_x, trace_height);
        println!("Plonky3 proof generated for {} in [{} , {}]", x_private, min_x, max_x);

        // --- Plonky3 proof verification example ---
    let verified = verify_range_check(&proof, min_x, max_x);
        println!("Plonky3 proof verification result: {}", verified);
    }
    {
        println!("--- OutsideBoxAggregateAir demo: shared (x,ts), multiple public ranges ---");
        let (x_priv, ts_priv) = (42u32, 1000u32);
        // Each tuple: (min_x, max_x, min_ts, max_ts)
    // Ensure each claim has x outside and ts inside; tweak bounds accordingly
        let claims = vec![
            (10, 20, 900, 1100),   // outside by right
            (43, 60, 950, 1050),   // outside by left (x<min_x)
            (0, 10, 800, 2000),    // outside by right
        ];
        let proof = prove_outside_box_shared_private_aggregate(x_priv, ts_priv, &claims);
        let ok = verify_outside_box_shared_private_aggregate(&proof, &claims);
        println!("OutsideBoxAggregateAir verification result: {} ({} claims)", ok, claims.len());
    }
    #[cfg(not(debug_assertions))]
    {
        // --- Plonky3 proof generation example (failing case) ---
        let x_private = 1000000;
        let min_x = 1000;
        let max_x = 100000;
        let trace_height = 8; // must be >= 2^log_final_poly_len + blowup
        let proof = prove_range_check(x_private, min_x, max_x, trace_height);
        println!("Plonky3 proof generated for {} in [{} , {}]", x_private, min_x, max_x);

        // --- Plonky3 proof verification example (failing case) ---
    let verified = verify_range_check(&proof, min_x, max_x);
        println!("Plonky3 proof verification result: {}", verified);
    }
    #[cfg(not(debug_assertions))]
    {
        // --- Plonky3 proof generation example (failing case) ---
        let x_private = 10;
        let min_x = 1000;
        let max_x = 100000;
        let trace_height = 8; // must be >= 2^log_final_poly_len + blowup
        let proof = prove_range_check(x_private, min_x, max_x, trace_height);
        println!("Plonky3 proof generated for {} in [{} , {}]", x_private, min_x, max_x);

        // --- Plonky3 proof verification example (failing case) ---
    let verified = verify_range_check(&proof, min_x, max_x);
        println!("Plonky3 proof verification result: {}", verified);
    }



    println!("---");
    println!("RangeCheckAirK30: min_x <= x_private <= max_x ---");
    println!("RangeCheck 10 <= 15 <= 20 -> {}", run_range_check_debug(15, 10, 20));
    println!("RangeCheck 10 <= 10 <= 20 -> {}", run_range_check_debug(10, 10, 20));
    println!("RangeCheck 10 <= 20 <= 20 -> {}", run_range_check_debug(20, 10, 20));
    println!("RangeCheck 10 <= 9 <= 20 -> {}", run_range_check_debug(9, 10, 20));
    println!("RangeCheck 10 <= 21 <= 20 -> {}", run_range_check_debug(21, 10, 20));
}


/// Build a single-row trace for RangeCheckAirK30: [x_private, min_x, max_x, bits1, bits2]
fn build_trace_range_check_k30(x_private: u32, min_x: u32, max_x: u32) -> RowMajorMatrix<BabyBear> {
    const W: usize = 3 + 30 + 30;
    let mut row = vec![BabyBear::ZERO; W];
    row[0] = BabyBear::new(x_private);
    row[1] = BabyBear::new(min_x);
    row[2] = BabyBear::new(max_x);
    // bits for x_private - min_x
    let diff1 = x_private.saturating_sub(min_x);
    for j in 0..30 {
        let bit = (diff1 >> j) & 1;
        row[3 + j] = BabyBear::from_bool(bit == 1);
    }
    // bits for max_x - x_private
    let diff2 = max_x.saturating_sub(x_private);
    for j in 0..30 {
        let bit = (diff2 >> j) & 1;
        row[33 + j] = BabyBear::from_bool(bit == 1);
    }
    RowMajorMatrix::new_row(row)
}

/// Run the RangeCheckAirK30 AIR on a 1-row witness; returns true if all constraints hold.
fn run_range_check_debug(x_private: u32, min_x: u32, max_x: u32) -> bool {
    let air = RangeCheckAirK30;
    let main = build_trace_range_check_k30(x_private, min_x, max_x);
    let view = main.as_view();
    let mut builder = MiniDebugBuilder { main: view, ok: true };
    air.eval(&mut builder);
    builder.ok
}


// ---- Minimal debug builder & helpers for local constraint checking ----

/// A tiny debug builder to run AIR constraints over a fixed 1-row trace.
struct MiniDebugBuilder<'a, F: Field> {
    main: RowMajorMatrixView<'a, F>,
    ok: bool,
}

impl<'a, F> p3_air::AirBuilder for MiniDebugBuilder<'a, F>
where
    F: Field,
{
    type F = F;
    type Expr = F;
    type Var = F;
    type M = RowMajorMatrixView<'a, F>;

    fn main(&self) -> Self::M { self.main }
    fn is_first_row(&self) -> Self::Expr { F::ONE }
    fn is_last_row(&self) -> Self::Expr { F::ONE }
    fn is_transition_window(&self, _size: usize) -> Self::Expr { F::ZERO }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let v = x.into();
        if v != F::ZERO { self.ok = false; }
    }

    fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2) {
        let xv = x.into();
        let yv = y.into();
        if xv != yv { self.ok = false; }
    }
}

impl<F: Field> AirBuilderWithPublicValues for MiniDebugBuilder<'_, F> {
    type PublicVar = F;
    fn public_values(&self) -> &[Self::PublicVar] { &[] }
}


/// Build a trace for RangeCheckAirK30 with variable height (n_rows >= 1, power of two recommended)
fn build_trace_range_check_k30_many(x_private: u32, min_x: u32, max_x: u32, n_rows: usize) -> RowMajorMatrix<BabyBear> {
    const W: usize = 3 + 30 + 30;
    let mut values = Vec::with_capacity(W * n_rows);
    for _ in 0..n_rows {
        let mut row = vec![BabyBear::ZERO; W];
        row[0] = BabyBear::new(x_private);
        row[1] = BabyBear::new(min_x);
        row[2] = BabyBear::new(max_x);
        // bits for x_private - min_x
        let diff1 = x_private.saturating_sub(min_x);
        for j in 0..30 {
            let bit = (diff1 >> j) & 1;
            row[3 + j] = BabyBear::from_bool(bit == 1);
        }
        // bits for max_x - x_private
        let diff2 = max_x.saturating_sub(x_private);
        for j in 0..30 {
            let bit = (diff2 >> j) & 1;
            row[33 + j] = BabyBear::from_bool(bit == 1);
        }
        values.extend(row);
    }
    RowMajorMatrix::new(values, W)
}
