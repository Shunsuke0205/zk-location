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
