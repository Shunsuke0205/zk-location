use p3_field::Field;
use p3_baby_bear::BabyBear;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_field::PrimeCharacteristicRing; // for ONE constant

// --- Plonky3 proof generation for RangeCheckAirK30 ---
use p3_uni_stark::{prove, verify, StarkConfig};

use p3_baby_bear::{Poseidon2BabyBear};
use p3_field::extension::BinomialExtensionField;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_fri::{TwoAdicFriPcs, create_test_fri_params};
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
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

/// Generate a STARK proof for min_x <= x_private <= max_x
fn prove_range_check(
    x_private: u32,
    min_x: u32,
    max_x: u32,
    trace_height: usize,
    log_final_poly_len: usize,
) -> p3_uni_stark::Proof<MyConfig> {
    // Setup Plonky3 config
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params(challenge_mmcs, log_final_poly_len);
    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // Build trace with variable height
    let trace = build_trace_range_check_k30_many(x_private, min_x, max_x, trace_height);

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
    trace_height: usize,
    log_final_poly_len: usize,
) -> bool {
    // Setup Plonky3 config (must match prover)
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params(challenge_mmcs, log_final_poly_len);
    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // Public values: [min_x, max_x]
    let public_values = vec![Val::new(min_x), Val::new(max_x)];

    // Verify proof
    let result = verify(&config, &RangeCheckAirK30, proof, &public_values);
    result.is_ok()
}


// all the comments should be in English

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

impl<AB: AirBuilder> Air<AB> for RangeCheckAirK30
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let x_private = row.get(0, 0).unwrap().into();
        let min_x = row.get(0, 1).unwrap().into();
        let max_x = row.get(0, 2).unwrap().into();

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

pub struct GteAirK30;

impl<F: Field> BaseAir<F> for GteAirK30 {
    fn width(&self) -> usize {
        // col0: a, 
        // col1: b, 
        // col2..31: bits of diff = a - b (K=30)
        2 + 30
    }
}


impl<AB: AirBuilder,> Air<AB> for GteAirK30
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let a = row.get(0, 0).unwrap().into();
        let b = row.get(0, 1).unwrap().into();
        let diff = a.clone() - b.clone(); // diff = a - b

        // boolean check (bit_j in {0,1})
        for j in 0..30 {
            builder.assert_bool(row.get(0, 2 + j).unwrap());
        }

        // diff = sum_{j=0}^{29} bit_j * 2^j
        let mut acc = diff.clone() - diff.clone(); // ZERO
        let mut pow2 = AB::F::ONE; // 2^0
        for j in 0..30 {
            let bit_expr = row.get(0, 2 + j).unwrap().into();
            acc = acc + bit_expr * pow2.clone();
            if j < 29 { pow2 = pow2.clone() + pow2; } // 次の 2^j
        }
        builder.assert_eq(acc, diff);
    }
}


fn main() {
    {
         // --- Plonky3 proof generation example ---
        let x_private = 15;
        let min_x = 10;
        let max_x = 20;
        let trace_height = 8; // must be >= 2^log_final_poly_len + blowup
        let log_final_poly_len = 2; // example: keep small for demo
        let proof = prove_range_check(x_private, min_x, max_x, trace_height, log_final_poly_len);
        println!("Plonky3 proof generated for {} in [{} , {}]", x_private, min_x, max_x);

        // --- Plonky3 proof verification example ---
        let verified = verify_range_check(&proof, min_x, max_x, trace_height, log_final_poly_len);
        println!("Plonky3 proof verification result: {}", verified);
    }
    {
        // --- Plonky3 proof generation example (failing case) ---
        let x_private = 1000000;
        let min_x = 1000;
        let max_x = 100000;
        let trace_height = 8; // must be >= 2^log_final_poly_len + blowup
        let log_final_poly_len = 2; // example: keep small for demo
        let proof = prove_range_check(x_private, min_x, max_x, trace_height, log_final_poly_len);
        println!("Plonky3 proof generated for {} in [{} , {}]", x_private, min_x, max_x);

        // --- Plonky3 proof verification example (failing case) ---
        let verified = verify_range_check(&proof, min_x, max_x, trace_height, log_final_poly_len);
        println!("Plonky3 proof verification result: {}", verified);
    }
    {
        // --- Plonky3 proof generation example (failing case) ---
        let x_private = 10;
        let min_x = 1000;
        let max_x = 100000;
        let trace_height = 8; // must be >= 2^log_final_poly_len + blowup
        let log_final_poly_len = 2; // example: keep small for demo
        let proof = prove_range_check(x_private, min_x, max_x, trace_height, log_final_poly_len);
        println!("Plonky3 proof generated for {} in [{} , {}]", x_private, min_x, max_x);

        // --- Plonky3 proof verification example (failing case) ---
        let verified = verify_range_check(&proof, min_x, max_x, trace_height, log_final_poly_len);
        println!("Plonky3 proof verification result: {}", verified);
    }


    // BabyBear field
    let x = BabyBear::new(100);
    let y = BabyBear::new(101);
    let sum = x + y;
    let diff = x - y;
    let prod = x * y;
    let quot = x / y;

    println!("x = {:?}", x);
    println!("y = {:?}", y);
    println!("sum (x + y) = {:?}", sum);
    println!("diff (x - y) = {:?}", diff);
    println!("prod (x * y) = {:?}", prod);
    println!("quot (x / y) = {:?}", quot);

    // Quick debug check for GteAirK30 using a single-row trace.
    let pass = run_gte_debug(1000, 999);
    println!("GteAirK30 check 1000 >= 999 -> {}", pass);
    let fail = run_gte_debug(999, 1000);
    println!("GteAirK30 check 999 >= 1000 -> {}", fail);
    println!("GteAirK30 check 1000 >= 1000 -> {}", run_gte_debug(1000, 1000));

    println!("---");
    println!("GT check (a > b) using GteAirK30 with b+1 ---");
    println!("GT check 1000 > 999 -> {}", run_gt_debug(1000, 999));
    println!("GT check 999 > 999 -> {}", run_gt_debug(999, 999));
    println!("GT check 999 > 1000 -> {}", run_gt_debug(999, 1000));

    println!("---");
    println!("LTE check (a <= b) using GteAirK30 with swapped (b, a) ---");
    println!("LTE check 999 <= 1000 -> {}", run_lte_debug(999, 1000));
    println!("LTE check 1000 <= 1000 -> {}", run_lte_debug(1000, 1000));
    println!("LTE check 1000 <= 999 -> {}", run_lte_debug(1000, 999));

    println!("---");
    println!("LT check (a < b) using GteAirK30 with a+1 ---");
    println!("LT check 999999 < 1000000 -> {}", run_lt_debug(999999, 1000000));
    println!("LT check 1000000 < 1000000 -> {}", run_lt_debug(1000000, 1000000));
    println!("LT check 1000001 < 1000000 -> {}", run_lt_debug(1000001, 1000000));

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

/// Build a single-row trace for GteAirK30: [a, b, bits(diff)] with K=30.
fn build_trace_gte_k30(a: u32, b: u32) -> RowMajorMatrix<BabyBear> {
    const W: usize = 2 + 30;
    let mut row = vec![BabyBear::ZERO; W];
    row[0] = BabyBear::new(a);
    row[1] = BabyBear::new(b);
    let diff = a.saturating_sub(b) as u32; // if a<b -> 0, which will intentionally fail constraints
    for j in 0..30 {
        let bit = (diff >> j) & 1;
        row[2 + j] = BabyBear::from_bool(bit == 1);
    }
    RowMajorMatrix::new_row(row)
}


/// Run the GteAirK30 AIR on a 1-row witness; returns true if all constraints hold.
fn run_gte_debug(a: u32, b: u32) -> bool {
    let air = GteAirK30;
    let main = build_trace_gte_k30(a, b);
    let view = main.as_view();
    let mut builder = MiniDebugBuilder { main: view, ok: true };
    air.eval(&mut builder);
    builder.ok
}

fn build_trace_gt_k30(a: u32, b: u32) -> RowMajorMatrix<BabyBear> {
    const W: usize = 2 + 30;
    let mut row = vec![BabyBear::ZERO; W];
    row[0] = BabyBear::new(a);
    let b_plus_1 = b.saturating_add(1);
    row[1] = BabyBear::new(b_plus_1);
    let diff = a.saturating_sub(b_plus_1) as u32;
    for j in 0..30 {
        let bit = (diff >> j) & 1;
        row[2 + j] = BabyBear::from_bool(bit == 1);
    }
    RowMajorMatrix::new_row(row)
}

fn run_gt_debug(a: u32, b: u32) -> bool {
    let air = GteAirK30;
    let main = build_trace_gt_k30(a, b);
    let view = main.as_view();
    let mut builder = MiniDebugBuilder { main: view, ok: true };
    air.eval(&mut builder);
    builder.ok
}

fn build_trace_lte_k30(a: u32, b: u32) -> RowMajorMatrix<BabyBear> {
    const W: usize = 2 + 30;
    let mut row = vec![BabyBear::ZERO; W];
    row[0] = BabyBear::new(b);
    row[1] = BabyBear::new(a);
    let diff = b.saturating_sub(a) as u32;
    for j in 0..30 {
        let bit = (diff >> j) & 1;
        row[2 + j] = BabyBear::from_bool(bit == 1);
    }
    RowMajorMatrix::new_row(row)
}

fn run_lte_debug(a: u32, b: u32) -> bool {
    let air = GteAirK30;
    let main = build_trace_lte_k30(a, b);
    let view = main.as_view();
    let mut builder = MiniDebugBuilder { main: view, ok: true };
    air.eval(&mut builder);
    builder.ok
}

fn build_trace_lt_k30(a: u32, b: u32) -> RowMajorMatrix<BabyBear> {
    const W: usize = 2 + 30;
    let mut row = vec![BabyBear::ZERO; W];
    row[0] = BabyBear::new(b);
    let a_plus_1 = a.saturating_add(1);
    row[1] = BabyBear::new(a_plus_1);
    let diff = b.saturating_sub(a_plus_1) as u32;
    for j in 0..30 {
        let bit = (diff >> j) & 1;
        row[2 + j] = BabyBear::from_bool(bit == 1);
    }
    RowMajorMatrix::new_row(row)
}

fn run_lt_debug(a: u32, b: u32) -> bool {
    let air = GteAirK30;
    let main = build_trace_lt_k30(a, b);
    let view = main.as_view();
    let mut builder = MiniDebugBuilder { main: view, ok: true };
    air.eval(&mut builder);
    builder.ok
}
