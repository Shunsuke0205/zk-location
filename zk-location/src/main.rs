use p3_field::Field;
use p3_baby_bear::BabyBear;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_field::PrimeCharacteristicRing; // for ONE constant

// all the comments should be in English

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
    // BabyBear field
    // let params = BabyBearParameters; // unused in this demo
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
