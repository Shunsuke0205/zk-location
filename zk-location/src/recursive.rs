//! Recursion scaffolding: statement shapes and accumulator API for pairwise aggregation.
//! This file intentionally avoids depending on Plonky3 types to keep compile fast.
#![allow(dead_code)]

/// Axis-aligned rectangle in biased micro-degree coordinates.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Rect {
    pub min_x: u32,
    pub max_x: u32,
    pub min_y: u32,
    pub max_y: u32,
}

impl Rect {
    pub const fn new(min_x: u32, max_x: u32, min_y: u32, max_y: u32) -> Self {
        Self { min_x, max_x, min_y, max_y }
    }
}

/// Fixed-size leaf statement for recursive aggregation.
/// K_MAX_OUTSIDE is the maximum number of outside rectangles carried as public inputs.
/// Unused slots must be zeroed and `outside_len` indicates the number of valid entries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimitiveRangeStatement<const K_MAX_OUTSIDE: usize> {
    pub min_ts: u32,
    pub max_ts: u32,
    pub inside: Rect,
    pub outside: [Rect; K_MAX_OUTSIDE],
    pub outside_len: u8,
}

impl<const K_MAX_OUTSIDE: usize> PrimitiveRangeStatement<K_MAX_OUTSIDE> {
    /// Returns true if the statement has at most K_MAX_OUTSIDE outside rectangles and
    /// unused slots are zero (best-effort shallow check for canonicalization).
    pub fn is_canonical(&self) -> bool {
        let len = self.outside_len as usize;
        if len > K_MAX_OUTSIDE { return false; }
        // Ensure zero padding after len to make hashing canonical upstream.
        for r in &self.outside[len..] {
            let zero = Rect { min_x: 0, max_x: 0, min_y: 0, max_y: 0 };
            if *r != zero { return false; }
        }
        true
    }
}

/// Small accumulator digest propagated up the aggregation tree.
/// In the real implementation this should be a Poseidon2 hash over BabyBear.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub struct AccumulatorDigest(pub [u32; 4]);

impl AccumulatorDigest {
    pub const ZERO: Self = Self([0; 4]);
}

/// Compute a placeholder accumulator digest for a leaf statement.
/// NOTE: This is a stub. Replace with Poseidon2 hash inside the AIR when implementing recursion.
pub fn digest_leaf_statement<const K: usize>(s: &PrimitiveRangeStatement<K>) -> AccumulatorDigest {
    // Very weak placeholder: xor/mix a few coordinates just to provide a stable API.
    // Do NOT rely on this outside of tests prior to real hashing.
    let mut acc = [0u32; 4];
    acc[0] ^= s.min_ts ^ s.max_ts ^ s.inside.min_x ^ s.inside.max_x;
    acc[1] ^= s.inside.min_y ^ s.inside.max_y;
    let len = s.outside_len as usize;
    for (i, r) in s.outside.iter().take(len).enumerate() {
        let lane = i & 3;
        acc[lane] = acc[lane]
            .wrapping_add(r.min_x)
            .wrapping_add(r.max_x)
            .wrapping_add(r.min_y)
            .wrapping_add(r.max_y);
    }
    AccumulatorDigest(acc)
}

/// Combine two accumulator digests into one (parent of a binary aggregation node).
/// NOTE: This is a stub. Replace with Poseidon2 hash(left||right) inside the AIR.
pub fn combine_digests(left: AccumulatorDigest, right: AccumulatorDigest) -> AccumulatorDigest {
    let mut out = [0u32; 4];
    for i in 0..4 { out[i] = left.0[i].wrapping_add(right.0[i]).rotate_left(13) ^ (i as u32); }
    AccumulatorDigest(out)
}

/// A binary aggregation node description (pure data, no proofs here).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AggNode {
    pub left: AccumulatorDigest,
    pub right: AccumulatorDigest,
    pub parent: AccumulatorDigest,
}

impl AggNode {
    pub fn new(left: AccumulatorDigest, right: AccumulatorDigest) -> Self {
        let parent = combine_digests(left, right);
        Self { left, right, parent }
    }
}
