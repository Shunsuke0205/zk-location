use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;

use crate::{MyConfig, Val};
use crate::config::make_config_with_blowup;
// use crate::combine; // not used here to keep PoC semantics as left + 3*right

/// Non-commutative lane-wise combine used for PoC Merkle hashing inside the AIR:
/// parent = left + 3 * right  (mod p)
#[inline]
pub fn combine_merkle_lane_mod_p(left: u32, right: u32) -> u32 {
    const P: u128 = 0x7800_0001; // BabyBear modulus
    let mut s = (left as u128) + 3u128 * (right as u128);
    s %= P;
    s as u32
}

#[inline]
pub fn combine_merkle_digest(left: [u32; 4], right: [u32; 4]) -> [u32; 4] {
    [
        combine_merkle_lane_mod_p(left[0], right[0]),
        combine_merkle_lane_mod_p(left[1], right[1]),
        combine_merkle_lane_mod_p(left[2], right[2]),
        combine_merkle_lane_mod_p(left[3], right[3]),
    ]
}

/// Compute Merkle root off-circuit for a given leaf, sibling path, and direction bits.
/// dir[i] = 0 => parent = combine(curr, sib[i]); dir[i] = 1 => parent = combine(sib[i], curr)
pub fn compute_merkle_root_poc(
    leaf: [u32; 4],
    siblings: &[[u32; 4]],
    dirs: &[u32],
) -> [u32; 4] {
    let mut curr = leaf;
    for (i, sib) in siblings.iter().enumerate() {
        let d = dirs[i] & 1;
        curr = if d == 0 { combine_merkle_digest(curr, *sib) } else { combine_merkle_digest(*sib, curr) };
    }
    curr
}

/// Heuristic parameter selection for the PoC to satisfy LDE sizing while keeping it fast.
/// Condition to avoid panic: blowup_bits >= log_quotient_degree (empirical upper bound grows with depth).
/// Returns: (trace_height, fri_log_blowup).
fn select_poc_params(depth: usize) -> (usize, usize) {
    match depth {
        0..=2 => (8, 2),    // shallow paths: small blowup
        3..=4 => (8, 4),    // our demo depth=4 uses blowup=4
        5..=6 => (16, 5),   // deeper: bump both moderately
        _ => (32, 6),       // conservative ceiling for larger depths
    }
}

/// AIR that verifies a Merkle path of fixed depth using the PoC combine.
/// Layout (single row):
///  - 0..4: leaf lanes
///  - For each step i in 0..depth:
///      - 4 lanes of sibling_i
///      - 1 bit dir_i
/// Public values: 4 lanes of expected root
pub struct MerklePathAir { pub depth: usize }

impl<F: Field> BaseAir<F> for MerklePathAir {
    fn width(&self) -> usize {
        4 + self.depth * (4 + 1)
    }
}

impl<AB: AirBuilder + AirBuilderWithPublicValues> Air<AB> for MerklePathAir
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let row = builder.main();
        let pvs: Vec<_> = builder.public_values().iter().cloned().collect();

        // Read leaf lanes
        let mut curr = [
            row.get(0, 0).unwrap().into(),
            row.get(0, 1).unwrap().into(),
            row.get(0, 2).unwrap().into(),
            row.get(0, 3).unwrap().into(),
        ];

        // Iterate over depth
        for i in 0..self.depth {
            let base = 4 + i * 5;
            // sibling lanes
            let sib = [
                row.get(0, base + 0).unwrap().into(),
                row.get(0, base + 1).unwrap().into(),
                row.get(0, base + 2).unwrap().into(),
                row.get(0, base + 3).unwrap().into(),
            ];
            let dir = row.get(0, base + 4).unwrap();
            builder.assert_bool(dir.clone());

            // parent = (1-dir)*(curr + 3*sib) + dir*(sib + 3*curr)
            let three = AB::F::ONE + AB::F::ONE + AB::F::ONE;
            // Build 1 as Expr using a lane-local zero
            let zero_e = curr[0].clone() - curr[0].clone();
            let one_e = zero_e.clone() + AB::F::ONE;
            let one_minus_dir = one_e.clone() - dir.clone().into();

            curr = [
                one_minus_dir.clone() * (
                    curr[0].clone() + sib[0].clone() * three.clone()
                ) + dir.clone().into() * (
                    sib[0].clone() + curr[0].clone() * three.clone()
                ),
                one_minus_dir.clone() * (
                    curr[1].clone() + sib[1].clone() * three.clone()
                ) + dir.clone().into() * (
                    sib[1].clone() + curr[1].clone() * three.clone()
                ),
                one_minus_dir.clone() * (
                    curr[2].clone() + sib[2].clone() * three.clone()
                ) + dir.clone().into() * (
                    sib[2].clone() + curr[2].clone() * three.clone()
                ),
                one_minus_dir.clone() * (
                    curr[3].clone() + sib[3].clone() * three.clone()
                ) + dir.clone().into() * (
                    sib[3].clone() + curr[3].clone() * three.clone()
                ),
            ];
        }

        // Bind to expected root PVs if provided
        if pvs.len() >= 4 {
            for k in 0..4 {
                builder.assert_eq(curr[k].clone(), pvs[k].clone());
            }
        }
    }
}

pub fn build_trace_merkle_path(
    leaf: [u32; 4],
    siblings: &[[u32; 4]],
    dirs: &[u32],
) -> RowMajorMatrix<BabyBear> {
    assert_eq!(siblings.len(), dirs.len());
    let depth = siblings.len();
    let width = 4 + depth * 5;
    // Build a single logical row then replicate to a small power-of-two height
    let mut row = vec![BabyBear::ZERO; width];
    for k in 0..4 { row[k] = BabyBear::new(leaf[k]); }
    for i in 0..depth {
        let base = 4 + i * 5;
        for k in 0..4 { row[base + k] = BabyBear::new(siblings[i][k]); }
        row[base + 4] = BabyBear::from_bool((dirs[i] & 1) == 1);
    }
    let (height, _blowup_bits) = select_poc_params(depth);
    let mut values = Vec::with_capacity(width * height);
    for _ in 0..height { values.extend_from_slice(&row); }
    RowMajorMatrix::new(values, width)
}

pub fn flatten_pv_merkle_root(root: [u32; 4]) -> Vec<Val> {
    vec![Val::new(root[0]), Val::new(root[1]), Val::new(root[2]), Val::new(root[3])]
}

pub fn prove_merkle_path(
    leaf: [u32; 4],
    siblings: &[[u32; 4]],
    dirs: &[u32],
    root: [u32; 4],
) -> p3_uni_stark::Proof<MyConfig> {
    let depth = siblings.len();
    let (_height, blowup_bits) = select_poc_params(depth);
    let config = make_config_with_blowup(blowup_bits);

    let trace = build_trace_merkle_path(leaf, siblings, dirs);
    let pvs = flatten_pv_merkle_root(root);
    let air = MerklePathAir { depth: siblings.len() };
    p3_uni_stark::prove(&config, &air, trace, &pvs)
}

pub fn verify_merkle_path(
    proof: &p3_uni_stark::Proof<MyConfig>,
    depth: usize,
    root: [u32; 4],
) -> bool {
    let (_height, blowup_bits) = select_poc_params(depth);
    let config = make_config_with_blowup(blowup_bits);

    let pvs = flatten_pv_merkle_root(root);
    let air = MerklePathAir { depth };
    p3_uni_stark::verify(&config, &air, proof, &pvs).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merkle_poc_happy_path_depth4() {
        let leaf = [11, 22, 33, 44];
        let siblings = vec![[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]];
        let dirs = vec![0,1,0,1];
        let root = compute_merkle_root_poc(leaf, &siblings, &dirs);
        let proof = prove_merkle_path(leaf, &siblings, &dirs, root);
        assert!(verify_merkle_path(&proof, siblings.len(), root));
    }

    #[test]
    fn merkle_poc_detects_wrong_dir() {
        let leaf = [1, 1, 1, 1];
        let siblings = vec![[2,2,2,2],[3,3,3,3]];
        let dirs = vec![0,0];
        let root = compute_merkle_root_poc(leaf, &siblings, &dirs);
        let proof = prove_merkle_path(leaf, &siblings, &dirs, root);
        // Flip one direction; verify should fail
        let wrong_dirs = vec![1,0];
        let wrong_root = compute_merkle_root_poc(leaf, &siblings, &wrong_dirs);
        assert!(!verify_merkle_path(&proof, siblings.len(), wrong_root));
    }
}
