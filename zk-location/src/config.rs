use rand::rngs::SmallRng;
use rand::SeedableRng;

use p3_challenger::DuplexChallenger;
use p3_fri::{create_test_fri_params_zk, FriParameters};
use p3_merkle_tree::MerkleTreeMmcs;

use crate::{
    Challenger, Dft, MyCompress, MyConfig, MyHash, Perm, Pcs, ValMmcs,
};

/// Build a Stark `MyConfig` with a specific FRI log_blowup.
/// Keeps other parameters identical to existing demos and uses a fixed RNG seed for reproducibility.
pub fn make_config_with_blowup(log_blowup: usize) -> MyConfig {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = p3_commit::ExtensionMmcs::<_, _, MerkleTreeMmcs<_, _, _, _, 8>>::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len: 0,
        num_queries: 2,
        proof_of_work_bits: 1,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger: Challenger = DuplexChallenger::new(perm);
    MyConfig::new(pcs, challenger)
}

/// Build a default ZK config using the repo’s test FRI parameters (small and fast).
pub fn make_config_default() -> MyConfig {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = p3_commit::ExtensionMmcs::<_, _, MerkleTreeMmcs<_, _, _, _, 8>>::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = create_test_fri_params_zk(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(1));
    let challenger: Challenger = DuplexChallenger::new(perm);
    MyConfig::new(pcs, challenger)
}
