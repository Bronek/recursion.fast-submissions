//! WP-4's end-to-end skeleton: leanVM's Keccak batch proof (`keccak_gkr`'s `batch_bench::run`, one pass)
//! on the oracle: `n` random permutations, the input and the state after round 12 committed (`C_main`'s
//! shape, `2^(log n + 6)` words), leanVM's GKR, ring switching and stacked WHIR with BLUEPRINT §3.1's
//! unique-decoding parameters (`ud_config`: no OOD, no grinding, caps), the transcript and every Merkle
//! hash through the oracle (`fiat_shamir::transcript`, `pcs::merkle`). Reports the proof's size, the
//! verifier's query count `qS` and trace length, the oracle load by class, the stage times and the peak RSS.

use std::time::Instant;

use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::keccak_gkr::{OutputClaim, Shape, Witness};
use crate::lv::pcs::whir::{INITIAL_FOLDING_FACTOR, commit};
use crate::lv::pcs::whir_config::{ProverConfig, ud_config};
use crate::lv::primitives::field::F64;
use crate::oracle::Digest;

/// The `S` proof header of BLUEPRINT §2.1 for the batch test: `'S' pad[7] | b | vk | c_L | s | n | h | σ_leaf`.
/// Here `s` is the batch's seed, `n` its size and the rest zero.
pub fn header(vk: &Digest, seed: u64, n: u64) -> Vec<u8> {
    let mut h = Vec::with_capacity(HEADER_BYTES);
    h.push(b'S');
    h.extend_from_slice(&[0u8; 7]);
    h.extend_from_slice(&0u64.to_le_bytes()); // b
    h.extend_from_slice(vk);
    h.extend_from_slice(&[0u8; 32]); // c_L
    let mut s = [0u8; 32];
    s[..8].copy_from_slice(&seed.to_le_bytes());
    h.extend_from_slice(&s);
    h.extend_from_slice(&n.to_le_bytes());
    h.extend_from_slice(&[0u8; 32]); // h
    h.extend_from_slice(&[0u8; SIG_BYTES]); // σ_leaf
    assert_eq!(h.len(), HEADER_BYTES);
    h
}

/// `idx u64 ‖ 133 × 32 ‖ 16 × 32`.
pub const SIG_BYTES: usize = 8 + 133 * 32 + 16 * 32;
/// The fields of BLUEPRINT §2.1 add up to 4,928 bytes (§2.1 states 4,936; WP-4 report).
pub const HEADER_BYTES: usize = 8 + 8 + 32 + 32 + 32 + 8 + 32 + SIG_BYTES;

/// SplitMix64, for the batch's inputs.
pub struct Rng(u64);
impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

pub struct Report {
    pub log_n: usize,
    pub mu: usize,
    pub config: ProverConfig,
    pub stages: Vec<(&'static str, f64)>,
    pub proof: Vec<u8>,
    pub trace: Vec<(Vec<u8>, Digest)>,
    pub fs_queries: usize,
}

impl Report {
    pub fn trace_bytes(&self) -> usize {
        // `traceBytes`: 0x54, then per item enc64 |q| ‖ q ‖ a
        1 + self.trace.iter().map(|(q, _)| 8 + q.len() + 32).sum::<usize>()
    }
}

/// Prove a batch of `2^log_n` random permutations (seeded by `seed`) on the installed oracle.
pub fn prove(log_n: usize, seed: u64, vk: &Digest) -> Report {
    const DEPTH: usize = 12;
    let n = 1usize << log_n;
    let shape = Shape::new(n, DEPTH);
    let mu = shape.stack_log();
    let config = ud_config(mu);
    let mut rng = Rng::new(seed ^ n as u64);
    let inputs: Vec<[u64; 25]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let mut stages = Vec::new();
    let mut lap = {
        let mut t = Instant::now();
        move |name: &'static str, stages: &mut Vec<(&'static str, f64)>| {
            let s = t.elapsed().as_secs_f64();
            crate::lv::tracing::record(name, s);
            stages.push((name, s));
            crate::alloc::memlog(name);
            t = Instant::now();
        }
    };

    // SAFETY: the witness generator writes every word.
    let mut committed = unsafe { crate::lv::primitives::uninit_vec::<F64>(1 << mu) };
    let witness = Witness::generate(shape, &inputs, &mut committed);
    lap("witness", &mut stages);

    let mut ps = ProverState::seeded(&header(vk, seed, n as u64));
    lap("seed", &mut stages);
    let (commitment, prover_data) =
        commit(&committed, mu, INITIAL_FOLDING_FACTOR, config.log_inv_rates[0], config.cap_logs[0], 1 << INITIAL_FOLDING_FACTOR);
    lap("commit", &mut stages);
    ps.add_cap(&commitment.cap);

    let instance = ps.sample_vec(shape.n_log());
    let output = OutputClaim::of_inputs(shape, &inputs, instance);
    ps.add_scalars(&output.lanes);
    drop(inputs);
    lap("output claim", &mut stages);

    let openings = witness.prove(&mut ps, &committed, &output);
    drop(witness);
    lap("gkr", &mut stages);

    let (ring, outputs) = openings.into_pcs_claims(0);
    let points: Vec<_> = outputs.into_iter().collect();
    crate::lv::pcs::stack_open::open_batch_mixed_whir_stacked(&mut ps, mu, committed, prover_data, &config, &points, &ring);
    lap("pcs open", &mut stages);

    let fs_queries = ps.fs_queries;
    let proof = std::mem::take(&mut ps.body);
    let trace = std::mem::take(&mut ps.trace);
    Report { log_n, mu, config, stages, proof, trace, fs_queries }
}
