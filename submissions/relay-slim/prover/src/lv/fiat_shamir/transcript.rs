// Vendored from leanVM 0b850750 `crates/fiat_shamir/src/transcript.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! Fiat-Shamir proof transport, prover side.
//!
//! **WP-4 replacement of leanVM's duplex** (BLUEPRINT §2.2, D12): the state is a 32-byte answer of
//! the contract oracle, and every step is one oracle query. The API is leanVM's (`add_scalar`
//! transmits and binds together; `sample`; `add_round_poly`; `hint_merkle`), so the GKR, sumcheck
//! and WHIR code call it unchanged; what it does is:
//!
//! - `q₀` = the 7 bytes `"lvm/1\0\0"` → `a₀`; seed = `a₀ ‖ header[8..]` → `st₀` ([`ProverState::seeded`]);
//! - a transmitted scalar or cap waits (a scalar is 24 bytes `c0 ‖ c1 ‖ c2` little-endian, a cap its
//!   `2^c` nodes); `sample` asks `st ‖ pending` (just `st` when nothing waits), the answer is the new state
//!   and its lanes 0–2 are the challenge (WP-15a: the Lean driver's `fsQuery`, `LvmDriver.lean`);
//! - positions: `⌈t/8⌉` queries, the first `st ‖ pending`, the others `st`; position `j` of a query is
//!   the bits `[d·j, d·j + d)` of lanes 0–2, low first ([`ProverState::sample_positions`]);
//! - PI-GRIND: with grinding bits `g > 0`, a separating sample, the nonce and the PoW sample precede the
//!   positions, which then all ask `st` ([`ProverState::grind`]);
//! - opened rows and siblings are never absorbed (the driver's `pend := off` after an opening);
//! - the length rule is a property of the schedule (`LvmSchedule.lengthRule`): every FS query is
//!   asserted not to have a reserved length (64, 384, 512) or the seed's; nothing is ever split.
//!
//! Besides the scalar stream and the Merkle phases (leanVM's [`Proof`]), the state keeps the proof
//! body in schedule order (scalars, caps, and per opened position the row then the siblings
//! bottom-up, BLUEPRINT §2.1) and the verifier's trace: every query `V` asks, in order, with its
//! answer (the Fiat–Shamir chain and the leaf and node queries of every opened path), which is what
//! `SIGN` signs. `hint_merkle` walks each opened path through the oracle and checks that it ends
//! at the cap node the commitment absorbed.

use crate::lv::fiat_shamir::merkle::{Hash, MerklePath};
use crate::lv::primitives::field::F192;
use crate::oracle::{self, Class, Digest};

/// The first query: 7 bytes, so every later length is a whole number of lanes (BLUEPRINT §2.2).
pub const Q0: &[u8; 7] = b"lvm/1\0\0";

/// Query lengths a Fiat–Shamir query may not have (node, later-level leaf, level-0 leaf).
const RESERVED: [usize; 3] = [64, 384, 512];

/// Positions per positions query.
pub const POSITIONS_PER_QUERY: usize = 8;

/// A scalar stream and its Merkle opening phases, each query's path in the order the verifier samples them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub stream: Vec<F192>,
    pub merkle: Vec<Vec<MerklePath>>,
}

/// Writes scalars into the stream and opening phases to the side.
pub struct ProverState {
    /// the chain's state: the last answer
    st: Digest,
    /// transmitted bytes not yet absorbed
    pending: Vec<u8>,
    /// the length of the seed query, which no other query may have
    seed_len: usize,
    stream: Vec<F192>,
    merkle: Vec<Vec<MerklePath>>,
    /// the proof body in schedule order
    pub body: Vec<u8>,
    /// the verifier's queries and answers, in order
    pub trace: Vec<(Vec<u8>, Digest)>,
    /// Fiat–Shamir queries asked (round trips)
    pub fs_queries: usize,
    /// PI-GRIND: per grinding level, the attempts made up to the accepted nonce (`counter + 1`)
    pub grind_attempts: Vec<u64>,
}

#[inline]
fn lanes(a: &Digest) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(a[8 * i..8 * i + 8].try_into().unwrap()))
}

#[inline]
fn scalar_bytes(x: F192) -> [u8; 24] {
    let mut b = [0u8; 24];
    b[..8].copy_from_slice(&x.c0.to_le_bytes());
    b[8..16].copy_from_slice(&x.c1.to_le_bytes());
    b[16..].copy_from_slice(&x.c2.to_le_bytes());
    b
}

/// The PoW predicate on the challenge's lane 2 (`c.c2`): its top `g` bits are zero, `c2 < 2^(64 − g)`.
#[inline]
pub fn pow_ok(lane2: u64, g: u32) -> bool {
    g == 0 || lane2 >> (64 - g) == 0
}

/// The grinding query `st ‖ (counter, 0, 0)` (32 + 24 bytes).
#[inline]
pub fn grind_query(st: &Digest, counter: u64, buf: &mut Vec<u8>) {
    buf.extend_from_slice(st);
    buf.extend_from_slice(&scalar_bytes(F192::new(counter, 0, 0)));
}

/// The smallest `counter` whose query `st ‖ (counter, 0, 0)` passes [`pow_ok`]. Rounds of `2^(g+1)` attempts
/// (at least 256, at most 2^13), split over the worker threads, each on its own oracle connection.
fn pow_search(st: &Digest, g: u32) -> u64 {
    use crate::lv::parallel;
    let round = (1usize << (g + 1).min(13)).max(256);
    let tasks = parallel::num_threads().clamp(1, round / 128);
    let chunk = round.div_ceil(tasks);
    let mut out = vec![[0u8; 32]; round];
    let mut base = 0u64;
    loop {
        let t = std::time::Instant::now();
        parallel::chunks_mut(&mut out, chunk, |i, sub| {
            let off = base + (i * chunk) as u64;
            oracle::get().ask_many_here(sub, &|j, buf: &mut Vec<u8>| grind_query(st, off + j as u64, buf));
        });
        oracle::note_grind(round, round.div_ceil(chunk), t);
        if let Some(j) = out.iter().position(|a| pow_ok(u64::from_le_bytes(a[16..24].try_into().unwrap()), g)) {
            return base + j as u64;
        }
        base += round as u64;
    }
}

impl ProverState {
    /// `q₀`, then the seed `a₀ ‖ header[8..]`: the whole header (statement, `vk`, …) is bound
    /// before anything is sampled.
    pub fn seeded(header: &[u8]) -> Self {
        assert!(header.len() >= 8);
        let a0 = oracle::ask(Class::Seed, Q0);
        let mut seed = Vec::with_capacity(32 + header.len() - 8);
        seed.extend_from_slice(&a0);
        seed.extend_from_slice(&header[8..]);
        assert!(!RESERVED.contains(&seed.len()) && seed.len() != 32, "the seed's length is its own");
        let st = oracle::ask(Class::Seed, &seed);
        let trace = vec![(Q0.to_vec(), a0), (seed.clone(), st)];
        Self {
            st,
            pending: Vec::new(),
            seed_len: seed.len(),
            stream: Vec::new(),
            merkle: Vec::new(),
            body: header.to_vec(),
            trace,
            fs_queries: 0,
            grind_attempts: Vec::new(),
        }
    }

    pub fn into_proof(self) -> Proof {
        Proof {
            stream: self.stream,
            merkle: self.merkle,
        }
    }

    pub fn state(&self) -> Digest {
        self.st
    }

    /// One query `st ‖ msg`; the answer is the new state.
    fn step(&mut self, msg: &[u8]) {
        let mut q = Vec::with_capacity(32 + msg.len());
        q.extend_from_slice(&self.st);
        q.extend_from_slice(msg);
        assert!(q.len() <= crate::format::QUERY_CAP, "a Fiat–Shamir query above queryCap");
        assert!(!RESERVED.contains(&q.len()) && q.len() != self.seed_len, "the length rule");
        self.st = oracle::ask(Class::Fs, &q);
        self.fs_queries += 1;
        self.trace.push((q, self.st));
    }

    /// Absorb what waits by one query `st ‖ pending` (the Lean driver never splits a message).
    fn flush(&mut self) {
        let msg = std::mem::take(&mut self.pending);
        self.step(&msg);
    }

    /// A challenge: the waiting scalars absorbed with it (`st ‖ pending`, or `st` alone
    /// when nothing waits); the last answer's lanes 0–2.
    pub fn sample(&mut self) -> F192 {
        self.flush();
        let l = lanes(&self.st);
        F192::new(l[0], l[1], l[2])
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// `count` positions in `[0, 2^d)`: one query `st` per [`POSITIONS_PER_QUERY`], position `j`
    /// of a query the bits `[d·j, d·j + d)` of its answer's lanes 0–2.
    pub fn sample_positions(&mut self, d: usize, count: usize) -> Vec<usize> {
        assert!(d * POSITIONS_PER_QUERY <= 192, "8 positions in 192 bits");
        let mut out = Vec::with_capacity(count);
        while out.len() < count {
            self.flush();
            let l = lanes(&self.st);
            let v = (l[0] as u128) | ((l[1] as u128) << 64);
            for j in 0..POSITIONS_PER_QUERY.min(count - out.len()) {
                let off = j * d;
                let chunk = if off + d <= 128 {
                    (v >> off) as u64
                } else if off >= 128 {
                    l[2] >> (off - 128)
                } else {
                    ((v >> off) as u64) | (l[2] << (128 - off))
                };
                out.push((chunk & ((1u64 << d) - 1)) as usize);
            }
        }
        out
    }

    /// Merkle data for the next opening phase: per path the leaf image then its siblings, bottom
    /// first, into the body; every path walked through the oracle (its leaf and node queries are
    /// the verifier's), and checked to end at `cap[q >> (height − c)]`.
    pub fn hint_merkle(&mut self, paths: Vec<MerklePath>, cap: &[Hash]) {
        assert!(self.pending.is_empty(), "an opening never follows unabsorbed messages");
        let c = cap.len().trailing_zeros() as usize;
        assert!(cap.len().is_power_of_two());
        let n = paths.len();
        if n == 0 {
            self.merkle.push(paths);
            return;
        }
        // the leaf queries, as one batch
        let leaf_bytes: Vec<Vec<u8>> = paths
            .iter()
            .map(|p| p.leaf.iter().flat_map(|w| w.0.to_le_bytes()).collect())
            .collect();
        let len = leaf_bytes.first().map_or(0, |b| b.len());
        assert!(leaf_bytes.iter().all(|b| b.len() == len) && (len == 512 || len == 384), "leaf queries are 512 or 384 bytes");
        let flat: Vec<u8> = leaf_bytes.concat();
        let mut cur = vec![[0u8; 32]; n];
        oracle::hash_items(Class::Leaf, &flat, len, &mut cur);
        let height = paths.first().map_or(0, |p| p.siblings.len());
        let mut items: Vec<Vec<(Vec<u8>, Digest)>> = (0..n).map(|i| vec![(leaf_bytes[i].clone(), cur[i])]).collect();
        // one level of every path at a time
        for level in 0..height {
            let mut q = Vec::with_capacity(64 * n);
            for (i, p) in paths.iter().enumerate() {
                let sib = &p.siblings[level];
                if (p.leaf_index >> level) & 1 == 0 {
                    q.extend_from_slice(&cur[i]);
                    q.extend_from_slice(sib);
                } else {
                    q.extend_from_slice(sib);
                    q.extend_from_slice(&cur[i]);
                }
            }
            oracle::hash_items(Class::Node, &q, 64, &mut cur);
            for i in 0..n {
                items[i].push((q[64 * i..64 * i + 64].to_vec(), cur[i]));
            }
        }
        for (i, p) in paths.iter().enumerate() {
            let top = (p.leaf_index as usize) >> height;
            assert!(top < cap.len(), "a path of {height} siblings under a cap of 2^{c}");
            assert_eq!(cur[i], cap[top], "an opened path ends at its cap node");
            self.body.extend_from_slice(&leaf_bytes[i]);
            for s in &p.siblings {
                self.body.extend_from_slice(s);
            }
        }
        for it in items {
            self.trace.extend(it);
        }
        self.merkle.push(paths);
    }

    /// Transmit a scalar into the proof AND bind it into the state (the two are
    /// inseparable: you cannot send without binding).
    #[inline]
    pub fn add_scalar(&mut self, x: F192) {
        let b = scalar_bytes(x);
        self.pending.extend_from_slice(&b);
        self.body.extend_from_slice(&b);
        self.stream.push(x);
    }

    pub fn add_scalars(&mut self, xs: &[F192]) {
        for &x in xs {
            self.add_scalar(x);
        }
    }

    /// Transmit a commitment's cap (`2^c` nodes, `c ≥ 1`); it waits for the next FS query like a scalar.
    pub fn add_cap(&mut self, cap: &[Hash]) {
        assert!(cap.len().is_power_of_two() && cap.len() >= 2, "a cap of 2^c nodes, c ≥ 1");
        for node in cap {
            self.pending.extend_from_slice(node);
            self.body.extend_from_slice(node);
        }
    }

    /// No message waits (an opening phase may start).
    pub fn nothing_pending(&self) -> bool {
        self.pending.is_empty()
    }

    /// Send one sumcheck round polynomial, as its COEFFICIENTS, constant first.
    ///
    /// The message is every coefficient but one: the running claim fixes the
    /// remaining one, which the verifier derives, so it is neither sent nor
    /// bound. Binding it would add nothing, being a function of the claim and the
    /// coefficients already bound. `eq` says whether the round's eq weight was
    /// factored out, which is what decides WHICH coefficient the claim fixes: a
    /// plain round has `h(0) + h(1) = Σ_{i≥1} c_i = claim`, which fixes `c_1`,
    /// and a round whose `eq` weight `r` was factored out has
    /// `(1 + r)·h(0) + r·h(1) = c_0 + r·Σ_{i≥1} c_i = claim`, which fixes `c_0`.
    pub fn add_round_poly(&mut self, coeffs: &[F192], eq: bool) {
        assert!(coeffs.len() >= 2, "a round polynomial has at least two coefficients");
        let fixed = usize::from(!eq);
        for (i, &c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.add_scalar(c);
            }
        }
    }

    /// PI-GRIND (`docs/lvm2/stages/PI-GRIND.md`, Gate §2): with `bits = g = 0` nothing is sent or absorbed (the
    /// v1/S2 schedule). With `g > 0`, right before a level's positions (its cap or final scalars waiting):
    /// 1. a separating sample `st ‖ pending`, discarded (the positions queries then all ask `st` alone);
    /// 2. the nonce, one `E` scalar `(counter, 0, 0)`: the smallest `counter ≥ 0` that passes;
    /// 3. the PoW challenge `c`, the sample `st ‖ nonce` (56 bytes); it passes when `eToNat c < 2^(192 − g)`,
    ///    i.e. the top `g` bits of lane 2 are zero.
    ///
    /// The search asks `st ‖ nonce` for whole rounds of counters over the oracle's connections (class `Grind`,
    /// not in `V`'s trace); only the accepted query is asked again as the Fiat–Shamir step. The result does not
    /// depend on the round size or the threads: the smallest passing counter.
    pub fn grind(&mut self, bits: u32) {
        if bits == 0 {
            return;
        }
        assert!(bits <= 64, "the PoW bits lie in lane 2 of the challenge (g ≤ 64)");
        self.sample();
        let counter = pow_search(&self.st, bits);
        self.add_scalar(F192::new(counter, 0, 0));
        let c = self.sample();
        assert!(pow_ok(c.c2, bits), "the accepted nonce's challenge passes");
        self.grind_attempts.push(counter + 1);
    }

    /// The verifier's query count so far.
    pub fn queries(&self) -> usize {
        self.trace.len()
    }
}

