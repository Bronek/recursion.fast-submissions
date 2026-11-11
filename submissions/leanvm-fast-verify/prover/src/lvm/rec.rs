//! The recursion witness of a `b = 1` proof (WP-15b; BLUEPRINT §2.2, §3.1, §4.2, §11 A2/A3): from the left
//! child's signed proof `(π', tr', σ')`:
//!
//! - **the stream** `Σ` = the lanes of `pad10*1(0x54 ‖ traceBytes tr')` (the bytes `traceDigest tr'` hashes, with
//!   Keccak-256's padding): KS row `i < B` absorbs lanes `17i … 17i + 16` (`C_rec`'s `M_l[i] = Σ[17i + l]`),
//!   rows `B … 2^rec − 1` absorb zero; so `Y` of row `B − 1` is `traceDigest tr'`;
//! - **`σ'`** as `C_rec` column 17: the 597 lanes of `idx ‖ ots ‖ path` (FORMAT.md's signature words);
//! - **KS rows `≥ R = 2^rec`** (messages `X`, padded blocks as 17 lanes), in this order:
//!   - 133 × 3 WOTS chain steps, chain-major: row `R + 3i + (s − 1)` hashes `wotsStep j i (s − 1) a_s` with
//!     `a_s` = the previous step's output if `d_i + 1 < s`, else `ots_i` (the selection of WP-12's
//!     `wots_chain_sound`; `d = wotsDigits (traceDigest tr')`, `j = σ'.idx`); chain `i` ends at step 3's output
//!     if `d_i < 3`, else at `ots_i`;
//!   - rows `R + 399 … R + 430`: the key leaf `0x4B ‖ enc64 j ‖ end_0 ‖ … ‖ end_132` (32 blocks, `cont` inside);
//!   - rows `R + 431 + t`, `t < 16`: `sigNode` of the current value and `path[t]`, ordered by bit `t` of `j`;
//!   - row `R + 447`: `leafStmt h' n'`; row `R + 448`: `nodeStmt c_L' (leafStmt h' n')` (both for either `b'`);
//!   - every later row absorbs zero.
//!
//! [`RecWitness::zero`] is the `b = 0` convention (BLUEPRINT §4.5 Gate): every message zero.

use crate::format::{self, Sig, Signed, SIG_HEIGHT, TAG_SIG_NODE, TAG_WOTS, TAG_WOTS_LEAF, WOTS_LEN};
use crate::keccak::{self, Digest, RATE, RATE_LANES, TAG_LEAF, TAG_NODE};
use crate::lvm::params::{Params, REC_STREAM_COLS, SIG_BYTES};
use crate::lvm::stream::header_of;

/// First KS row (above `R`) of each group.
pub const ROW_CHAIN: usize = 0;
pub const ROW_LEAF: usize = 3 * WOTS_LEN;
pub const ROW_PATH: usize = ROW_LEAF + 32;
pub const ROW_LEAF_STMT: usize = ROW_PATH + SIG_HEIGHT;
pub const ROW_NODE_STMT: usize = ROW_LEAF_STMT + 1;
/// KS rows `≥ R` used (WP-0: 449).
pub const UPPER_ROWS: usize = ROW_NODE_STMT + 1;
/// Lanes of `σ'` in its `C_rec` column.
pub const SIG_LANES: usize = SIG_BYTES / 8;

/// The recursion witness: the 17 message lanes of every KS row (rows `< 2^rec` are `C_rec`'s stream columns
/// `M_l`, rows `≥ 2^rec` the `X` columns of `C_main`) and `σ'`'s column (`2^rec` words).
pub struct RecWitness {
    pub msg: Vec<[u64; REC_STREAM_COLS]>,
    pub sigma: Vec<u64>,
    /// The recursion tables (LoopIR pieces, input arrays, BITS) for the real bus and the table sumcheck;
    /// empty: the null bus of WP-15a (`M3.v0`).
    pub tables: Vec<crate::lvm::m3::TableW>,
}

/// `m` with Keccak's `pad10*1` as rate blocks of 17 lanes.
pub fn padded_blocks(m: &[u8]) -> Vec<[u64; RATE_LANES]> {
    let nb = m.len() / RATE + 1;
    let mut b = vec![0u8; nb * RATE];
    b[..m.len()].copy_from_slice(m);
    b[m.len()] ^= 0x01;
    b[nb * RATE - 1] ^= 0x80;
    (0..nb).map(|k| std::array::from_fn(|l| keccak::lane_of(&b[k * RATE..(k + 1) * RATE], l))).collect()
}

/// The bytes `traceDigest` hashes: `0x54 ‖ (enc64 |q| ‖ q ‖ a)…`.
pub fn trace_bytes(tr: &[(Vec<u8>, Digest)]) -> Vec<u8> {
    let n = 1 + tr.iter().map(|(q, _)| 40 + q.len()).sum::<usize>();
    let mut v = Vec::with_capacity(n);
    v.push(format::TAG_TRACE);
    for (q, a) in tr {
        v.extend_from_slice(&(q.len() as u64).to_le_bytes());
        v.extend_from_slice(q);
        v.extend_from_slice(a);
    }
    v
}

fn one_block(m: &[u8]) -> [u64; RATE_LANES] {
    let b = padded_blocks(m);
    assert_eq!(b.len(), 1, "a one-block message");
    b[0]
}

fn hash_block(m: &[u64; RATE_LANES]) -> Digest {
    let mut a = [0u64; 25];
    a[..RATE_LANES].copy_from_slice(m);
    keccak::keccak_f(&mut a);
    keccak::digest_of(&a)
}

pub fn wots_step_msg(j: u64, i: usize, s: usize, x: &Digest) -> [u64; RATE_LANES] {
    let mut m = Vec::with_capacity(43);
    m.push(TAG_WOTS);
    m.extend_from_slice(&j.to_le_bytes());
    m.extend_from_slice(&[i as u8, s as u8]);
    m.extend_from_slice(x);
    one_block(&m)
}

fn two_msg(tag: u8, a: &Digest, b: &Digest) -> [u64; RATE_LANES] {
    let mut m = Vec::with_capacity(65);
    m.push(tag);
    m.extend_from_slice(a);
    m.extend_from_slice(b);
    one_block(&m)
}

impl RecWitness {
    /// The `b = 0` convention: every message zero.
    pub fn zero(p: &Params) -> Self {
        Self { msg: vec![[0; REC_STREAM_COLS]; 1 << p.ks_log], sigma: vec![0; 1 << p.rec_rows_log], tables: Vec::new() }
    }

    /// The witness of a node whose left child is `child` (module doc).
    pub fn from_child(p: &Params, child: &Signed) -> Self {
        let r = 1usize << p.rec_rows_log;
        let mut w = Self::zero(p);
        // the stream
        let blocks = padded_blocks(&trace_bytes(&child.tr));
        assert_eq!(blocks.len(), crate::lvm::prove::sponge_blocks(p), "the child's trace has the schedule's length");
        assert!(blocks.len() <= r);
        for (i, b) in blocks.iter().enumerate() {
            w.msg[i] = *b;
        }
        // σ'
        let mut sb = Vec::with_capacity(SIG_BYTES);
        format::put_sig(&mut sb, &child.sig);
        assert_eq!(sb.len(), SIG_BYTES);
        for k in 0..SIG_LANES {
            w.sigma[k] = keccak::lane_of(&sb, k);
        }
        // the WOTS walk of σ' on traceDigest tr'
        let m = format::trace_digest(&child.tr);
        let sig: &Sig = &child.sig;
        let j = sig.idx;
        let d = format::wots_digits(&m);
        let mut ends = Vec::with_capacity(WOTS_LEN);
        for i in 0..WOTS_LEN {
            let mut prev = [0u8; 32];
            for s in 1..=3usize {
                let a = if (d[i] as usize) + 1 < s { prev } else { sig.ots[i] };
                let blk = wots_step_msg(j, i, s - 1, &a);
                w.msg[r + ROW_CHAIN + 3 * i + (s - 1)] = blk;
                prev = hash_block(&blk);
            }
            ends.push(if d[i] < 3 { prev } else { sig.ots[i] });
        }
        let mut leaf = Vec::with_capacity(9 + 32 * WOTS_LEN);
        leaf.push(TAG_WOTS_LEAF);
        leaf.extend_from_slice(&j.to_le_bytes());
        for e in &ends {
            leaf.extend_from_slice(e);
        }
        let lb = padded_blocks(&leaf);
        assert_eq!(lb.len(), 32);
        for (k, b) in lb.iter().enumerate() {
            w.msg[r + ROW_LEAF + k] = *b;
        }
        let mut cur = keccak::keccak256(&leaf);
        for t in 0..SIG_HEIGHT {
            let sib = &sig.path[t];
            let blk = if (j >> t) & 1 == 0 { two_msg(TAG_SIG_NODE, &cur, sib) } else { two_msg(TAG_SIG_NODE, sib, &cur) };
            w.msg[r + ROW_PATH + t] = blk;
            cur = hash_block(&blk);
        }
        // the child's statement
        let hd = header_of(p, &child.pi);
        let mut ls = Vec::with_capacity(41);
        ls.push(TAG_LEAF);
        ls.extend_from_slice(&hd.h);
        ls.extend_from_slice(&hd.n.to_le_bytes());
        let lsb = one_block(&ls);
        w.msg[r + ROW_LEAF_STMT] = lsb;
        w.msg[r + ROW_NODE_STMT] = two_msg(TAG_NODE, &hd.c_l, &hash_block(&lsb));
        w
    }

    /// The `C_rec` stream columns and the `X` messages as one dump (`LVM_REC_DUMP`, for the Lean check):
    /// `2^ks_log` rows of 17 little-endian lanes, then `2^rec` lanes of `σ'`.
    pub fn dump(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(8 * (17 * self.msg.len() + self.sigma.len()));
        for row in &self.msg {
            for x in row {
                v.extend_from_slice(&x.to_le_bytes());
            }
        }
        for x in &self.sigma {
            v.extend_from_slice(&x.to_le_bytes());
        }
        v
    }
}

/// Self-checks (`lvm-prover rqtest`; the crate's `cargo test` does not build the vendored tests).
pub mod check {
    use super::*;

    pub fn padding_matches_keccak256() {
        for n in [0usize, 1, 41, 43, 65, 135, 136, 137, 4265] {
            let m: Vec<u8> = (0..n).map(|k| (k * 7 + 3) as u8).collect();
            let bl = padded_blocks(&m);
            let mut st = [0u64; 25];
            for b in &bl {
                for l in 0..RATE_LANES {
                    st[l] ^= b[l];
                }
                keccak::keccak_f(&mut st);
            }
            assert_eq!(keccak::digest_of(&st), keccak::keccak256(&m), "n = {n}");
        }
    }

    pub fn wots_rows_reach_the_key() {
        let msg: Digest = std::array::from_fn(|k| (k as u8).wrapping_mul(13));
        let (vk, sig) = format::toy_sign(7, &msg);
        // a fake child whose trace digest is not `msg`: sign its digest instead
        let p = crate::lvm::params::p8();
        let tr: Vec<(Vec<u8>, Digest)> = crate::lvm::params::query_list(&p)
            .iter()
            .enumerate()
            .map(|(k, (_, len))| (vec![k as u8; *len], [k as u8; 32]))
            .collect();
        let m = format::trace_digest(&tr);
        let (vk2, sig2) = format::toy_sign(7, &m);
        assert!(format::sig_ok(&vk, &msg, &sig) && format::sig_ok(&vk2, &m, &sig2));
        let mut pi = vec![0u8; crate::lvm::params::header_bytes(&p)];
        pi[0] = b'S';
        let child = Signed { pi, tr, sig: sig2.clone() };
        let w = RecWitness::from_child(&p, &child);
        let r = 1usize << p.rec_rows_log;
        // replay the KS rows: trace sponge, then the path's last output is vk2
        let cont = crate::lvm::tables::cont_column(p.ks_log, p.rec_rows_log, crate::lvm::prove::sponge_blocks(&p));
        let ks = crate::lvm::tables::Sponge::run(p.ks_log, cont, w.msg.clone());
        let b = crate::lvm::prove::sponge_blocks(&p);
        assert_eq!(keccak::digest_of(&ks.outputs[b - 1]), m, "Y of the last trace row is traceDigest");
        assert_eq!(keccak::digest_of(&ks.outputs[r + ROW_PATH + SIG_HEIGHT - 1]), vk2, "the walk reaches vk");
    }
}
