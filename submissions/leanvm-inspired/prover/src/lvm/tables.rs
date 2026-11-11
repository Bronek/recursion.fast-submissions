//! The committed tables and where they sit (BLUEPRINT §3.1, §4.1–4.2, §11 A7, A9; WP-15a layout, sent to
//! WP-11a for `M3.chBlock`/`ksBlock`):
//!
//! `C_main` (`2^nu_main` K words), S2 (BLUEPRINT2 §2.2; FRZ-0's layout, docs/lvm2/stages/T-P1.md C.1): the fixed
//! blocks largest first from word 0 (ties `D`, `KS`, `KSY2`, `X`), then the recursion tables from `free_lo`.
//! - `D`: the chain digests, lane `l < 4` at `d_off + l·2^log_n` (an aligned 4-column cube).
//! - `KS` (`ks_log + 6` variables): its own slots `in` 0–24, `mid` 25–49, `Y` lanes 0–13 in 50–63.
//! - `KSY2` (KS `Y` lanes 14–24, one `2^ks_log` column each), `X` (`X_l`, the KS messages of rows `≥ 2^rec_rows_log`).
//! - `P20` (ν = 24): `D` 0, `KS` 4·2^20, `KSY2` 6·2^20, `X` 6·2^20 + 2^19, tables from 7·2^20.
//!   `P8` (ν = 23): `KS` 0, `KSY2` 2^20, `X` 2^20 + 2^18, `D` 2^20 + 2^19.
//!
//! `C_rec` (`2^(rec_rows_log + 5)` words): column `c` at `c·2^rec_rows_log`: the 17 stream columns `M_l`, then
//! `σ'`, then 14 zero columns. With the recursion part zero (`b = 0` convention, WP-15b fills it) it is zero.

use crate::lv::keccak_gkr::{Shape, Witness};
use crate::lv::primitives::field::F64;
use crate::lvm::layout;
use crate::lvm::params::{GKR_DEPTH, LANES, Params, REC_STREAM_COLS, SLOT_LOG, TAPE_DEPTH};
use crate::oracle::Digest;

/// `log2` of the `D` block's lanes (4).
pub const D_LOG: usize = 2;

/// Where every column of the two commitments sits (word offsets).
#[derive(Clone, Debug)]
pub struct Layout {
    pub log_n: usize,
    pub ks_log: usize,
    pub rec_log: usize,
    pub nu_main: usize,
    pub nu_rec: usize,
    /// S2: the chain digests `D_l` (4 lanes × `2^log_n`), one aligned block (BLUEPRINT2 §1.1, T-P1 C.1).
    pub d_off: usize,
    pub ks_off: usize,
    pub ksy2_off: usize,
    pub x_off: usize,
    /// The end of the fixed blocks: where the recursion tables go.
    free_lo: usize,
}

/// The KS slot of `Y` lane 0; lanes `0..KS_Y_IN_BLOCK` are in the KS block.
pub const KS_Y_SLOT: usize = 50;
pub const KS_Y_IN_BLOCK: usize = 14;

impl Layout {
    pub fn new(p: &Params) -> Self {
        // S2 (T-P1 C.1 = FRZ-0's rule): the fixed blocks largest first from word 0, ties in the order D, KS, KSY2, X
        // (each a power of two, so each lands aligned to its size); the recursion tables from the end (`free_lo`)
        let (d_vars, ks_vars) = (p.log_n + D_LOG, p.ks_log + SLOT_LOG);
        let ksy2 = 16usize << p.ks_log;
        let mut blocks = [(0usize, 1usize << d_vars), (1, 1usize << ks_vars), (2, ksy2), (3, 32usize << p.rec_rows_log)];
        blocks.sort_by_key(|&(k, size)| (std::cmp::Reverse(size), k));
        let mut off = [0usize; 4];
        let mut at = 0usize;
        for (k, size) in blocks {
            off[k] = at;
            at += size;
        }
        let [d_off, ks_off, spare, x_off] = off;
        let l = Self {
            log_n: p.log_n,
            ks_log: p.ks_log,
            rec_log: p.rec_rows_log,
            nu_main: p.nu_main,
            nu_rec: p.nu_rec(),
            d_off,
            ks_off,
            ksy2_off: spare,
            x_off,
            free_lo: at,
        };
        assert!(l.free_lo <= 1 << p.nu_main, "the layout fits C_main");
        // the rule's offsets are the shared layout's (`layout.rs`, generated with Lean's `LvmLayout` from params.py)
        let b = layout::of(p.name);
        assert_eq!((b.nu_main, b.d_off, b.ks_off, b.ksy2_off, b.x_off, b.free_lo),
            (l.nu_main, l.d_off, l.ks_off, l.ksy2_off, l.x_off, l.free_lo), "layout.rs is this layout");
        assert_eq!(l.d_off % (1 << d_vars), 0);
        assert_eq!(l.ks_off % (1 << ks_vars), 0);
        assert_eq!(l.ksy2_off % ksy2, 0);
        assert_eq!(l.x_off % (32 << l.rec_log), 0);
        assert_eq!(p.ks_log, p.rec_rows_log + 1, "KS rows: the stream half, then the X half");
        l
    }
    pub fn d_vars(&self) -> usize {
        self.log_n + D_LOG
    }
    pub fn ks_vars(&self) -> usize {
        self.ks_log + SLOT_LOG
    }
    /// The `D` column of lane `l < 4`.
    pub fn d(&self, l: usize) -> usize {
        self.d_off + (l << self.log_n)
    }
    pub fn ks_slot(&self, s: usize) -> usize {
        self.ks_off + (s << self.ks_log)
    }
    pub fn ks_y(&self, l: usize) -> usize {
        if l < KS_Y_IN_BLOCK { self.ks_slot(KS_Y_SLOT + l) } else { self.ksy2_off + ((l - KS_Y_IN_BLOCK) << self.ks_log) }
    }
    pub fn x(&self, l: usize) -> usize {
        self.x_off + (l << self.rec_log)
    }
    /// The first word above the fixed blocks (`layout.rs`; v1: the end of `X`, which takes 32 columns of
    /// `2^rec`): where the recursion tables go.
    pub fn free_lo(&self) -> usize {
        self.free_lo
    }
    /// `C_rec` column `c`.
    pub fn rec_col(&self, c: usize) -> usize {
        c << self.rec_log
    }
}

/// Little-endian lanes of a digest.
pub fn digest_lanes(d: &Digest) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap()))
}

pub fn lanes_digest(l: &[u64]) -> Digest {
    let mut d = [0u8; 32];
    for i in 0..4 {
        d[8 * i..8 * i + 8].copy_from_slice(&l[i].to_le_bytes());
    }
    d
}

/// The chain table `CH`: `in_0 = Pad43(s)`, `in_{i+1} = Pad43(Y_i)` for `i + 1 < n`; S1 (BLUEPRINT2 §2.1, A9 deleted):
/// rows `≥ n` hold the zero input ([`Chain::run_gated`]). [`Chain::run`] is v1's walk to `2^log_n` rows, kept for tests.
pub struct Chain {
    pub shape: Shape,
    pub inputs: Vec<[u64; LANES]>,
    /// Lanes 0–3 of every row's output.
    pub y: Vec<[u64; 4]>,
}

impl Chain {
    #[allow(dead_code)]
    pub fn run(log_n: usize, s: &Digest) -> Self {
        Self::run_notify(log_n, s, 0, |_| {})
    }
    /// [`Chain::run`], calling `at_end(chainEnd s n_end)` as soon as row `n_end − 1` is done (`n_end = 0`: never).
    pub fn run_notify(log_n: usize, s: &Digest, n_end: usize, mut at_end: impl FnMut(Digest)) -> Self {
        let n = 1usize << log_n;
        let mut inputs = Vec::with_capacity(n);
        let mut y = Vec::with_capacity(n);
        let mut d = *s;
        for i in 0..n {
            let a = crate::keccak::chain_block(&d);
            inputs.push(a);
            let mut b = a;
            // P-QUICK lever 2: the vendored single-state permutation (AVX-512 tier: 247 ns against 480 ns for
            // `keccak.rs`'s scalar one; `kat keccak` checks that the two agree)
            crate::lv::primitives::hash::keccak_f(&mut b);
            let out = [b[0], b[1], b[2], b[3]];
            y.push(out);
            d = lanes_digest(&out);
            if i + 1 == n_end {
                at_end(d);
            }
        }
        Self { shape: Shape::new(n, TAPE_DEPTH), inputs, y }
    }
    /// S1 (BLUEPRINT2 §2.1; P-GATE): walk only the `n` live rows; rows `≥ n` hold the all-zero input and
    /// `Y = Keccak-f(0)[0..4)`. `explicit` keeps the zero inputs as written rows (the dense reference prover,
    /// whose proof must be byte-identical to the padded one); otherwise `inputs` has `n` rows and the GKR
    /// witness pads the rest with leanVM's padding block.
    pub fn run_gated(log_n: usize, s: &Digest, n: usize, explicit: bool) -> Self {
        Self::run_gated_notify(log_n, s, n, explicit, |_| {})
    }
    /// [`Chain::run_gated`], calling `at_end(chainEnd s n)` as soon as row `n − 1` is done (P-QUICK lever 3).
    pub fn run_gated_notify(log_n: usize, s: &Digest, n: usize, explicit: bool, mut at_end: impl FnMut(Digest)) -> Self {
        let big = 1usize << log_n;
        let mut inputs = Vec::with_capacity(if explicit { big } else { n });
        let mut y = Vec::with_capacity(big);
        let mut d = *s;
        for _ in 0..n {
            let a = crate::keccak::chain_block(&d);
            inputs.push(a);
            let mut b = a;
            crate::lv::primitives::hash::keccak_f(&mut b);
            let out = [b[0], b[1], b[2], b[3]];
            y.push(out);
            d = lanes_digest(&out);
        }
        at_end(d);
        let mut z = [0u64; LANES];
        crate::lv::primitives::hash::keccak_f(&mut z);
        y.resize(big, [z[0], z[1], z[2], z[3]]);
        if explicit {
            inputs.resize(big, [0u64; LANES]);
        }
        Self { shape: Shape::new(big, TAPE_DEPTH), inputs, y }
    }
    /// `chainEnd s n` for `1 ≤ n ≤ 2^log_n`: lanes 0–3 of row `n − 1`.
    pub fn end(&self, n: usize) -> Digest {
        lanes_digest(&self.y[n - 1])
    }
}

/// The sponge table `KS`: per row `in_i[l] = cont_i·Y_{i−1}[l] + [l < 17]·Msg_l[i]` (`cont_0 = 0`).
pub struct Sponge {
    pub shape: Shape,
    pub inputs: Vec<[u64; LANES]>,
    pub outputs: Vec<[u64; LANES]>,
    pub cont: Vec<bool>,
    /// The messages, 17 lanes per row: rows `< 2^rec` are `C_rec`'s stream columns, the rest `X`.
    pub msg: Vec<[u64; REC_STREAM_COLS]>,
}

/// `cont` (structured, BLUEPRINT §4.2): rows `1 … B−1` (the trace sponge, `B` blocks) and rows 1–31 of the
/// 32-row WOTS leaf group (KS rows `≥ 2^rec`: 399 chain steps, 32 leaf rows, 16 path rows, leafStmt, nodeStmt).
pub fn cont_column(ks_log: usize, rec_log: usize, blocks: usize) -> Vec<bool> {
    let mut c = vec![false; 1 << ks_log];
    assert!(blocks <= 1 << rec_log);
    for i in 1..blocks {
        c[i] = true;
    }
    let leaf = (1 << rec_log) + 399;
    for j in 1..32 {
        c[leaf + j] = true;
    }
    c
}

impl Sponge {
    pub fn run(ks_log: usize, cont: Vec<bool>, msg: Vec<[u64; REC_STREAM_COLS]>) -> Self {
        let n = 1usize << ks_log;
        assert_eq!(msg.len(), n);
        let mut inputs = Vec::with_capacity(n);
        let mut outputs: Vec<[u64; LANES]> = Vec::with_capacity(n);
        for i in 0..n {
            let mut a = if cont[i] { outputs[i - 1] } else { [0u64; LANES] };
            for l in 0..REC_STREAM_COLS {
                a[l] ^= msg[i][l];
            }
            inputs.push(a);
            let mut b = a;
            crate::lv::primitives::hash::keccak_f(&mut b);
            outputs.push(b);
        }
        Self { shape: Shape::new(n, GKR_DEPTH), inputs, outputs, cont, msg }
    }
}

/// S2: write `D` (lanes 0–3 of every chain row's output; `z*[0..4)` on rows `≥ n`) into `C_main`. The tape's GKR
/// witness commits nothing (its inputs are virtual, BLUEPRINT2 §1.1): `Witness::generate_uncommitted`.
pub fn write_d(lay: &Layout, ch: &Chain, cmain: &mut [F64]) {
    for m in 0..4 {
        let o = lay.d(m);
        for (i, y) in ch.y.iter().enumerate() {
            cmain[o + i] = F64(y[m]);
        }
    }
}

/// Write `KS` (its committed lanes, its 25 `Y` lanes and the `X` messages) into `C_main`, and the stream
/// messages into `C_rec`.
pub fn write_ks(lay: &Layout, ks: &Sponge, cmain: &mut [F64], crec: &mut [F64]) -> Witness {
    let n = 1usize << lay.ks_log;
    let w = Witness::generate(ks.shape, &ks.inputs, &mut cmain[lay.ks_off..lay.ks_off + 50 * n]);
    write_ks_lanes(lay, ks, cmain, crec);
    w
}

/// The KS columns outside its GKR witness's slots `[ks_off, ks_off + 50·2^ks_log)`: its 25 `Y` lanes and the `X`
/// messages in `C_main`, the stream messages in `C_rec` (P-FIX: written before the witness, which
/// [`write_ks`] writes, so that the recursion tables can be built meanwhile).
pub fn write_ks_lanes(lay: &Layout, ks: &Sponge, cmain: &mut [F64], crec: &mut [F64]) {
    let half = 1usize << lay.rec_log;
    for l in 0..LANES {
        let o = lay.ks_y(l);
        for (i, y) in ks.outputs.iter().enumerate() {
            cmain[o + i] = F64(y[l]);
        }
    }
    for l in 0..REC_STREAM_COLS {
        for i in 0..half {
            crec[lay.rec_col(l) + i] = F64(ks.msg[i][l]);
            cmain[lay.x(l) + i] = F64(ks.msg[half + i][l]);
        }
    }
}
