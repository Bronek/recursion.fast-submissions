//! The committed tables and where they sit (BLUEPRINT §3.1, §4.1–4.2, §11 A7, A9; WP-15a layout, sent to
//! WP-11a for `M3.chBlock`/`ksBlock`):
//!
//! `C_main` (`2^nu_main` K words):
//! - `P20` (`nu_main = log_n + 6`): the `CH` block is the whole of `C_main`: slot `s` at `s·2^20`, `in` in
//!   slots 0–24, `mid` 25–49, **`Y` lanes 0–3 in slots 52–55** (an aligned 4-slot cube, for the link's
//!   `Y` slices). The `KS` block (`ks_log + 6` variables) is `CH` slots 50–51; its own slots: `in` 0–24, `mid`
//!   25–49, `Y` lanes 0–13 in 50–63. `CH` slots 56–63: `KSY2` (KS `Y` lanes 14–24, one `2^ks_log` column
//!   each) then `X` (`X_l`, the KS messages of rows `≥ 2^rec_rows_log`, one `2^rec_rows_log` column each).
//! - `P8`: `KS` block at 0, `CH` block at `2^(ks_log+6)`, then `KSY2`, then `X`.
//!
//! `C_rec` (`2^(rec_rows_log + 5)` words): column `c` at `c·2^rec_rows_log`: the 17 stream columns `M_l`, then
//! `σ'`, then 14 zero columns. With the recursion part zero (`b = 0` convention, WP-15b fills it) it is zero.

use crate::lv::keccak_gkr::{Shape, Witness};
use crate::lv::primitives::field::F64;
use crate::lvm::params::{GKR_DEPTH, LANES, Params, REC_STREAM_COLS, SLOT_LOG};
use crate::oracle::Digest;

/// Where every column of the two commitments sits (word offsets).
#[derive(Clone, Debug)]
pub struct Layout {
    pub log_n: usize,
    pub ks_log: usize,
    pub rec_log: usize,
    pub nu_main: usize,
    pub nu_rec: usize,
    pub ch_off: usize,
    pub ks_off: usize,
    pub ksy2_off: usize,
    pub x_off: usize,
}

/// The CH slot of `Y` lane 0.
pub const CH_Y_SLOT: usize = 52;
/// The KS slot of `Y` lane 0; lanes `0..KS_Y_IN_BLOCK` are in the KS block.
pub const KS_Y_SLOT: usize = 50;
pub const KS_Y_IN_BLOCK: usize = 14;

impl Layout {
    pub fn new(p: &Params) -> Self {
        let (ch_vars, ks_vars) = (p.log_n + SLOT_LOG, p.ks_log + SLOT_LOG);
        let (ch_off, ks_off, spare) = if p.nu_main == ch_vars {
            assert!(ks_vars <= p.log_n + 1, "the KS block fits two CH slots");
            (0, 50usize << p.log_n, 56usize << p.log_n)
        } else {
            assert!(ks_vars >= ch_vars);
            (1usize << ks_vars, 0, (1usize << ks_vars) + (1usize << ks_vars.max(ch_vars)))
        };
        let ksy2 = 16usize << p.ks_log;
        let l = Self {
            log_n: p.log_n,
            ks_log: p.ks_log,
            rec_log: p.rec_rows_log,
            nu_main: p.nu_main,
            nu_rec: p.nu_rec(),
            ch_off,
            ks_off,
            ksy2_off: spare,
            x_off: spare + ksy2,
        };
        assert!(l.x_off + (32usize << l.rec_log) <= 1 << p.nu_main, "the layout fits C_main");
        assert_eq!(l.ch_off % (1 << ch_vars), 0);
        assert_eq!(l.ks_off % (1 << ks_vars), 0);
        assert_eq!(l.ksy2_off % ksy2, 0);
        assert_eq!(l.x_off % (32 << l.rec_log), 0);
        assert_eq!(p.ks_log, p.rec_rows_log + 1, "KS rows: the stream half, then the X half");
        l
    }
    pub fn ch_vars(&self) -> usize {
        self.log_n + SLOT_LOG
    }
    pub fn ks_vars(&self) -> usize {
        self.ks_log + SLOT_LOG
    }
    /// The CH column of slot `s`.
    pub fn ch_slot(&self, s: usize) -> usize {
        self.ch_off + (s << self.log_n)
    }
    pub fn ch_y(&self, m: usize) -> usize {
        self.ch_slot(CH_Y_SLOT + m)
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
    /// The first word above WP-15a's tables (`X` takes 32 columns of `2^rec`): where the recursion tables go.
    pub fn free_lo(&self) -> usize {
        self.x_off + (32usize << self.rec_log)
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

/// The chain table `CH`: `in_0 = Pad43(s)`, `in_{i+1} = Pad43(Y_i)`, continued to `2^log_n` rows (A9).
pub struct Chain {
    pub shape: Shape,
    pub inputs: Vec<[u64; LANES]>,
    /// Lanes 0–3 of every row's output.
    pub y: Vec<[u64; 4]>,
}

impl Chain {
    pub fn run(log_n: usize, s: &Digest) -> Self {
        let n = 1usize << log_n;
        let mut inputs = Vec::with_capacity(n);
        let mut y = Vec::with_capacity(n);
        let mut d = *s;
        for _ in 0..n {
            let a = crate::keccak::chain_block(&d);
            inputs.push(a);
            let mut b = a;
            crate::keccak::keccak_f(&mut b);
            let out = [b[0], b[1], b[2], b[3]];
            y.push(out);
            d = lanes_digest(&out);
        }
        Self { shape: Shape::new(n, GKR_DEPTH), inputs, y }
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
            crate::keccak::keccak_f(&mut b);
            outputs.push(b);
        }
        Self { shape: Shape::new(n, GKR_DEPTH), inputs, outputs, cont, msg }
    }
}

/// Write `CH` (its GKR witness's committed lanes and its `Y`) into `C_main`.
pub fn write_ch(lay: &Layout, ch: &Chain, cmain: &mut [F64]) -> Witness {
    let n = 1usize << lay.log_n;
    let w = Witness::generate(ch.shape, &ch.inputs, &mut cmain[lay.ch_off..lay.ch_off + 50 * n]);
    for m in 0..4 {
        let o = lay.ch_y(m);
        for (i, y) in ch.y.iter().enumerate() {
            cmain[o + i] = F64(y[m]);
        }
    }
    w
}

/// Write `KS` (its committed lanes, its 25 `Y` lanes and the `X` messages) into `C_main`, and the stream
/// messages into `C_rec`.
pub fn write_ks(lay: &Layout, ks: &Sponge, cmain: &mut [F64], crec: &mut [F64]) -> Witness {
    let n = 1usize << lay.ks_log;
    let half = 1usize << lay.rec_log;
    let w = Witness::generate(ks.shape, &ks.inputs, &mut cmain[lay.ks_off..lay.ks_off + 50 * n]);
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
    w
}
