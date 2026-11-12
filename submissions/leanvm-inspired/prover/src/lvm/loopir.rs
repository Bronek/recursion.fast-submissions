//! LoopIR witness generation (WP-15b; BLUEPRINT §4.5, WP-10's `LvmLoopIR`/`LvmLoopTable`, transcribed): the
//! program as data (a blob dumped from Lean), its layout, the interpreter, the pieces and every piece's table
//! (committed columns in `Shape.committed` order, fixed columns `Program.fval`), the read counts and the bus
//! messages.
//!
//! **Blob** (`LOOPIR1`, whitespace-separated decimal tokens, written by a Lean dumper
//! from the Lean `Program`):
//! `LOOPIR1 nInK nInE nBlocks {block} nGlue {glue}`; block = `nDims {dim} nRows {row}`;
//! row = `op [k k' | lo m] ty nArgs {ty base nStrides {stride}}`; op 0 muladd, 1 lin (then `k k'` as `FK.val`),
//! 2 assert0, 3 loadE, 4 fixmul, 5 readd (then `lo m`); ty 0 = `K`, 1 = `E`.
//!
//! **Semantics** (each item is the Lean definition of the same name):
//! - result cells are dense: instance `(b, jf, t)` writing `τ` writes `start τ b + tw τ·jf + rank τ t`;
//! - `interp` runs blocks, loop indices (dimension 0 fastest), template rows; `fixmul`'s `F` is the glue
//!   matrix `fixMat [j₀, j₁]` (precomputed once, WP-10's speed note);
//! - pieces: per block, per row shape in order of first use, the binary decomposition of its rows; piece row
//!   `x` is loop index `x % size`, template row `ts[x / size]`;
//! - read counts (WP-10 §4 "WP-15"): reads are numbered per cell in the order of `Program.prows` (pieces,
//!   rows, operands, then `readd`'s computed read); the `t`-th read has `cnt = g^t`; a cell's finalize count
//!   is `g^{reads}` (results: the `fin` column; inputs: [`Tables::in_fin`], for the input tables).

use crate::lv::primitives::field::{F64, F192, g_pow};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    K,
    E,
}

impl Ty {
    pub fn limbs(self) -> usize {
        match self {
            Ty::K => 1,
            Ty::E => 3,
        }
    }
    fn ix(self) -> usize {
        match self {
            Ty::K => 0,
            Ty::E => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Addr {
    pub ty: Ty,
    pub base: usize,
    pub strides: Vec<usize>,
}

impl Addr {
    /// `Addr.at`: `base + dot strides j` (the shorter list decides).
    pub fn at(&self, j: &[usize]) -> usize {
        self.base + self.strides.iter().zip(j).map(|(s, x)| s * x).sum::<usize>()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    MulAdd,
    Lin(F64, F64),
    Assert0,
    LoadE,
    FixMul,
    Readd(usize, u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    MulAdd,
    Lin,
    Assert0,
    LoadE,
    FixMul,
    Readd,
}

impl Op {
    pub fn kind(self) -> Kind {
        match self {
            Op::MulAdd => Kind::MulAdd,
            Op::Lin(..) => Kind::Lin,
            Op::Assert0 => Kind::Assert0,
            Op::LoadE => Kind::LoadE,
            Op::FixMul => Kind::FixMul,
            Op::Readd(..) => Kind::Readd,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Row {
    pub op: Op,
    pub ty: Ty,
    pub args: Vec<Addr>,
}

impl Row {
    /// `Row.writes`.
    pub fn writes(&self) -> Option<Ty> {
        if self.op == Op::Assert0 { None } else { Some(self.ty) }
    }
    /// `Row.shape`.
    pub fn shape(&self) -> Shape {
        let kind = self.op.kind();
        Shape { kind, ty: if kind == Kind::Assert0 { Ty::K } else { self.ty }, args: self.args.iter().map(|a| a.ty).collect() }
    }
}

#[derive(Clone, Debug)]
pub struct Block {
    pub dims: Vec<u32>,
    pub tpl: Vec<Row>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub n_in: [usize; 2],
    pub blocks: Vec<Block>,
    pub glue: Vec<usize>,
}

/// A row shape: what a piece's columns and constraints depend on.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Shape {
    pub kind: Kind,
    pub ty: Ty,
    pub args: Vec<Ty>,
}

/// A committed column of a piece (`Var` without `fix`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Var {
    Res(usize),
    Fin,
    Arg(usize, usize),
    Cnt(usize),
    Dcnt,
}

/// A fixed column (`FCol`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FCol {
    Res,
    Arg(usize),
    K,
    K2,
    F,
}

impl Shape {
    pub fn writes(&self) -> bool {
        self.kind != Kind::Assert0
    }
    /// `Shape.committed`.
    pub fn committed(&self) -> Vec<Var> {
        let mut v = Vec::new();
        if self.writes() {
            v.extend((0..self.ty.limbs()).map(Var::Res));
            v.push(Var::Fin);
        }
        for (o, t) in self.args.iter().enumerate() {
            v.extend((0..t.limbs()).map(|l| Var::Arg(o, l)));
            v.push(Var::Cnt(o));
        }
        if self.kind == Kind::Readd {
            v.push(Var::Dcnt);
        }
        v
    }
    /// `Shape.fcols`.
    pub fn fcols(&self) -> Vec<FCol> {
        let mut v = Vec::new();
        if self.writes() {
            v.push(FCol::Res);
        }
        v.extend((0..self.args.len()).map(FCol::Arg));
        if self.kind == Kind::Lin {
            v.extend([FCol::K, FCol::K2]);
        }
        if self.kind == Kind::FixMul {
            v.push(FCol::F);
        }
        v
    }
}

/// A piece: `2^a` template rows `ts` of one shape of block `blk`, times its loop indices.
#[derive(Clone, Debug)]
pub struct Piece {
    pub blk: usize,
    pub shape: Shape,
    pub a: u32,
    pub ts: Vec<usize>,
}

/// One row instance (`Inst`).
#[derive(Clone, Debug)]
pub struct Inst {
    pub blk: usize,
    pub jf: usize,
    pub j: Vec<usize>,
    pub t: usize,
    /// `clock` per memory: cells defined before the instance (the cell it writes).
    pub clock: [usize; 2],
}

/// The per-block layout numbers.
#[derive(Clone, Debug)]
pub struct BlockLay {
    pub lsize: u32,
    pub size: usize,
    pub tw: [usize; 2],
    /// `rank τ t` per template row.
    pub rank: Vec<[usize; 2]>,
    pub start: [usize; 2],
}

// ---------------------------------------------------------------- the blob

struct Toks<'a>(std::str::SplitAsciiWhitespace<'a>);

impl Toks<'_> {
    fn u(&mut self) -> u64 {
        self.0.next().expect("LoopIR blob: truncated").parse().expect("LoopIR blob: a number")
    }
    fn n(&mut self) -> usize {
        self.u() as usize
    }
    fn ty(&mut self) -> Ty {
        match self.u() {
            0 => Ty::K,
            1 => Ty::E,
            t => panic!("LoopIR blob: type {t}"),
        }
    }
}

impl Program {
    /// Parse a `LOOPIR1` blob (the program only; [`parse_blob`] also reads the `M3` section).
    pub fn parse(s: &str) -> Program {
        parse_blob(s).0
    }
}

/// How an input array's value columns are given (`InArr.vcols`, WP-9b/INT-2's PUB).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArrKind {
    /// Committed, aliasing a column that already lives in a commitment (the stream `M_l`, `X_l`, the KS
    /// digests): the cells' values are read from it.
    Aliased,
    /// Committed and written by the prover at its placement (the BITS outputs: values computed).
    Written,
    /// Public (`pubArr`): no committed value column; cell `x` is the header lane `sel[x]` (0 past the list).
    Public,
}

/// An input array of the M3 section (WP-9 `InArr`).
#[derive(Clone, Debug)]
pub struct ArrSpec {
    pub ty: Ty,
    pub tau: usize,
    pub base: usize,
    pub stride: usize,
    pub kind: ArrKind,
    /// Value placements `(in C_rec, offset)`, one per limb (a public array's is a dummy).
    pub val: Vec<(bool, usize)>,
    /// The finalize-count column's placement.
    pub fin: (bool, usize),
    /// A public array's lanes: indices into [`crate::lvm::m3::pub_lanes`].
    pub sel: Vec<usize>,
}

/// The M3 section of a blob (optional; WP-9's `lvmTabs Q pl groups arrs aux` inputs, dumped from Lean).
/// `M3 nGroups {tau nMem {piece off} nCom {rec off}} nArrs {ty tau base stride nVal {rec off} finRec finOff}`
/// (every array aliased), or (WP-15c) `M3B` with groups as `M3`, arrays
/// `{ty tau base stride kind nVal {rec off} finRec finOff [nSel {sel} if kind = 2]}` (kind 0 aliased, 1
/// written, 2 public), then `BITS nB {tau n rd nOut {kind a b c} {wc}^n {oc}^(nOut·n, output-major)
/// nCom {rec off}}` (WP-12b `BSpec`; output kind 0 shl a, 1 shr a, 2 bit a, 3 fld a b c).
/// Absent: the prover's defaults (`m3::default_groups`, `m3::place`, `m3::stream_arrays`).
#[derive(Clone, Debug, Default)]
pub struct M3Spec {
    /// Per group: `tau`, members `(piece, row offset)`, its committed columns' placements `(in C_rec, offset)`.
    pub groups: Vec<(usize, Vec<(usize, usize)>, Vec<(bool, usize)>)>,
    /// The input arrays.
    pub arrs: Vec<ArrSpec>,
    /// The BITS tables (aux).
    pub bits: Vec<crate::lvm::bits::BitsSpec>,
    /// Constant public lanes appended to [`crate::lvm::m3::pub_lanes`] (WP-16a: Q_link's static QLT table,
    /// `PUBX n {v}` after the BITS part; public arrays select them at index `pub_lanes_len + i`, A23: 706 + i).
    pub pubx: Vec<u64>,
    /// Free BITS words (`rd = false`) the prover computes (WP-16a, `FREE n {class kind cell}` after PUBX):
    /// kind 0 = the WOTS checksum `Σ (3 − dᵢ)` of the digest in cells `cell..cell+4` (Q_sig's `cs` class).
    pub free: Vec<(usize, u32, usize)>,
}

/// Parse a blob: the program and, if present, its M3 section.
pub fn parse_blob(s: &str) -> (Program, Option<M3Spec>) {
    {
        let mut t = Toks(s.split_ascii_whitespace());
        assert_eq!(t.0.next(), Some("LOOPIR1"), "LoopIR blob magic");
        let n_in = [t.n(), t.n()];
        let nb = t.n();
        let mut blocks = Vec::with_capacity(nb);
        for _ in 0..nb {
            let nd = t.n();
            let dims = (0..nd).map(|_| t.u() as u32).collect();
            let nr = t.n();
            let mut tpl = Vec::with_capacity(nr);
            for _ in 0..nr {
                let op = match t.u() {
                    0 => Op::MulAdd,
                    1 => Op::Lin(F64(t.u()), F64(t.u())),
                    2 => Op::Assert0,
                    3 => Op::LoadE,
                    4 => Op::FixMul,
                    5 => Op::Readd(t.n(), t.u() as u32),
                    o => panic!("LoopIR blob: op {o}"),
                };
                let ty = t.ty();
                let na = t.n();
                let args = (0..na)
                    .map(|_| {
                        let ty = t.ty();
                        let base = t.n();
                        let ns = t.n();
                        Addr { ty, base, strides: (0..ns).map(|_| t.n()).collect() }
                    })
                    .collect();
                tpl.push(Row { op, ty, args });
            }
            blocks.push(Block { dims, tpl });
        }
        let ng = t.n();
        let glue = (0..ng).map(|_| t.n()).collect();
        let q = Program { n_in, blocks, glue };
        let m3 = match t.0.next() {
            None => None,
            Some(sec @ ("M3" | "M3B")) => {
                let v2 = sec == "M3B";
                let pl = |t: &mut Toks| (t.u() == 1, t.n());
                let groups = (0..t.n())
                    .map(|_| {
                        let tau = t.n();
                        let mem = (0..t.n()).map(|_| (t.n(), t.n())).collect();
                        let com = (0..t.n()).map(|_| pl(&mut t)).collect();
                        (tau, mem, com)
                    })
                    .collect();
                let arrs = (0..t.n())
                    .map(|_| {
                        let (ty, tau, base, stride) = (t.ty(), t.n(), t.n(), t.n());
                        let kind = if !v2 {
                            ArrKind::Aliased
                        } else {
                            match t.u() {
                                0 => ArrKind::Aliased,
                                1 => ArrKind::Written,
                                2 => ArrKind::Public,
                                k => panic!("LoopIR blob: array kind {k}"),
                            }
                        };
                        let val: Vec<(bool, usize)> = (0..t.n()).map(|_| pl(&mut t)).collect();
                        let fin = pl(&mut t);
                        assert_eq!(val.len(), if kind == ArrKind::Public { 1 } else { ty.limbs() }, "LoopIR blob: a value placement per limb");
                        let sel = if kind == ArrKind::Public { (0..t.n()).map(|_| t.n()).collect() } else { Vec::new() };
                        ArrSpec { ty, tau, base, stride, kind, val, fin, sel }
                    })
                    .collect();
                let mut bits = Vec::new();
                if v2 {
                    assert_eq!(t.0.next(), Some("BITS"), "LoopIR blob: the M3B section's BITS part");
                    for _ in 0..t.n() {
                        use crate::lvm::bits::BOut;
                        let (tau, n, rd, no) = (t.n(), t.n(), t.u() == 1, t.n());
                        let outs = (0..no)
                            .map(|_| {
                                let (k, a, b, c) = (t.u(), t.u() as u32, t.u() as u32, t.u() as u32);
                                // `BOut.Valid`
                                assert!(a < 64 && (k != 3 || (1 <= b && b + c <= 64)), "LoopIR blob: BITS output {k} {a} {b} {c} not valid");
                                match k {
                                    0 => BOut::Shl(a),
                                    1 => BOut::Shr(a),
                                    2 => BOut::Bit(a),
                                    3 => BOut::Fld(a, b, c),
                                    k => panic!("LoopIR blob: BITS output kind {k}"),
                                }
                            })
                            .collect();
                        let wc = (0..n).map(|_| t.n()).collect();
                        let oc = (0..no).map(|_| (0..n).map(|_| t.n()).collect()).collect();
                        let pl = (0..t.n()).map(|_| pl(&mut t)).collect();
                        bits.push(crate::lvm::bits::BitsSpec { tau, n, rd, outs, wc, oc, pl });
                    }
                }
                let mut pubx = Vec::new();
                let mut free = Vec::new();
                if let Some(tok) = t.0.next() {
                    assert_eq!(tok, "PUBX", "LoopIR blob: PUBX after the BITS part");
                    pubx = (0..t.n()).map(|_| t.u()).collect();
                    if let Some(tok) = t.0.next() {
                        assert_eq!(tok, "FREE", "LoopIR blob: FREE after PUBX");
                        free = (0..t.n()).map(|_| (t.n(), t.u() as u32, t.n())).collect();
                    }
                }
                Some(M3Spec { groups, arrs, bits, pubx, free })
            }
            Some(x) => panic!("LoopIR blob: unexpected {x:?}"),
        };
        assert!(t.0.next().is_none(), "LoopIR blob: trailing tokens");
        (q, m3)
    }
}

impl Program {
    /// The layout numbers of every block (`lsize`, `size`, `tw`, `rank`, `start`).
    pub fn layout(&self) -> (Vec<BlockLay>, [usize; 2]) {
        let mut start = self.n_in;
        let mut v = Vec::with_capacity(self.blocks.len());
        for b in &self.blocks {
            let lsize: u32 = b.dims.iter().sum();
            let size = 1usize << lsize;
            let mut rank = Vec::with_capacity(b.tpl.len());
            let mut tw = [0usize; 2];
            for r in &b.tpl {
                rank.push(tw);
                if let Some(t) = r.writes() {
                    tw[t.ix()] += 1;
                }
            }
            v.push(BlockLay { lsize, size, tw, rank, start });
            for k in 0..2 {
                start[k] += tw[k] * size;
            }
        }
        (v, start)
    }

    /// `Program.pieces`.
    pub fn pieces(&self) -> Vec<Piece> {
        let mut out = Vec::new();
        for (b, blk) in self.blocks.iter().enumerate() {
            let mut shapes: Vec<Shape> = Vec::new();
            for r in &blk.tpl {
                let s = r.shape();
                if !shapes.contains(&s) {
                    shapes.push(s);
                }
            }
            for s in shapes {
                let rows: Vec<usize> = (0..blk.tpl.len()).filter(|&t| blk.tpl[t].shape() == s).collect();
                let mut off = 0;
                for a in (0..usize::BITS).rev().filter(|a| rows.len() >> a & 1 == 1) {
                    out.push(Piece { blk: b, shape: s.clone(), a, ts: rows[off..off + (1 << a)].to_vec() });
                    off += 1 << a;
                }
            }
        }
        out
    }
}

/// `unflat dims jf`.
pub fn unflat(dims: &[u32], mut n: usize) -> Vec<usize> {
    dims.iter()
        .map(|&d| {
            let x = n % (1 << d);
            n >>= d;
            x
        })
        .collect()
}

// ---------------------------------------------------------------- the run

/// The cells of a run of the interpreter.
pub struct Run {
    pub kc: Vec<F64>,
    pub ec: Vec<F192>,
    /// Every `assert0` holds.
    pub ok: bool,
    /// Every `readd` found its cell.
    pub inb: bool,
}

impl Run {
    fn rd(&self, t: Ty, n: usize) -> F192 {
        match t {
            Ty::K => F192::from(self.kc.get(n).copied().unwrap_or(F64::ZERO)),
            Ty::E => self.ec.get(n).copied().unwrap_or(F192::ZERO),
        }
    }
    fn put(&mut self, t: Ty, v: F192) {
        match t {
            Ty::K => self.kc.push(F64(v.c0)),
            Ty::E => self.ec.push(v),
        }
    }
}

/// The program with its layout, pieces and glue matrix: everything the interpreter and the tables need.
pub struct Compiled {
    pub q: Program,
    pub lay: Vec<BlockLay>,
    pub cells: [usize; 2],
    pub pieces: Vec<Piece>,
    /// `fixMat`: per glue column, its values on the rows of its piece (zero beyond).
    pub glue_mat: Vec<Vec<F64>>,
    /// `g^e` for every cell exponent `e < max(cells)` and every count.
    pub gp: Vec<F64>,
    /// P-FIX: the fixed columns of every table group built so far (`m3::group_table`), by `(tau, members)`.
    fcache: FixedCache,
    /// P-FIX2: the input-independent read counts of `tables_ext` (computed once, at the first build).
    counts: std::sync::OnceLock<Counts>,
}

type FixedCache = std::sync::Mutex<HashMap<(usize, Vec<(usize, usize)>), std::sync::Arc<Vec<Vec<F64>>>>>;

impl Compiled {
    pub fn new(q: Program) -> Self {
        let (lay, cells) = q.layout();
        let pieces = q.pieces();
        let n = cells[0].max(cells[1]) + 2;
        let gp = crate::lv::primitives::field::g_powers(n);
        let mut c = Compiled { q, lay, cells, pieces, glue_mat: Vec::new(), gp, fcache: Default::default(), counts: Default::default() };
        let mut gm = Vec::new();
        for p in c.pieces.iter().filter(|p| c.q.glue.contains(&p.blk)) {
            for col in p.shape.fcols().into_iter().filter(|&f| f != FCol::F) {
                gm.push((0..1usize << c.height(p)).map(|x| c.fval_basic(p, col, x)).collect());
            }
        }
        c.glue_mat = gm;
        c
    }

    pub fn g(&self, e: usize) -> F64 {
        self.gp.get(e).copied().unwrap_or_else(|| g_pow(e))
    }

    /// `log₂` of a piece's height.
    pub fn height(&self, p: &Piece) -> u32 {
        p.a + self.lay[p.blk].lsize
    }

    /// `Program.inst b jf t`.
    pub fn inst(&self, b: usize, jf: usize, t: usize) -> Inst {
        let l = &self.lay[b];
        let clock = [0, 1].map(|k| l.start[k] + l.tw[k] * jf + l.rank[t][k]);
        Inst { blk: b, jf, j: unflat(&self.q.blocks[b].dims, jf), t, clock }
    }

    /// `Program.pinst p x`.
    pub fn pinst(&self, p: &Piece, x: usize) -> Inst {
        let size = self.lay[p.blk].size;
        self.inst(p.blk, x % size, p.ts[x / size])
    }

    fn row(&self, i: &Inst) -> &Row {
        &self.q.blocks[i.blk].tpl[i.t]
    }

    /// `fvalBasic` (`F` is `0`).
    pub fn fval_basic(&self, p: &Piece, c: FCol, x: usize) -> F64 {
        let i = self.pinst(p, x);
        let r = self.row(&i);
        match c {
            FCol::Res => self.g(i.clock[r.ty.ix()]),
            FCol::Arg(o) => self.g(r.args[o].at(&i.j)),
            FCol::K => match r.op {
                Op::Lin(k, _) => k,
                _ => F64::ZERO,
            },
            FCol::K2 => match r.op {
                Op::Lin(_, k) => k,
                _ => F64::ZERO,
            },
            FCol::F => F64::ZERO,
        }
    }

    /// `fixMat j`.
    /// The fixed columns of the table group `key`, from the cache, or `make`'s (then cached). They depend on
    /// the program only, so every build of the same program gets the same columns.
    pub fn fixed_cols(&self, key: (usize, Vec<(usize, usize)>), make: impl FnOnce() -> Vec<Vec<F64>>) -> std::sync::Arc<Vec<Vec<F64>>> {
        if let Some(v) = self.fcache.lock().unwrap().get(&key) {
            return v.clone();
        }
        let v = std::sync::Arc::new(make());
        self.fcache.lock().unwrap().entry(key).or_insert(v).clone()
    }

    pub fn fix_mat(&self, j: &[usize]) -> F64 {
        let (c, x) = (j.first().copied().unwrap_or(0), j.get(1).copied().unwrap_or(0));
        self.glue_mat.get(c).and_then(|col| col.get(x)).copied().unwrap_or(F64::ZERO)
    }

    /// `fval`.
    pub fn fval(&self, p: &Piece, c: FCol, x: usize) -> F64 {
        match c {
            FCol::F => self.fix_mat(&self.pinst(p, x).j),
            c => self.fval_basic(p, c, x),
        }
    }

    /// `interp`: run every instance in order from the inputs.
    pub fn interp(&self, in_k: &[F64], in_e: &[F192]) -> Run {
        assert_eq!([in_k.len(), in_e.len()], self.q.n_in, "input sizes");
        let mut s = Run { kc: Vec::with_capacity(self.cells[0]), ec: Vec::with_capacity(self.cells[1]), ok: true, inb: true };
        s.kc.extend_from_slice(in_k);
        s.ec.extend_from_slice(in_e);
        let mut found: HashMap<(usize, u32), HashMap<u64, usize>> = HashMap::new();
        // dev: `LVM_QDEBUG=1` lists the first failing assertions and `readd` misses (block, iteration, row)
        let dbg = std::env::var_os("LVM_QDEBUG").is_some();
        let mut nbad = 0usize;
        if dbg {
            eprintln!("lvm qdebug: interp start");
        }
        // P-FIX: the block indices `j` kept in one buffer (no `unflat` per iteration), and rows whose result and
        // arguments are all `K` cells computed in `K` (the same values: `K` is a subfield of `E`, and `put` keeps
        // a `K` result's `c0`)
        let mut j: Vec<usize> = Vec::new();
        for (b, blk) in self.q.blocks.iter().enumerate() {
            let all_k: Vec<bool> = blk.tpl.iter().map(|r| r.ty == Ty::K && r.args.iter().all(|a| a.ty == Ty::K)).collect();
            j.clear();
            j.resize(blk.dims.len(), 0);
            for jf in 0..self.lay[b].size {
                let mut rest = jf;
                for (jk, &d) in j.iter_mut().zip(&blk.dims) {
                    *jk = rest % (1 << d);
                    rest >>= d;
                }
                let j = &j[..];
                for (ri, r) in blk.tpl.iter().enumerate() {
                    if all_k[ri] {
                        let rk = |s: &Run, o: usize| s.kc.get(r.args[o].at(j)).copied().unwrap_or(F64::ZERO);
                        let v = match r.op {
                            Op::MulAdd => Some(rk(&s, 0) * rk(&s, 1) + rk(&s, 2)),
                            Op::Lin(k, k2) => Some(rk(&s, 0) + rk(&s, 1) * k + k2),
                            Op::FixMul => Some(rk(&s, 0) * self.fix_mat(j) + rk(&s, 1)),
                            _ => None,
                        };
                        if let Some(v) = v {
                            s.kc.push(v);
                            continue;
                        }
                    }
                    let rd = |s: &Run, o: usize| s.rd(r.args[o].ty, r.args[o].at(j));
                    match r.op {
                        Op::MulAdd => {
                            let v = rd(&s, 0) * rd(&s, 1) + rd(&s, 2);
                            s.put(r.ty, v)
                        }
                        Op::Lin(k, k2) => {
                            let v = rd(&s, 0) + rd(&s, 1).mul_base(k) + F192::from(k2);
                            s.put(r.ty, v)
                        }
                        Op::Assert0 => {
                            let z = (rd(&s, 1) * rd(&s, 0)).is_zero();
                            if !z && dbg && nbad < 4000 {
                                nbad += 1;
                                eprintln!("lvm qdebug: assert0 fails: block {b} iteration {jf} row {ri} (cells {} {})", r.args[0].at(j), r.args[1].at(j));
                            }
                            s.ok &= z
                        }
                        Op::LoadE => {
                            let v = rd(&s, 0) + F192::Y * rd(&s, 1) + F192::Y * F192::Y * rd(&s, 2);
                            s.put(r.ty, v)
                        }
                        Op::FixMul => {
                            let v = rd(&s, 0).mul_base(self.fix_mat(j)) + rd(&s, 1);
                            s.put(r.ty, v)
                        }
                        Op::Readd(lo, m) => {
                            let alpha = rd(&s, 0).c0;
                            let tab = found.entry((lo, m)).or_insert_with(|| {
                                (0..1usize << m).rev().map(|i| (self.g(lo + i).0, lo + i)).collect()
                            });
                            match tab.get(&alpha) {
                                Some(&e) => {
                                    let v = s.rd(r.ty, e);
                                    s.put(r.ty, v)
                                }
                                None => {
                                    if dbg && nbad < 4000 {
                                        nbad += 1;
                                        eprintln!("lvm qdebug: readd misses: block {b} iteration {jf} row {ri}");
                                    }
                                    s.put(r.ty, F192::ZERO);
                                    s.inb = false
                                }
                            }
                        }
                    }
                }
            }
        }
        debug_assert_eq!([s.kc.len(), s.ec.len()], self.cells);
        s
    }
}

// ---------------------------------------------------------------- the tables

/// Every piece's committed columns (in `Shape.committed` order, `2^height` words each), and the inputs'
/// finalize counts.
pub struct Tables {
    pub cols: Vec<Vec<Vec<F64>>>,
    /// `g^{reads}` of every input cell, per memory.
    pub in_fin: [Vec<F64>; 2],
    /// Reads per cell, per memory (all cells).
    pub reads: [Vec<u32>; 2],
    /// The counts `g^t` of the extra `K` reads ([`Compiled::tables_ext`]), in their order.
    pub extra_cnt: Vec<F64>,
}

fn limbs(t: Ty, v: F192) -> [u64; 3] {
    match t {
        Ty::K => [v.c0, 0, 0],
        Ty::E => [v.c0, v.c1, v.c2],
    }
}

impl Compiled {
    /// Fill every piece's table from a run (WP-10 §4 "WP-15").
    pub fn tables(&self, run: &Run) -> Tables {
        self.tables_ext(run, &[])
    }

    /// [`Compiled::tables`] with `extra` further reads of `K` cells (the aux tables' reads, WP-9b
    /// `aux_read`: the BITS words and outputs, padding rows included), numbered after the program's reads
    /// of the same cell; the finalize counts include them.
    pub fn tables_ext(&self, run: &Run, extra: &[usize]) -> Tables {
        let t = self.tables_fast(run, extra);
        if std::env::var_os("LVM_TABLES_REF").is_some() {
            let r = self.tables_ext_ref(run, extra);
            assert!(t.cols == r.cols && t.in_fin == r.in_fin && t.reads == r.reads && t.extra_cnt == r.extra_cnt, "P-FIX2 tables = the reference tables");
            eprintln!("lvm: LVM_TABLES_REF: the tables equal the reference");
        }
        t
    }

    /// The single serial pass (P-QUICK lever 5b), kept as the reference of [`Compiled::tables_ext`].
    pub fn tables_ext_ref(&self, run: &Run, extra: &[usize]) -> Tables {
        let mut reads = [vec![0u32; self.cells[0]], vec![0u32; self.cells[1]]];
        let mut dlog: HashMap<(usize, u32), HashMap<u64, usize>> = HashMap::new();
        let mut cols: Vec<Vec<Vec<F64>>> = Vec::with_capacity(self.pieces.len());
        // the result cell of every writer row, for its `fin` (filled when every read is counted)
        let mut fin_of: Vec<(usize, usize, Ty, Vec<usize>)> = Vec::new();
        for (n, p) in self.pieces.iter().enumerate() {
            let h = 1usize << self.height(p);
            let com = p.shape.committed();
            let mut c = vec![vec![F64::ZERO; h]; com.len()];
            let at = |v: Var| com.iter().position(|&u| u == v).unwrap();
            // P-QUICK lever 5b: the column of every variable once per piece (`at`, not per cell; usize::MAX
            // where `at` would fail, so that a use still panics), and each row's instance (`pinst`: `jf`, `t`,
            // `j`, `clock`) into one buffer instead of a fresh `Inst` per row
            let pos = |v: Var| com.iter().position(|&u| u == v).unwrap_or(usize::MAX);
            let n_args = p.shape.args.len().max(self.q.blocks[p.blk].tpl.iter().map(|r| r.args.len()).max().unwrap_or(0));
            let res_pos: [usize; 3] = std::array::from_fn(|l| pos(Var::Res(l)));
            let arg_pos: Vec<[usize; 3]> = (0..n_args).map(|o| std::array::from_fn(|l| pos(Var::Arg(o, l)))).collect();
            let cnt_pos: Vec<usize> = (0..n_args).map(|o| pos(Var::Cnt(o))).collect();
            let dcnt_pos = pos(Var::Dcnt);
            let lay = &self.lay[p.blk];
            let blk = &self.q.blocks[p.blk];
            let mut j = vec![0usize; blk.dims.len()];
            let mut fin_cells = Vec::new();
            for x in 0..h {
                let jf = x % lay.size;
                let t = p.ts[x / lay.size];
                let mut rest = jf;
                for (jk, &d) in j.iter_mut().zip(&blk.dims) {
                    *jk = rest % (1 << d);
                    rest >>= d;
                }
                let clock: [usize; 2] = [0, 1].map(|k| lay.start[k] + lay.tw[k] * jf + lay.rank[t][k]);
                let r = &blk.tpl[t];
                if let Some(t) = r.writes() {
                    let cell = clock[t.ix()];
                    let v = limbs(t, run.rd(t, cell));
                    for l in 0..t.limbs() {
                        c[res_pos[l]][x] = F64(v[l]);
                    }
                    fin_cells.push(cell);
                }
                for (o, a) in r.args.iter().enumerate() {
                    let e = a.at(&j);
                    let v = limbs(a.ty, run.rd(a.ty, e));
                    for l in 0..a.ty.limbs() {
                        c[arg_pos[o][l]][x] = F64(v[l]);
                    }
                    let k = &mut reads[a.ty.ix()][e];
                    c[cnt_pos[o]][x] = self.g(*k as usize);
                    *k += 1;
                }
                if let Op::Readd(lo, m) = r.op {
                    let alpha = run.rd(Ty::K, r.args[0].at(&j)).c0;
                    let tab = dlog.entry((lo, m)).or_insert_with(|| (0..1usize << m).map(|i| (self.g(lo + i).0, lo + i)).collect());
                    let e = *tab.get(&alpha).expect("readd: the cell (interp.inb)");
                    let k = &mut reads[r.ty.ix()][e];
                    c[dcnt_pos][x] = self.g(*k as usize);
                    *k += 1;
                }
            }
            if p.shape.writes() {
                fin_of.push((n, at(Var::Fin), p.shape.ty, fin_cells));
            }
            cols.push(c);
        }
        let extra_cnt = extra
            .iter()
            .map(|&e| {
                let k = &mut reads[0][e];
                let c = self.g(*k as usize);
                *k += 1;
                c
            })
            .collect();
        for (n, col, t, cells) in fin_of {
            for (x, e) in cells.into_iter().enumerate() {
                cols[n][col][x] = self.g(reads[t.ix()][e] as usize);
            }
        }
        let in_fin = [0, 1].map(|k| (0..self.q.n_in[k]).map(|e| self.g(reads[k][e] as usize)).collect());
        Tables { cols, in_fin, reads, extra_cnt }
    }

    /// Committed words of every piece (A12's budget).
    pub fn committed_words(&self) -> usize {
        self.pieces.iter().map(|p| (1usize << self.height(p)) * p.shape.committed().len()).sum()
    }
}

/// A bus message `⟨sep, addr, cnt, value limbs⟩` and its side.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Msg {
    pub push: bool,
    pub sep: u64,
    pub addr: u64,
    pub cnt: u64,
    pub val: Vec<u64>,
}

/// `sep τ` (`g^3`, `g^4`).
pub fn sep(t: Ty) -> F64 {
    g_pow(3 + t.ix())
}

impl Compiled {
    /// Every flush of every piece row (`Shape.flushes`: reads, bumped reads, seed, finalize), then the inputs'
    /// seeds and finalizes: the multiset the bus balances.
    pub fn messages(&self, run: &Run, tb: &Tables) -> Vec<Msg> {
        let mut out = Vec::new();
        for (n, p) in self.pieces.iter().enumerate() {
            let com = p.shape.committed();
            let at = |v: Var| com.iter().position(|&u| u == v).unwrap();
            let c = &tb.cols[n];
            for x in 0..1usize << self.height(p) {
                let i = self.pinst(p, x);
                let r = self.row(&i);
                let mut reads = Vec::new();
                for (o, a) in r.args.iter().enumerate() {
                    let val = (0..a.ty.limbs()).map(|l| c[at(Var::Arg(o, l))][x].0).collect();
                    reads.push(Msg { push: false, sep: sep(a.ty).0, addr: self.fval(p, FCol::Arg(o), x).0, cnt: c[at(Var::Cnt(o))][x].0, val });
                }
                if let Op::Readd(..) = r.op {
                    let val = (0..r.ty.limbs()).map(|l| c[at(Var::Res(l))][x].0).collect();
                    reads.push(Msg { push: false, sep: sep(r.ty).0, addr: c[at(Var::Arg(0, 0))][x].0, cnt: c[at(Var::Dcnt)][x].0, val });
                }
                let bumped: Vec<Msg> =
                    reads.iter().map(|m| Msg { push: true, cnt: crate::lv::primitives::field::mul_by_g(F64(m.cnt)).0, ..m.clone() }).collect();
                out.extend(reads);
                out.extend(bumped);
                if p.shape.writes() {
                    let val: Vec<u64> = (0..p.shape.ty.limbs()).map(|l| c[at(Var::Res(l))][x].0).collect();
                    let addr = self.fval(p, FCol::Res, x).0;
                    let s = sep(p.shape.ty).0;
                    out.push(Msg { push: true, sep: s, addr, cnt: 1, val: val.clone() });
                    out.push(Msg { push: false, sep: s, addr, cnt: c[at(Var::Fin)][x].0, val });
                }
            }
        }
        for t in [Ty::K, Ty::E] {
            for e in 0..self.q.n_in[t.ix()] {
                let val = limbs(t, run.rd(t, e))[..t.limbs()].to_vec();
                let (s, addr) = (sep(t).0, self.g(e).0);
                out.push(Msg { push: true, sep: s, addr, cnt: 1, val: val.clone() });
                out.push(Msg { push: false, sep: s, addr, cnt: tb.in_fin[t.ix()][e].0, val });
            }
        }
        out
    }
}

/// The dump the Lean check reads (`RQLoop.lean`), all little-endian `u64`: `nPieces`, per piece `h`, `nCols`,
/// the columns; per memory the inputs' finalize counts (`n`, then `n` words); the messages (`nMsg`, per
/// message `push sep addr cnt nVal val…`); then `ok`, `inb`.
pub fn dump(c: &Compiled, run: &Run, tb: &Tables, msgs: &[Msg]) -> Vec<u8> {
    let mut v: Vec<u64> = vec![c.pieces.len() as u64];
    for (n, p) in c.pieces.iter().enumerate() {
        v.push(c.height(p) as u64);
        v.push(tb.cols[n].len() as u64);
        for col in &tb.cols[n] {
            v.extend(col.iter().map(|x| x.0));
        }
    }
    for k in 0..2 {
        v.push(tb.in_fin[k].len() as u64);
        v.extend(tb.in_fin[k].iter().map(|x| x.0));
    }
    v.push(msgs.len() as u64);
    for m in msgs {
        v.extend([m.push as u64, m.sep, m.addr, m.cnt, m.val.len() as u64]);
        v.extend(&m.val);
    }
    v.push(run.ok as u64);
    v.push(run.inb as u64);
    v.iter().flat_map(|x| x.to_le_bytes()).collect()
}

/// Self-check: pushes and pulls form the same multiset.
pub fn balanced(msgs: &[Msg]) -> bool {
    let key = |m: &Msg| (m.sep, m.addr, m.cnt, m.val.clone());
    let mut a: Vec<_> = msgs.iter().filter(|m| m.push).map(key).collect();
    let mut b: Vec<_> = msgs.iter().filter(|m| !m.push).map(key).collect();
    a.sort();
    b.sort();
    a == b
}

/// A synthetic program of the real `Q`'s estimated size (dev benchmark, `sprove --synth`): `n_in` `K` inputs
/// (the stream lanes), a `loadE` block of `2^12` `E` cells, `big` blocks of `2^10` iterations with an
/// `E·E + E` and an `E + k·K` row, `small` blocks of `2^8` with `K` muladd, lin and assert0 rows, and a
/// glue block; every operand reads inputs or the `loadE` cells (WP-0's ≈ 5 M words, ≈ 760 pieces).
pub fn synthetic(n_in: usize, big: usize, small: usize) -> Program {
    let k = |b: usize, s: Vec<usize>| Addr { ty: Ty::K, base: b, strides: s };
    let e = |b: usize, s: Vec<usize>| Addr { ty: Ty::E, base: b, strides: s };
    let mut blocks = vec![Block { dims: vec![12], tpl: vec![Row { op: Op::LoadE, ty: Ty::E, args: vec![k(0, vec![3]), k(1, vec![3]), k(2, vec![3])] }] }];
    for i in 0..big {
        blocks.push(Block {
            dims: vec![10],
            tpl: vec![
                Row { op: Op::MulAdd, ty: Ty::E, args: vec![e(i % 7, vec![1]), e(1024 + i % 5, vec![2]), e(i % 3, vec![3])] },
                Row { op: Op::Lin(F64(3 + i as u64), F64(i as u64)), ty: Ty::E, args: vec![e(i % 11, vec![1]), k(17 * i % 1000, vec![17])] },
            ],
        });
    }
    for i in 0..small {
        blocks.push(Block {
            dims: vec![8],
            tpl: vec![
                Row { op: Op::MulAdd, ty: Ty::K, args: vec![k(i, vec![1]), k(300 + i, vec![5]), k(7, vec![])] },
                Row { op: Op::Lin(F64(5), F64(1)), ty: Ty::K, args: vec![k(i + 1, vec![1]), k(i + 2, vec![1])] },
                Row { op: Op::Assert0, ty: Ty::K, args: vec![k(n_in - 1, vec![]), k(n_in - 2, vec![])] },
            ],
        });
    }
    let glue: Vec<Row> = (0..2000)
        .map(|t| if t % 2 == 0 {
            Row { op: Op::MulAdd, ty: Ty::E, args: vec![e(t, vec![]), e(t + 1, vec![]), e(t + 2, vec![])] }
        } else {
            Row { op: Op::Lin(F64(t as u64), F64(1)), ty: Ty::K, args: vec![k(t, vec![]), k(t + 9, vec![])] }
        })
        .collect();
    blocks.push(Block { dims: vec![], tpl: glue });
    Program { n_in: [n_in, 0], blocks, glue: vec![] }
}

// ---------------------------------------------------------------- P-FIX2: the read counts before `ready`

/// The input-independent part of `tables_ext`'s read counts. Every read of a statically addressed cell gets the
/// count of the reads of that cell before it, in the program's order (pieces, rows, arguments, then a `Readd`
/// row's own read). Only `Readd` reads have data-dependent cells (a discrete log of their argument), and they
/// always land in their table `[lo, lo + 2^m)`: so the static reads' counts, *without* the `Readd` reads, are
/// computed once, and each build adds the `Readd` reads that precede a static read of the same cell.
pub struct Counts {
    /// Per piece: `(column, count per row)` of every `Cnt` column (`u32::MAX`: the row does not read; the column
    /// holds zero there).
    cnt: Vec<Vec<(usize, Vec<u32>)>>,
    /// Per piece: its `Dcnt` column, if it has `Readd` rows.
    dcnt: Vec<Option<usize>>,
    /// Static reads per cell, per memory.
    total: [Vec<u32>; 2],
    /// The `Readd` reads in order: `(sequence number, piece, row, memory, lo, m, the argument's K cell)`.
    readd: Vec<(u64, usize, usize, usize, usize, u32, usize)>,
    /// The static reads of every cell some `Readd` table covers, in order: `(memory, cell) ->
    /// [(sequence number, piece, column, row, static count)]`.
    sites: HashMap<(usize, usize), Vec<(u64, usize, usize, usize, u32)>>,
    /// The writer pieces' result cells (for `Fin`): `(piece, column, memory type, cells)`.
    fin_of: Vec<(usize, usize, Ty, Vec<usize>)>,
}

/// Worker threads of the value pass and the count conversion (plain scoped threads: the build runs beside the
/// tape witness's dispatch on the pool).
const BUILD_THREADS: usize = 6;

/// `f(i)` for `i < n` on `BUILD_THREADS` scoped threads taking indices in turn; the results in index order.
fn par_map<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let threads = BUILD_THREADS.min(crate::lv::parallel::num_threads()).min(n);
    if threads <= 1 {
        return (0..n).map(&f).collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let mut out: Vec<Option<T>> = (0..n).map(|_| None).collect();
    std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|_| {
                sc.spawn(|| {
                    let mut mine = Vec::new();
                    loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= n {
                            break mine;
                        }
                        mine.push((i, f(i)));
                    }
                })
            })
            .collect();
        for h in hs {
            for (i, t) in h.join().expect("a build task") {
                out[i] = Some(t);
            }
        }
    });
    out.into_iter().map(|t| t.expect("every task")).collect()
}

impl Compiled {
    /// The row walk of `tables_ext`: for every row `x` of piece `n`, its block indices, template and clock cells.
    #[inline(always)]
    fn rows_of(&self, n: usize, mut f: impl FnMut(usize, &[usize], &Row, [usize; 2])) {
        let p = &self.pieces[n];
        let h = 1usize << self.height(p);
        let lay = &self.lay[p.blk];
        let blk = &self.q.blocks[p.blk];
        let mut j = vec![0usize; blk.dims.len()];
        for x in 0..h {
            let jf = x % lay.size;
            let t = p.ts[x / lay.size];
            let mut rest = jf;
            for (jk, &d) in j.iter_mut().zip(&blk.dims) {
                *jk = rest % (1 << d);
                rest >>= d;
            }
            let clock: [usize; 2] = [0, 1].map(|k| lay.start[k] + lay.tw[k] * jf + lay.rank[t][k]);
            f(x, &j, &blk.tpl[t], clock);
        }
    }

    /// Piece `n`'s committed-column positions of `Res`, `Arg`, `Cnt`, `Dcnt` and `Fin` (`usize::MAX` if absent:
    /// a use panics, as in the reference).
    #[allow(clippy::type_complexity)]
    fn positions(&self, n: usize) -> ([usize; 3], Vec<[usize; 3]>, Vec<usize>, usize, usize) {
        let p = &self.pieces[n];
        let com = p.shape.committed();
        let pos = |v: Var| com.iter().position(|&u| u == v).unwrap_or(usize::MAX);
        let n_args = p.shape.args.len().max(self.q.blocks[p.blk].tpl.iter().map(|r| r.args.len()).max().unwrap_or(0));
        (
            std::array::from_fn(|l| pos(Var::Res(l))),
            (0..n_args).map(|o| std::array::from_fn(|l| pos(Var::Arg(o, l)))).collect(),
            (0..n_args).map(|o| pos(Var::Cnt(o))).collect(),
            pos(Var::Dcnt),
            pos(Var::Fin),
        )
    }

    fn counts(&self) -> &Counts {
        self.counts.get_or_init(|| {
            let mut total = [vec![0u32; self.cells[0]], vec![0u32; self.cells[1]]];
            // the cells some `Readd` table covers
            let mut covered: [Vec<bool>; 2] = [vec![false; self.cells[0]], vec![false; self.cells[1]]];
            for p in &self.pieces {
                for r in &self.q.blocks[p.blk].tpl {
                    if let Op::Readd(lo, m) = r.op {
                        for e in lo..(lo + (1usize << m)).min(self.cells[r.ty.ix()]) {
                            covered[r.ty.ix()][e] = true;
                        }
                    }
                }
            }
            let (mut cnt, mut dcnt, mut readd, mut fin_of) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
            let mut sites: HashMap<(usize, usize), Vec<(u64, usize, usize, usize, u32)>> = HashMap::new();
            let mut seq = 0u64;
            for n in 0..self.pieces.len() {
                let p = &self.pieces[n];
                let h = 1usize << self.height(p);
                let (_, _, cnt_pos, dcnt_pos, fin_pos) = self.positions(n);
                let mut cols: Vec<(usize, Vec<u32>)> = Vec::new();
                let mut col_of = vec![usize::MAX; cnt_pos.len()];
                let mut fin_cells = Vec::new();
                let mut has_readd = false;
                self.rows_of(n, |x, j, r, clock| {
                    if let Some(t) = r.writes() {
                        fin_cells.push(clock[t.ix()]);
                    }
                    for (o, a) in r.args.iter().enumerate() {
                        let (k, e) = (a.ty.ix(), a.at(j));
                        if col_of[o] == usize::MAX {
                            assert!(cnt_pos[o] != usize::MAX, "a read's count column");
                            col_of[o] = cols.len();
                            cols.push((cnt_pos[o], vec![u32::MAX; h]));
                        }
                        let c = &mut total[k][e];
                        cols[col_of[o]].1[x] = *c;
                        if covered[k][e] {
                            sites.entry((k, e)).or_default().push((seq, n, cnt_pos[o], x, *c));
                        }
                        *c += 1;
                        seq += 1;
                    }
                    if let Op::Readd(lo, m) = r.op {
                        assert!(dcnt_pos != usize::MAX, "a Readd row's count column");
                        has_readd = true;
                        readd.push((seq, n, x, r.ty.ix(), lo, m, r.args[0].at(j)));
                        seq += 1;
                    }
                });
                if p.shape.writes() {
                    fin_of.push((n, fin_pos, p.shape.ty, fin_cells));
                }
                cnt.push(cols);
                dcnt.push(has_readd.then_some(dcnt_pos));
            }
            if std::env::var_os("LVM_LOG").is_some() {
                eprintln!(
                    "lvm: read counts: {seq} reads, {} Readd, {} covered cells with {} static reads",
                    readd.len(),
                    sites.len(),
                    sites.values().map(|v| v.len()).sum::<usize>()
                );
            }
            Counts { cnt, dcnt, total, readd, sites, fin_of }
        })
    }

    /// [`Compiled::tables_ext_ref`]'s tables from the cached static counts, the `Readd` reads added; the value
    /// columns and the count columns are filled per piece on worker threads.
    fn tables_fast(&self, run: &Run, extra: &[usize]) -> Tables {
        let cs = self.counts();
        let mut reads = cs.total.clone();
        // the `Readd` reads in order: their cells, their counts, and per cell the sequence numbers of its reads
        let mut dlog: HashMap<(usize, u32), HashMap<u64, usize>> = HashMap::new();
        let mut events: HashMap<(usize, usize), Vec<u64>> = HashMap::new();
        let mut dval: Vec<(usize, usize, u32)> = Vec::with_capacity(cs.readd.len());
        for &(seq, n, x, k, lo, m, arg) in &cs.readd {
            let alpha = run.rd(Ty::K, arg).c0;
            let tab = dlog.entry((lo, m)).or_insert_with(|| (0..1usize << m).map(|i| (self.g(lo + i).0, lo + i)).collect());
            let e = *tab.get(&alpha).expect("readd: the cell (interp.inb)");
            let ev = events.entry((k, e)).or_default();
            let before_static = cs.sites.get(&(k, e)).map_or(0, |v| v.partition_point(|s| s.0 < seq));
            dval.push((n, x, (before_static + ev.len()) as u32));
            ev.push(seq);
            reads[k][e] += 1;
        }
        // the patches: a static read after `d` `Readd` reads of its cell counts `d` more
        let mut patch: Vec<Vec<(usize, usize, u32)>> = vec![Vec::new(); self.pieces.len()];
        for (key, ev) in &events {
            for &(seq, n, col, x, c) in cs.sites.get(key).map_or(&[][..], |v| &v[..]) {
                let d = ev.partition_point(|&t| t < seq);
                if d > 0 {
                    patch[n].push((col, x, c + d as u32));
                }
            }
        }
        let mut dby: Vec<Vec<(usize, u32)>> = vec![Vec::new(); self.pieces.len()];
        for &(n, x, c) in &dval {
            dby[n].push((x, c));
        }
        let g = |c: u32| if c == u32::MAX { F64::ZERO } else { self.g(c as usize) };
        let mut cols: Vec<Vec<Vec<F64>>> = par_map(self.pieces.len(), |n| {
            let p = &self.pieces[n];
            let h = 1usize << self.height(p);
            let (res_pos, arg_pos, _, _, _) = self.positions(n);
            let mut c: Vec<Vec<F64>> = vec![Vec::new(); p.shape.committed().len()];
            let col = |c: &mut Vec<Vec<F64>>, at: usize| -> usize {
                if c[at].is_empty() {
                    c[at] = vec![F64::ZERO; h];
                }
                at
            };
            self.rows_of(n, |x, j, r, clock| {
                if let Some(t) = r.writes() {
                    let v = limbs(t, run.rd(t, clock[t.ix()]));
                    for l in 0..t.limbs() {
                        let at = col(&mut c, res_pos[l]);
                        c[at][x] = F64(v[l]);
                    }
                }
                for (o, a) in r.args.iter().enumerate() {
                    let v = limbs(a.ty, run.rd(a.ty, a.at(j)));
                    for l in 0..a.ty.limbs() {
                        let at = col(&mut c, arg_pos[o][l]);
                        c[at][x] = F64(v[l]);
                    }
                }
            });
            for (at, counts) in &cs.cnt[n] {
                c[*at] = counts.iter().map(|&k| g(k)).collect();
            }
            for &(at, x, k) in &patch[n] {
                c[at][x] = g(k);
            }
            if let Some(at) = cs.dcnt[n] {
                let at = col(&mut c, at);
                for &(x, k) in &dby[n] {
                    c[at][x] = g(k);
                }
            }
            for v in c.iter_mut().filter(|v| v.is_empty()) {
                *v = vec![F64::ZERO; h];
            }
            c
        });
        let extra_cnt = extra
            .iter()
            .map(|&e| {
                let k = &mut reads[0][e];
                let c = self.g(*k as usize);
                *k += 1;
                c
            })
            .collect();
        for (n, col, t, cells) in &cs.fin_of {
            let r = &reads[t.ix()];
            let fin: Vec<F64> = cells.iter().map(|&e| self.g(r[e] as usize)).collect();
            cols[*n][*col][..fin.len()].copy_from_slice(&fin);
        }
        let in_fin = [0, 1].map(|k| (0..self.q.n_in[k]).map(|e| self.g(reads[k][e] as usize)).collect());
        Tables { cols, in_fin, reads, extra_cnt }
    }
}
