//! The bus and the table sumcheck over the recursion tables (WP-15b; BLUEPRINT §4.4–4.5): leanVM's
//! `leaf::prove_balance` (fingerprint challenges, the batched push/pull/count grand-product GKR, the
//! decomposition of every table-owned block into its table's bus forms) and `constraints::prove` (one
//! sumcheck over every table's degree-2 identities plus its three bus forms, on the GKR point), wired the
//! way leanVM's `cpu::prove` wires them (`bus_wiring`, `airs`), with no framework block (WP-9's
//! `LvmM3Phase`: the instance has no boundary block, so the decomposition reads nothing).
//!
//! A table is generic ([`TableW`]): its columns (committed first, then fixed: verifier-known, never opened),
//! its constraints (polynomials of degree ≤ 2 in the columns) and its flushes (tuples `⟨sep, addr, cnt,
//! limbs…⟩`, WP-9's coordinate order). [`piece_tables`] builds the LoopIR pieces' tables (WP-10
//! `Shape.constraints`, `Shape.flushes`, `Program.fval`, transcribed); [`InArr`] the input arrays (WP-9
//! `InArr`: one seed and one finalize per row, a fixed address column `g^(base + stride·x)`).
//!
//! Ordering (both sides must agree; WP-9 fixes it in Lean): tables in the order given; per table its
//! flushes in order, the push side taking the pushes and the pull side the pulls; the count side one block
//! per read (its count column); constraint `ξ`-powers table by table, then the three form powers.

use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::leanvm_core::constraints::{self, Air, Claims};
use crate::lv::leanvm_core::leaf::{self, Block, BusForm, Coord};
use crate::lv::primitives::field::{F64, powers};
use crate::lvm::loopir::{self, Compiled, FCol, Kind, Shape, Ty, Var};

/// A monomial: coefficient and at most two (table-local) columns.
pub type Mono = (F64, Vec<usize>);

/// One flush of a table (local column indices).
#[derive(Clone, Debug)]
pub struct FlushW {
    pub push: bool,
    pub coords: Vec<Coord>,
    /// A read's count column: the count side carries it (`CountsNonzero`).
    pub count: Option<usize>,
}

/// A table: `2^tau` rows, columns (`com[c]`: committed, else fixed: verifier-known), constraints, flushes.
/// `pre`: committed columns with a given place `(column, in C_rec, offset, write)`: `write = false` for a
/// column that already lives in a commitment (the stream columns `M_l` and `σ'` in `C_rec`, the `KS`
/// digests in `C_main`: checked, not written), `true` for one placed by the program's M3 spec; the others
/// are placed by [`place`].
pub struct TableW {
    pub tau: usize,
    pub cols: Vec<Vec<F64>>,
    pub com: Vec<bool>,
    pub cons: Vec<Vec<Mono>>,
    pub flushes: Vec<FlushW>,
    pub pre: Vec<(usize, bool, usize, bool)>,
    /// The header array `PUB` (A23): its value column (column 0) depends on the header, so it is not a column
    /// of the fixed-column polynomial `Φ` (`acc::fix_cols`).
    pub hdr: bool,
}

/// Whether the fixed columns' evaluations are sent (leanVM's way; the current V_S interface, whose
/// `tableTerms` evaluates the bus forms on the sent evaluations) or left to the verifier's closed forms
/// (`Air::sent` = committed only; needs a V_S hook for the fixed values, see WP-15b.md).
pub const SEND_FIXED: bool = true;

/// WP-9's `LvmM3Phase.lvmBusProg`: the bus phase ends with one prover scalar that must be zero (it stands
/// where leanVM reads the boundary values, so a prover move separates the GKR's last challenges from `ξ`):
/// `leafdecReads = 1`.
pub const BUS_TRAILING_ZERO: bool = true;

impl TableW {
    /// The evaluations the table sumcheck sends: every column (WP-9 `nativeTable`; INT-2's freeze).
    pub fn sent(&self) -> usize {
        assert!(SEND_FIXED);
        self.cols.len()
    }
    /// The committed columns, in column order (their claims, V_S `tableClaimsR`).
    pub fn committed(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.cols.len()).filter(|&c| self.com[c])
    }
    /// How many columns are committed.
    pub fn n_committed(&self) -> usize {
        self.com.iter().filter(|&&b| b).count()
    }
    /// Where committed column `c` is pre-placed, if it is.
    pub fn pre_of(&self, c: usize) -> Option<(bool, usize)> {
        self.pre.iter().find(|x| x.0 == c).map(|x| (x.1, x.2))
    }
    /// Whether pre-placed column `c` is written by the prover (else it is checked against the commitment).
    pub fn pre_writes(&self, c: usize) -> bool {
        self.pre.iter().any(|x| x.0 == c && x.3)
    }
}

impl TableW {
    /// Every constraint vanishes on every row (a prover self-check).
    pub fn constraints_hold(&self) -> bool {
        (0..1usize << self.tau).all(|x| {
            self.cons.iter().all(|c| {
                c.iter().fold(F64::ZERO, |acc, (k, vs)| acc + vs.iter().fold(*k, |p, &v| p * self.cols[v][x])).is_zero()
            })
        })
    }
}

/// An input array (WP-9 `InArr`): row `x` seeds cell `base + stride·x` of memory `ty` with its value limbs
/// and finalizes it with `fin` (`g^{reads}`).
pub struct InArr {
    pub ty: Ty,
    pub tau: usize,
    pub base: usize,
    pub stride: usize,
    pub vals: Vec<Vec<F64>>,
    pub fin: Vec<F64>,
    /// Per value limb: already committed at `(in C_rec, offset)` (e.g. a stream column), or new.
    pub pre: Vec<Option<(bool, usize)>>,
    /// A public array (`pubArr`, A19's PUB): its value column is fixed (the header's lanes), not committed.
    pub public: bool,
}

fn c(i: usize) -> Coord {
    Coord::Col(i)
}

impl InArr {
    /// Columns: the value limbs, `fin` (committed), the address `g^(base + stride·x)` (fixed).
    pub fn table(&self) -> TableW {
        let n = 1usize << self.tau;
        let lim = self.ty.limbs();
        assert_eq!(self.vals.len(), lim);
        let step = crate::lv::primitives::field::g_pow(self.stride);
        let mut addr: Vec<F64> = Vec::with_capacity(n);
        let mut a = crate::lv::primitives::field::g_pow(self.base);
        for _ in 0..n {
            addr.push(a);
            a = a * step;
        }
        let mut cols = self.vals.clone();
        cols.push(self.fin.clone());
        cols.push(addr);
        let sep = Coord::Const(loopir::sep(self.ty));
        let vals: Vec<Coord> = (0..lim).map(c).collect();
        let seed = [vec![sep.clone(), c(lim + 1), Coord::Const(F64::ONE)], vals.clone()].concat();
        let fin = [vec![sep, c(lim + 1), c(lim)], vals].concat();
        TableW {
            tau: self.tau,
            cols,
            com: [vec![!self.public; lim], vec![true, false]].concat(),
            cons: Vec::new(),
            flushes: vec![FlushW { push: true, coords: seed, count: None }, FlushW { push: false, coords: fin, count: None }],
            pre: self.pre.iter().enumerate().filter_map(|(l, x)| x.map(|(r, o)| (l, r, o, false))).collect(),
            hdr: false,
        }
    }
}

/// `red`: the limbs of `y^e` reduced by `y^3 = y + 1`.
fn red(e: usize) -> &'static [usize] {
    match e {
        0 => &[0],
        1 => &[1],
        2 => &[2],
        3 => &[0, 1],
        4 => &[1, 2],
        _ => &[],
    }
}

/// `prodTerms la lb l`.
fn prod_terms(la: usize, lb: usize, l: usize) -> Vec<(usize, usize)> {
    (0..la).flat_map(|i| (0..lb).filter(move |&j| red(i + j).contains(&l)).map(move |j| (i, j))).collect()
}

/// The variables of a shape's table: committed, then fixed (WP-9 `shapeVars`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V {
    C(Var),
    F(FCol),
}

/// `Shape.constraints`, as monomials over `V`.
fn shape_constraints(s: &Shape) -> Vec<Vec<(F64, Vec<V>)>> {
    let lim = |o: usize| s.args.get(o).copied().unwrap_or(Ty::K).limbs();
    let res = |l: usize| vec![(F64::ONE, vec![V::C(Var::Res(l))])];
    let prod = |l: usize| -> Vec<(F64, Vec<V>)> {
        prod_terms(lim(0), lim(1), l).into_iter().map(|(i, j)| (F64::ONE, vec![V::C(Var::Arg(0, i)), V::C(Var::Arg(1, j))])).collect()
    };
    let limb = |o: usize, l: usize| -> Vec<(F64, Vec<V>)> { if l < lim(o) { vec![(F64::ONE, vec![V::C(Var::Arg(o, l))])] } else { vec![] } };
    let limb_fix = |f: FCol, o: usize, l: usize| -> Vec<(F64, Vec<V>)> {
        if l < lim(o) { vec![(F64::ONE, vec![V::F(f), V::C(Var::Arg(o, l))])] } else { vec![] }
    };
    match s.kind {
        Kind::MulAdd => (0..s.ty.limbs()).map(|l| [res(l), prod(l), limb(2, l)].concat()).collect(),
        Kind::Lin => (0..s.ty.limbs())
            .map(|l| {
                let kk = if l == 0 { vec![(F64::ONE, vec![V::F(FCol::K2)])] } else { vec![] };
                [res(l), limb(0, l), limb_fix(FCol::K, 1, l), kk].concat()
            })
            .collect(),
        Kind::Assert0 => (0..if lim(0) == 1 && lim(1) == 1 { 1 } else { 3 }).map(prod).collect(),
        Kind::LoadE => (0..3).map(|l| [res(l), vec![(F64::ONE, vec![V::C(Var::Arg(l, 0))])]].concat()).collect(),
        Kind::FixMul => (0..s.ty.limbs()).map(|l| [res(l), limb_fix(FCol::F, 0, l), limb(1, l)].concat()).collect(),
        Kind::Readd => vec![],
    }
}

/// A group (WP-9 `Grp`): pieces of one shape stacked in one table of `2^tau` rows, member `(piece, row
/// offset)` (aligned, no padding row).
#[derive(Clone, Debug)]
pub struct Grp {
    pub tau: usize,
    pub mem: Vec<(usize, usize)>,
}

/// One group per piece (`Program.pieces` order): the tables when no grouping is given.
pub fn singleton_groups(c: &Compiled) -> Vec<Grp> {
    c.pieces.iter().enumerate().map(|(n, p)| Grp { tau: c.height(p) as usize, mem: vec![(n, 0)] }).collect()
}

/// WP-9's grouping (`LvmM3LoopTab.Grp`, as its doc describes it): per shape, in order of first use, the
/// pieces' total rows cut by its binary decomposition (largest first); the pieces, largest first (stable),
/// fill the groups in order, each at the next aligned offset. Exact because every height is a power of two.
pub fn default_groups(c: &Compiled) -> Vec<Grp> {
    let mut shapes: Vec<&Shape> = Vec::new();
    for p in &c.pieces {
        if !shapes.contains(&&p.shape) {
            shapes.push(&p.shape);
        }
    }
    let mut out = Vec::new();
    for s in shapes {
        let mut ms: Vec<(usize, u32)> = c.pieces.iter().enumerate().filter(|(_, p)| &p.shape == s).map(|(n, p)| (n, c.height(p))).collect();
        ms.sort_by(|a, b| b.1.cmp(&a.1));
        let total: usize = ms.iter().map(|m| 1usize << m.1).sum();
        let mut it = ms.into_iter().peekable();
        for a in (0..usize::BITS).rev().filter(|a| total >> a & 1 == 1) {
            let mut g = Grp { tau: a as usize, mem: Vec::new() };
            let mut off = 0usize;
            while off < 1 << a {
                let (n, h) = it.next().expect("the pieces fill the groups");
                g.mem.push((n, off));
                off += 1 << h;
            }
            assert_eq!(off, 1 << a);
            out.push(g);
        }
    }
    out
}

/// The LoopIR pieces as tables, one per piece (`piece_tables`) or per group (`group_tables`): columns
/// `Shape.committed` then `Shape.fcols` (`Program.fval`; WP-9 `shapeVars`), constraints `Shape.constraints`,
/// flushes `Shape.flushes`; a group's column holds each member's rows at its offset.
pub fn piece_tables(c: &Compiled, tb: &loopir::Tables) -> Vec<TableW> {
    group_tables(c, tb, &singleton_groups(c))
}

pub fn group_tables(c: &Compiled, tb: &loopir::Tables, groups: &[Grp]) -> Vec<TableW> {
    groups
        .iter()
        .map(|g| {
            let p0 = &c.pieces[g.mem[0].0];
            let s = &p0.shape;
            let com = s.committed();
            let fc = s.fcols();
            let h = 1usize << g.tau;
            let ix = |v: V| match v {
                V::C(u) => com.iter().position(|&w| w == u).unwrap(),
                V::F(f) => com.len() + fc.iter().position(|&g| g == f).unwrap(),
            };
            let mut cols = vec![vec![F64::ZERO; h]; com.len() + fc.len()];
            for &(n, off) in &g.mem {
                let p = &c.pieces[n];
                assert_eq!(&p.shape, s, "a group's members share a shape");
                let hp = 1usize << c.height(p);
                assert!(off % hp == 0 && off + hp <= h, "a member is aligned inside its group");
                for (k, col) in tb.cols[n].iter().enumerate() {
                    cols[k][off..off + hp].copy_from_slice(col);
                }
                for (k, &f) in fc.iter().enumerate() {
                    for x in 0..hp {
                        cols[com.len() + k][off + x] = c.fval(p, f, x);
                    }
                }
            }
            assert_eq!(g.mem.iter().map(|&(n, _)| 1usize << c.height(&c.pieces[n])).sum::<usize>(), h, "no padding row");
            let cons = shape_constraints(s)
                .into_iter()
                .map(|poly| poly.into_iter().map(|(k, vs)| (k, vs.into_iter().map(ix).collect())).collect())
                .collect();
            // Shape.flushes: reads (pulls), the same bumped (pushes), then a writer's seed and finalize
            let mut reads: Vec<(Ty, Coord, usize, Vec<Coord>)> = s
                .args
                .iter()
                .enumerate()
                .map(|(o, &t)| (t, c_of(ix(V::F(FCol::Arg(o)))), ix(V::C(Var::Cnt(o))), (0..t.limbs()).map(|l| c_of(ix(V::C(Var::Arg(o, l))))).collect()))
                .collect();
            if s.kind == Kind::Readd {
                reads.push((s.ty, c_of(ix(V::C(Var::Arg(0, 0)))), ix(V::C(Var::Dcnt)), (0..s.ty.limbs()).map(|l| c_of(ix(V::C(Var::Res(l))))).collect()));
            }
            let mut flushes = Vec::new();
            for (t, a, k, v) in &reads {
                flushes.push(FlushW { push: false, coords: [vec![Coord::Const(loopir::sep(*t)), a.clone(), c_of(*k)], v.clone()].concat(), count: Some(*k) });
            }
            for (t, a, k, v) in &reads {
                flushes.push(FlushW { push: true, coords: [vec![Coord::Const(loopir::sep(*t)), a.clone(), Coord::GCol(*k, 1)], v.clone()].concat(), count: None });
            }
            if s.writes() {
                let sep = Coord::Const(loopir::sep(s.ty));
                let addr = c_of(ix(V::F(FCol::Res)));
                let v: Vec<Coord> = (0..s.ty.limbs()).map(|l| c_of(ix(V::C(Var::Res(l))))).collect();
                flushes.push(FlushW { push: true, coords: [vec![sep.clone(), addr.clone(), Coord::Const(F64::ONE)], v.clone()].concat(), count: None });
                flushes.push(FlushW { push: false, coords: [vec![sep, addr, c_of(ix(V::C(Var::Fin)))], v].concat(), count: None });
            }
            TableW { tau: g.tau, cols, com: [vec![true; com.len()], vec![false; fc.len()]].concat(), cons, flushes, pre: Vec::new(), hdr: false }
        })
        .collect()
}

fn c_of(i: usize) -> Coord {
    Coord::Col(i)
}

fn shift(co: &Coord, base: usize) -> Coord {
    match co {
        Coord::Col(i) => Coord::Col(i + base),
        Coord::GCol(i, k) => Coord::GCol(i + base, *k),
        Coord::Prod(i, j, k) => Coord::Prod(i + base, j + base, *k),
        Coord::Sum(cs) => Coord::Sum(cs.iter().map(|x| shift(x, base)).collect()),
        x => x.clone(),
    }
}

/// What the bus and the table sumcheck leave to the openings: per table its point and its columns'
/// evaluations there (committed first; the fixed ones the verifier checks itself), and the GKR shape.
pub struct M3Out {
    pub claims: Vec<Claims>,
    pub bus_depth: usize,
    pub table_rounds: usize,
    pub table_evals: usize,
}

/// Prove the bus balance over every table's flushes, then the one table sumcheck (leanVM `cpu::prove`'s
/// "Prove bus", "Prove constraints").
pub fn prove(ps: &mut ProverState, tables: &[TableW]) -> M3Out {
    assert!(tables.iter().all(active), "only sumcheck tables (WP-9 M3R.real's filter)");
    let mut cols: Vec<&[F64]> = Vec::new();
    let mut spans = Vec::with_capacity(tables.len());
    let (mut push, mut pull, mut count) = (Vec::new(), Vec::new(), Vec::new());
    let mut owners: [Vec<Option<(usize, usize)>>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    for (t, tw) in tables.iter().enumerate() {
        let base = cols.len();
        for col in &tw.cols {
            assert_eq!(col.len(), 1 << tw.tau);
            cols.push(col);
        }
        spans.push((base, tw.cols.len()));
        for f in &tw.flushes {
            let blk = Block::full(tw.tau, f.coords.iter().map(|x| shift(x, base)).collect());
            if f.push {
                push.push(blk);
                owners[0].push(Some((t, base)));
            } else {
                pull.push(blk);
                owners[1].push(Some((t, base)));
            }
            if let Some(k) = f.count {
                count.push(Block::full(tw.tau, vec![Coord::Col(base + k)]));
                owners[2].push(Some((t, base)));
            }
        }
    }
    let bus_depth = leaf::layout(&push).mu;
    let bus = leaf::prove_balance(&push, &pull, &count, &cols, &owners, &spans, ps);
    if BUS_TRAILING_ZERO {
        ps.add_scalars(&[crate::lv::primitives::field::F192::ZERO]);
    }
    // the table sumcheck (leanVM `airs`)
    let xi = ps.sample();
    let n_cons: usize = tables.iter().map(|t| t.cons.len()).sum();
    let pows = powers(xi, n_cons + 3);
    let mut off = 0;
    let airs: Vec<Air> = tables
        .iter()
        .enumerate()
        .map(|(t, tw)| {
            let (start, n) = spans[t];
            let mut id = BusForm::new(n);
            for (i, poly) in tw.cons.iter().enumerate() {
                let w = pows[off + i];
                for (k, vs) in poly {
                    match vs.as_slice() {
                        [] => id.constant += w.mul_base(*k),
                        [a] => id.coeffs[*a] += w.mul_base(*k),
                        [a, b] => id.prods.push((*a, *b, w.mul_base(*k))),
                        _ => panic!("a constraint of degree > 2"),
                    }
                }
            }
            off += tw.cons.len();
            let forms = (0..3).map(|s| bus.forms[s][t].scaled(pows[n_cons + s]));
            Air {
                tau: tw.tau,
                cols: &cols[start..start + n],
                form: BusForm::sum(forms.chain([id])),
                sigma: (0..3).map(|s| pows[n_cons + s] * bus.sigmas[s][t]).sum(),
                sent: tw.sent(),
            }
        })
        .collect();
    let claims = constraints::prove(&airs, &bus.point, ps);
    M3Out {
        claims,
        bus_depth,
        table_rounds: tables.iter().map(|t| t.tau).max().unwrap_or(0),
        table_evals: tables.iter().map(|t| t.sent()).sum(),
    }
}

/// Where every table's committed columns sit in `C_main` (`None` for a fixed column): largest first at
/// aligned offsets from `lo` (rounded up to the largest column), the free region above WP-15a's tables
/// (provisional: WP-9/WP-14 fix the final layout). Panics if the region is too small.
pub fn place(tables: &[TableW], lo: usize, nu_main: usize) -> Vec<Vec<Option<usize>>> {
    let mut cols: Vec<(usize, usize, usize)> = Vec::new(); // (tau, table, column)
    for (t, tw) in tables.iter().enumerate() {
        for c in tw.committed().filter(|&c| tw.pre_of(c).is_none()) {
            cols.push((tw.tau, t, c));
        }
    }
    cols.sort_by(|a, b| b.0.cmp(&a.0).then((a.1, a.2).cmp(&(b.1, b.2))));
    let top = cols.first().map_or(0, |x| x.0);
    let mut off = lo.div_ceil(1 << top) << top;
    let mut out: Vec<Vec<Option<usize>>> = tables.iter().map(|t| vec![None; t.cols.len()]).collect();
    for (tau, t, c) in cols {
        out[t][c] = Some(off);
        off += 1 << tau;
    }
    assert!(off <= 1 << nu_main, "the recursion tables fit C_main ({off} > 2^{nu_main})");
    out
}

/// Committed words the tables add (A12's budget): aliased columns (stream, `σ'`, digests) excluded.
pub fn committed_words(tables: &[TableW]) -> usize {
    tables.iter().map(|t| (t.n_committed() - t.pre.iter().filter(|x| !x.3).count()) << t.tau).sum()
}

/// WP-9 `M3R.real`'s sumcheck tables: those with a constraint, a read or a seed (every flush here is one).
pub fn active(t: &TableW) -> bool {
    !t.cons.is_empty() || !t.flushes.is_empty()
}

/// The schedule numbers these tables make (`Params.busDepth/leafdecReads/tableRounds/tableEvals`).
pub fn shape(tables: &[TableW]) -> (usize, usize, usize, usize) {
    let tables: Vec<&TableW> = tables.iter().filter(|t| active(t)).collect();
    let push: Vec<Block> = tables
        .iter()
        .flat_map(|t| t.flushes.iter().filter(|f| f.push).map(move |_| Block::full(t.tau, vec![])))
        .collect();
    (leaf::layout(&push).mu, BUS_TRAILING_ZERO as usize, tables.iter().map(|t| t.tau).max().unwrap_or(0), tables.iter().map(|t| t.sent()).sum())
}

/// The tables of a LoopIR run: its pieces, then its inputs as input arrays split by the binary
/// decomposition of their counts (`K` then `E`, base 0, stride 1; provisional: the real `Q`'s input arrays
/// are the stream columns, the digests and the bit fields, WP-9's `InArr`s).
pub fn loop_tables(c: &Compiled, tb: &loopir::Tables, in_k: &[F64], in_e: &[crate::lv::primitives::field::F192]) -> Vec<TableW> {
    let mut tabs = group_tables(c, tb, &default_groups(c));
    for t in [Ty::K, Ty::E] {
        let k = if t == Ty::K { 0 } else { 1 };
        let n = c.q.n_in[k];
        let mut base = 0;
        for a in (0..usize::BITS).rev().filter(|a| n >> a & 1 == 1) {
            let rows = 1usize << a;
            let vals = (0..t.limbs())
                .map(|l| (0..rows).map(|x| F64(match t { Ty::K => in_k[base + x].0, Ty::E => in_e[base + x].to_limbs()[l] })).collect())
                .collect();
            let fin = tb.in_fin[k][base..base + rows].to_vec();
            tabs.push(InArr { ty: t, tau: a as usize, base, stride: 1, vals, fin, pre: vec![None; t.limbs()], public: false }.table());
            base += rows;
        }
    }
    tabs
}

/// The stream as input arrays (BLUEPRINT §4.2 memory view; WP-9 `InArr`): array `l < 17` seeds the cells
/// `17i + l` (`i < 2^rec`) with `C_rec`'s column `M_l`, pre-placed there; `fin` from the run's reads.
pub fn stream_arrays(rec_log: usize, msg: &[[u64; crate::lvm::params::REC_STREAM_COLS]], in_fin: &[F64]) -> Vec<TableW> {
    let n = 1usize << rec_log;
    (0..crate::lvm::params::REC_STREAM_COLS)
        .map(|l| {
            InArr {
                ty: Ty::K,
                tau: rec_log,
                base: l,
                stride: crate::lvm::params::REC_STREAM_COLS,
                vals: vec![(0..n).map(|i| F64(msg[i][l])).collect()],
                fin: (0..n).map(|i| in_fin[crate::lvm::params::REC_STREAM_COLS * i + l]).collect(),
                pre: vec![Some((true, l << rec_log))],
                public: false,
            }
            .table()
        })
        .collect()
}

/// A LoopIR program whose `K` inputs are the stream lanes (`nInK = 17·2^rec`, no `E` input), run on the
/// stream of `rec`: its pieces and the 17 stream arrays.
pub fn stream_program_tables(c: &Compiled, rec_log: usize, msg: &[[u64; crate::lvm::params::REC_STREAM_COLS]]) -> Vec<TableW> {
    let w = crate::lvm::params::REC_STREAM_COLS;
    assert_eq!(c.q.n_in, [w << rec_log, 0], "the program's inputs are the stream lanes");
    let in_k: Vec<F64> = (0..w << rec_log).map(|e| F64(msg[e / w][e % w])).collect();
    let run = c.interp(&in_k, &[]);
    let tb = c.tables(&run);
    let mut t = group_tables(c, &tb, &default_groups(c));
    t.extend(stream_arrays(rec_log, msg, &tb.in_fin[0]));
    t
}

/// The WOTS checksum `Σ (3 − dᵢ)` of a digest's four lanes (4 base-4 digits per byte, low bits first): Q_sig's
/// free `cs` word (WP-16a, the blob's `FREE … 0 …`).
pub fn free_checksum(d: &[F64]) -> u64 {
    d.iter().flat_map(|v| v.0.to_le_bytes()).map(|byte| (0..4).map(|t| 3 - ((byte >> (2 * t)) & 3) as u64).sum::<u64>()).sum()
}

/// How many lanes [`pub_lanes`] gives at `p`: the header's lanes from byte 8 and the statement's four.
pub fn pub_lanes_len(p: &crate::lvm::params::Params) -> usize {
    (crate::lvm::params::header_bytes(p) - 8) / 8 + 4
}

/// The public lanes a public array's selectors index (provisional order, WP-15c; the final assembly fixes
/// the Lean `arrsOf`): `b, vk (4), c (4), c_L (4), s (4), n, h (4), σ_leaf (597), acc_in (3(D + 1))` = the
/// header's lanes from byte 8 with the statement `c` (V's argument) after `vk`.
pub fn pub_lanes(header: &[u8], c: &[u8; 32]) -> Vec<u64> {
    let lane = |b: &[u8], o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
    let hl: Vec<u64> = (8..header.len()).step_by(8).map(|o| lane(header, o)).collect();
    let mut v = hl[..5].to_vec();
    v.extend((0..4).map(|i| lane(c, 8 * i)));
    v.extend_from_slice(&hl[5..]);
    assert_eq!(v.len(), (header.len() - 8) / 8 + 4);
    v
}

/// The tables of a blob's M3 section (WP-9 `lvmTabs Q pl groups arrs aux`): groups with Lean's placements
/// (pre-placed, written), input arrays (aliased: values read from the commitments' contents, `col(rec, off,
/// len)`; written: the cells' values, placed; public: fixed value columns from `pub_lanes`), then the BITS
/// tables (aux). The run must already hold the BITS outputs in its input cells (`Ctx::build_tables`'s
/// fixpoint); `extra` reads = every BITS table's [`crate::lvm::bits::BitsSpec::reads`] in order.
pub fn spec_tables(
    c: &Compiled,
    run: &loopir::Run,
    spec: &loopir::M3Spec,
    col: &dyn Fn(bool, usize, usize) -> Vec<F64>,
    pub_lanes: &[u64],
    hdr_lanes: usize,
) -> Vec<TableW> {
    use crate::lvm::loopir::ArrKind;
    let extra: Vec<usize> = spec.bits.iter().flat_map(|b| b.reads()).collect();
    let tb = c.tables_ext(run, &extra);
    let groups: Vec<Grp> = spec.groups.iter().map(|(tau, mem, _)| Grp { tau: *tau, mem: mem.clone() }).collect();
    let mut tabs = group_tables(c, &tb, &groups);
    for (t, (_, _, com)) in tabs.iter_mut().zip(&spec.groups) {
        assert_eq!(com.len(), t.n_committed(), "a placement per committed column");
        t.pre = com.iter().enumerate().map(|(k, &(r, o))| (k, r, o, true)).collect();
    }
    for a in &spec.arrs {
        let k = if a.ty == Ty::K { 0 } else { 1 };
        let n = 1usize << a.tau;
        let cells: Vec<usize> = (0..n).map(|x| a.base + a.stride * x).collect();
        let fins = cells.iter().map(|&e| tb.in_fin[k][e]).collect();
        let vals: Vec<Vec<F64>> = match a.kind {
            ArrKind::Aliased => a.val.iter().map(|&(r, o)| col(r, o, n)).collect(),
            ArrKind::Written => (0..a.ty.limbs())
                .map(|l| cells.iter().map(|&e| F64(if k == 0 { run.kc[e].0 } else { run.ec[e].to_limbs()[l] })).collect())
                .collect(),
            ArrKind::Public => {
                assert_eq!(a.ty, Ty::K, "public arrays are K arrays");
                vec![(0..n).map(|x| F64(a.sel.get(x).and_then(|&i| pub_lanes.get(i).copied()).unwrap_or(0))).collect()]
            }
        };
        let mut t = InArr {
            ty: a.ty,
            tau: a.tau,
            base: a.base,
            stride: a.stride,
            vals,
            fin: fins,
            pre: vec![None; a.ty.limbs()],
            public: a.kind == ArrKind::Public,
        }
        .table();
        match a.kind {
            ArrKind::Aliased => t.pre = a.val.iter().enumerate().map(|(l, &(r, o))| (l, r, o, false)).collect(),
            ArrKind::Written => t.pre = a.val.iter().enumerate().map(|(l, &(r, o))| (l, r, o, true)).collect(),
            // the header array: a public array that selects header lanes only (QLT selects `PUBX` lanes)
            ArrKind::Public => t.hdr = a.sel.iter().all(|&i| i < hdr_lanes),
        }
        t.pre.push((a.ty.limbs(), a.fin.0, a.fin.1, true));
        tabs.push(t);
    }
    let mut off = 0;
    for (bi, b) in spec.bits.iter().enumerate() {
        let nr = b.reads().len();
        let words: Vec<u64> = match spec.free.iter().find(|f| f.0 == bi) {
            Some(&(_, 0, cell)) => vec![free_checksum(&run.kc[cell..cell + 4]); b.n],
            Some(&(_, k, _)) => panic!("LoopIR blob: free word kind {k}"),
            None => b.wc.iter().map(|&e| run.kc[e].0).collect(),
        };
        tabs.push(b.table(&words, &tb.extra_cnt[off..off + nr], &|e| c.g(e)));
        off += nr;
    }
    tabs
}
