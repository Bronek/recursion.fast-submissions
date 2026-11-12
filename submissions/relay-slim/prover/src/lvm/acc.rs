//! The fixed-column accumulator (BLUEPRINT §12, A23; Lean `accOutOf`, `PhiC`, `decideProg` phase 3b).
//!
//! `Φ(x, k) = F_k(x mod 2^{τ_k})` over `D = τ* + dk` variables, `F_k` the `k`-th fixed column of the sumcheck
//! tables (table order, then column order) except the header array `PUB`'s value column; its extension is
//! `Φ̃(p, κ) = Σ_k eq(κ, k)·F̃_k(p[..τ_k])` (low bit first). An accumulator `(pt, y)` claims `Φ̃(pt) = y`.
//!
//! Phase 3b (after the table sumcheck's evaluations): `κ` (dk samples); `h` (D + 1 coefficients of
//! `Φ̃ ∘ line`, `line(t) = a + t·(a + b)`, `a` = the header's `acc_in.pt`, `b = r ++ κ`); `t`; one zero scalar.
//! `V` checks `h(0) = acc_in.y`, `h(1) = Σ_k eq(κ, k)·v_fix[k]` and natively `Φ̃(line(t)) = h(t)`.

use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::primitives::field::{F64, F192, Weights8, dot_base};
use crate::lv::primitives::multilinear::{eq_table, poly_eval};
use crate::lvm::m3::TableW;
use crate::lvm::params::{self, E_BYTES, Item, Params, Phase};

/// An evaluation claim on `Φ̃`: `pt ∈ E^D`, `y ∈ E`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Acc {
    pub pt: Vec<F192>,
    pub y: F192,
}

fn scalar(b: &[u8]) -> F192 {
    let l = |i: usize| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
    F192::new(l(0), l(1), l(2))
}

fn put(v: &mut Vec<u8>, x: F192) {
    for l in x.to_limbs() {
        v.extend_from_slice(&l.to_le_bytes());
    }
}

impl Acc {
    /// `pt` then `y`, 24 B per `E` scalar (the header's `acc_in`).
    pub fn bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(E_BYTES * (self.pt.len() + 1));
        for &x in &self.pt {
            put(&mut v, x);
        }
        put(&mut v, self.y);
        v
    }
    pub fn parse(b: &[u8], d: usize) -> Acc {
        assert_eq!(b.len(), E_BYTES * (d + 1), "acc_in is D + 1 scalars");
        Acc { pt: (0..d).map(|i| scalar(&b[E_BYTES * i..])).collect(), y: scalar(&b[E_BYTES * d..]) }
    }
    /// `(0, Φ̃(0))`: step 1's `S,0` (BLUEPRINT §12.7).
    pub fn zero(d: usize, phi0: F192) -> Acc {
        Acc { pt: vec![F192::ZERO; d], y: phi0 }
    }
}

/// `⌈log₂ n⌉` (0 for n ≤ 1).
pub fn log2_ceil(n: usize) -> usize {
    if n <= 1 { 0 } else { (usize::BITS - (n - 1).leading_zeros()) as usize }
}

/// Whether column `c` of sumcheck table `j` is a column of `Φ` (Lean `fixColsR`): fixed, and not column 0
/// of table `pub_tab` (`PUB`'s value column).
fn in_phi(t: &TableW, j: usize, c: usize, pub_tab: usize) -> bool {
    !t.com[c] && !(j == pub_tab && c == 0)
}

/// The columns of `Φ` (`fixCols`), in table order then column order.
pub fn fix_cols(tables: &[TableW], pub_tab: usize) -> Vec<&[F64]> {
    tables
        .iter()
        .enumerate()
        .flat_map(|(j, t)| (0..t.cols.len()).filter(move |&c| in_phi(t, j, c, pub_tab)).map(move |c| &t.cols[c][..]))
        .collect()
}

/// Where `Φ`'s columns sit in the table phase's evaluations item (every column of every table, in order).
pub fn fix_index(tables: &[TableW], pub_tab: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut i = 0;
    for (j, t) in tables.iter().enumerate() {
        for c in 0..t.cols.len() {
            if in_phi(t, j, c, pub_tab) {
                out.push(i);
            }
            i += 1;
        }
    }
    out
}

/// The sumcheck table holding the header array `PUB` (a prover-side cross-check of `Params.pub_tab`).
pub fn hdr_tab(tables: &[TableW]) -> Option<usize> {
    tables.iter().position(|t| t.hdr)
}

/// The low variables of a column's evaluation folded by one packed dot product per `2^LOW` cells.
const LOW: usize = 10;

/// Per-point tables shared by every column: `eq(p[..τ])` for `τ < LOW`, the packed `eq(p[..LOW])`, and
/// `eq(p[LOW..τ])` for `LOW ≤ τ ≤ τ*`.
struct PointTabs {
    small: Vec<Vec<F192>>,
    low: Vec<Weights8>,
    high: Vec<Vec<F192>>,
}

impl PointTabs {
    fn new(p: &[F192]) -> Self {
        let small = (0..=p.len().min(LOW - 1)).map(|t| eq_table(&p[..t])).collect::<Vec<_>>();
        let low = if p.len() >= LOW { crate::lv::primitives::multilinear::packed_eq(&p[..LOW]) } else { Vec::new() };
        let high = if p.len() >= LOW { (LOW..=p.len()).map(|t| eq_table(&p[LOW..t])).collect() } else { Vec::new() };
        PointTabs { small, low, high }
    }
    /// `F̃(p[..τ])`, `τ = log₂ |col|`.
    fn eval(&self, col: &[F64]) -> F192 {
        let tau = col.len().trailing_zeros() as usize;
        if tau < LOW {
            let w = &self.small[tau];
            return col.iter().zip(w).map(|(&k, &e)| e.mul_base(k)).sum();
        }
        let hi = &self.high[tau - LOW];
        col.chunks_exact(1 << LOW).zip(hi).map(|(row, &e)| e * dot_base(&self.low, row).reduce()).sum()
    }
}

/// `Φ̃` at each of `pts` (`pt = p ++ κ`, `|p| = τ*`): one pass over every column per point, the columns in
/// parallel.
pub fn phi_at(cols: &[&[F64]], tau_star: usize, pts: &[Vec<F192>]) -> Vec<F192> {
    if cols.is_empty() {
        return vec![F192::ZERO; pts.len()];
    }
    assert!(cols.iter().all(|c| c.len().is_power_of_two() && c.len() <= 1 << tau_star), "every fixed column is at most 2^τ* high");
    let dk = log2_ceil(cols.len());
    let tabs: Vec<PointTabs> = pts.iter().map(|pt| PointTabs::new(&pt[..tau_star])).collect();
    let eqk: Vec<Vec<F192>> = pts
        .iter()
        .map(|pt| {
            assert!(pt.len() >= tau_star + dk, "the point covers the column index");
            let mut e = eq_table(&pt[tau_star..tau_star + dk]);
            // the column index's further variables are 0 on every column (nFix ≤ 2^dk)
            let rest: F192 = pt[tau_star + dk..].iter().map(|&x| F192::ONE + x).product();
            e.iter_mut().for_each(|w| *w *= rest);
            e
        })
        .collect();
    // per column, its value at every point; columns are the tasks (largest work first does not matter here)
    let per_col: Vec<Vec<F192>> = crate::lv::parallel::map_collect(cols.len(), |k| tabs.iter().map(|t| t.eval(cols[k])).collect());
    (0..pts.len()).map(|i| per_col.iter().zip(&eqk[i]).map(|(v, &w)| w * v[i]).sum()).collect()
}

/// The coefficients (constant first) of the polynomial of degree `< xs.len()` through `(xs[i], ys[i])`.
pub fn interpolate(xs: &[F192], ys: &[F192]) -> Vec<F192> {
    let n = xs.len();
    assert_eq!(ys.len(), n);
    // Newton divided differences (characteristic 2: subtraction is addition)
    let mut dd = ys.to_vec();
    for j in 1..n {
        for i in (j..n).rev() {
            dd[i] = (dd[i] + dd[i - 1]) * (xs[i] + xs[i - j]).inv();
        }
    }
    // Horner on the Newton form: c = dd[n-1]; c = c·(X − x_i) + dd[i]
    let mut c = vec![F192::ZERO; n];
    c[0] = dd[n - 1];
    let mut deg = 0;
    for i in (0..n - 1).rev() {
        // c ← c·(X + x_i)
        let mut nc = vec![F192::ZERO; n];
        for d in 0..=deg {
            nc[d + 1] += c[d];
            nc[d] += c[d] * xs[i];
        }
        deg += 1;
        nc[0] += dd[i];
        c = nc;
    }
    c
}

/// `line(t) = a + t·(a + b)` coordinatewise.
pub fn line(a: &[F192], b: &[F192], t: F192) -> Vec<F192> {
    a.iter().zip(b).map(|(&x, &y)| x + t * (x + y)).collect()
}

/// What phase 3b leaves: the outgoing accumulator and the line evaluation's time.
pub struct Fold {
    pub out: Acc,
    pub secs: f64,
}

/// Phase 3b, prover side: `κ`, `h`, `t`, the zero scalar. `r` = the table point (by variable), `v_fix` the sent
/// evaluations of `Φ`'s columns, `cols` those columns.
pub fn prove(ps: &mut ProverState, p: &Params, acc_in: &Acc, r: &[F192], v_fix: &[F192], cols: &[&[F64]]) -> Fold {
    let d = p.acc_d();
    assert_eq!(r.len(), p.table_rounds, "the table point has τ* coordinates");
    assert_eq!(acc_in.pt.len(), d);
    assert!(cols.len() <= 1 << p.acc_log(), "nFix ≤ 2^dk ({} > 2^{})", cols.len(), p.acc_log());
    let kappa = ps.sample_vec(p.acc_log());
    let eqk = eq_table(&kappa);
    let y_own: F192 = v_fix.iter().zip(&eqk).map(|(&v, &w)| w * v).sum();
    let b: Vec<F192> = [r, &kappa[..]].concat();
    let xs: Vec<F192> = (0..=d as u64).map(|j| F192::new(j, 0, 0)).collect();
    let t0 = std::time::Instant::now();
    let pts: Vec<Vec<F192>> = xs[2..].iter().map(|&x| line(&acc_in.pt, &b, x)).collect();
    let mut ys = vec![acc_in.y, y_own];
    ys.extend(phi_at(cols, p.table_rounds, &pts));
    let secs = t0.elapsed().as_secs_f64();
    let h = interpolate(&xs, &ys);
    debug_assert_eq!(poly_eval(&h, F192::ONE), y_own);
    assert_eq!(h[0], acc_in.y, "h(0) = acc_in.y");
    ps.add_scalars(&h);
    let t = ps.sample();
    ps.add_scalars(&[F192::ZERO]);
    let out = Acc { pt: line(&acc_in.pt, &b, t), y: poly_eval(&h, t) };
    if std::env::var_os("LVM_ACC_CHECK").is_some() {
        let y = phi_at(cols, p.table_rounds, std::slice::from_ref(&out.pt))[0];
        assert_eq!(y, out.y, "Φ̃(accOut.pt) = accOut.y (the incoming claim and the fixed evaluations are true)");
    }
    Fold { out, secs }
}

/// `accOutOf`: the outgoing accumulator of a proof `(π, tr)` at `p`, from its stream alone (BLUEPRINT §12.4
/// steps 2–4; the child's `acc_in` is in its header, `r`, `κ`, `t` are its trace's answers, `h` its body).
pub fn acc_out_of(p: &Params, pi: &[u8], tr: &[(Vec<u8>, [u8; 32])]) -> Acc {
    let d = p.acc_d();
    let hb = params::header_bytes(p);
    assert!(pi.len() >= hb, "the proof holds a header");
    let acc_in = Acc::parse(&pi[params::HEADER_BASE..hb], d);
    let (mut body, mut q) = (hb, 2usize);
    let ans = |q: usize| scalar(&tr[q].1);
    let mut table_samples: Vec<F192> = Vec::new();
    let mut acc_samples: Vec<F192> = Vec::new();
    let mut h: Vec<F192> = Vec::new();
    for (ph, items) in params::phases(p) {
        for it in items {
            match it {
                Item::Read(m) => {
                    if ph == Phase::Acc && m == d + 1 {
                        h = (0..m).map(|i| scalar(&pi[body + E_BYTES * i..])).collect();
                    }
                    body += E_BYTES * m;
                }
                Item::Cap(c, _, _) => body += crate::lvm::params::NODE_BYTES << c,
                Item::Sample => {
                    match ph {
                        Phase::Tables => table_samples.push(ans(q)),
                        Phase::Acc => acc_samples.push(ans(q)),
                        _ => {}
                    }
                    q += 1;
                }
                Item::Positions(com, lv) => q += p.levels(com)[lv].t.div_ceil(params::POSITIONS_PER_ANSWER),
                Item::Opening(com, lv) => {
                    let l = p.levels(com)[lv];
                    q += l.t * (1 + l.path);
                    body += l.t * (l.row + l.path * crate::lvm::params::NODE_BYTES);
                }
            }
        }
        if ph == Phase::Acc {
            break;
        }
    }
    // table phase: ξ, then one challenge per round, round j binding variable τ* − 1 − j
    let n = p.table_rounds;
    assert_eq!(table_samples.len(), 1 + n);
    let r: Vec<F192> = (0..n).map(|m| table_samples[n - m]).collect();
    let dk = p.acc_log();
    assert_eq!(acc_samples.len(), dk + 1);
    let (kappa, t) = (&acc_samples[..dk], acc_samples[dk]);
    let b: Vec<F192> = [&r[..], kappa].concat();
    Acc { pt: line(&acc_in.pt, &b, t), y: poly_eval(&h, t) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn interpolation() {
        let xs: Vec<F192> = (0..6u64).map(|j| F192::new(j, 0, 0)).collect();
        let c: Vec<F192> = (0..6u64).map(|j| F192::new(3 * j + 1, j, 7)).collect();
        let ys: Vec<F192> = xs.iter().map(|&x| poly_eval(&c, x)).collect();
        assert_eq!(interpolate(&xs, &ys), c);
    }
}
