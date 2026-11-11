//! S2's chain wiring (BLUEPRINT2 §1.2 T3–T4; docs/lvm2/stages/T-P1.md, Conventions C.5–C.6).
//!
//! The tape's GKR ends with a claim on the virtual input state, `C_in = Σ_i ι(i)·⟨ω, in(i)⟩` with
//! `ι(i) = eq(ρ, i ≫ 4)·μ[i & 15]`. On the chain, `in(0) = Pad43(s)`, `in(i) = Pad43(D[i − 1])` for `1 ≤ i ≤ m`
//! (`m = n − 1`) and `in(i) = 0` beyond, so `C_in = const + Σ_x K_ch(x)·G_D(x)` with
//! `const = ι(0)·⟨ω, Pad43(s)⟩ + ⟨ω, c43⟩·Σ_{i=1}^{m} ι(i)`, `K_ch(x) = ι(x + 1)·[x + 1 ≤ m]` and
//! `G_D(x) = Σ_{p<256} ω(8 + p)·bit_p(D[x])`. One degree-2 sumcheck over `x` (low bit first) ends at `σ`; the prover
//! sends `g_D = G̃_D(σ)`, and a 2-round slot sumcheck over the lane `l` reduces it to the 64 bit slices of the `D`
//! block at `(σ, τ)`, a ring-switched claim on `C_main`.
//!
//! The prover works on the live prefix (`x < n`): `K_ch` vanishes past it and `G_D` is the constant `G_D(z*)` (dead
//! rows hold `z*[0..4)`), a tail that folds to itself. The verifier's closed forms (`k_ch_mle`, `iota_prefix_sum`,
//! `lt_mle`) are asserted against the prover's tables on every proof.

use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::keccak_gkr::Claim as GkrClaim;
use crate::lv::pcs::ring_switch::fold_1b_rows;
use crate::lv::primitives::field::{F64, F192};
use crate::lv::primitives::multilinear::{eq_eval, eq_table};
use crate::lvm::link::{Claim, bitdot, byte_tables, eq_prefix, lt_mle};
use crate::lvm::params::{LANES, PAD_SHIFT, RING_STAGES};
use crate::lvm::tables::{Chain, Layout};
use crate::oracle::Digest;

/// `⟨ω, v⟩ = Σ_j ω(j)·bit_j(v)`, `j = 64·lane + z`.
pub fn omega_dot(omega: &[F192], v: &[u64; LANES]) -> F192 {
    let mut acc = F192::ZERO;
    for (l, &w) in v.iter().enumerate() {
        let mut bits = w;
        while bits != 0 {
            acc += omega[64 * l + bits.trailing_zeros() as usize];
            bits &= bits - 1;
        }
    }
    acc
}

/// `ι(i) = eq(ρ, i ≫ 4)·μ[i & 15]` for `i < len`.
pub fn iota_table(rho: &[F192], mu: &[F192; 16], len: usize) -> Vec<F192> {
    let packs = eq_prefix(rho, len.div_ceil(16).min(1 << rho.len()));
    (0..len).map(|i| packs[i >> 4] * mu[i & 15]).collect()
}

/// `Σ_{i<t} ι(i)` in closed form (`t ≤ 2^(|ρ| + 4)`): whole packs by `lt̃`, the partial pack by its `μ` prefix.
pub fn iota_prefix_sum(rho: &[F192], mu: &[F192; 16], t: usize) -> F192 {
    let (q, r) = (t >> 4, t & 15);
    let total: F192 = mu.iter().copied().sum();
    let mut s = lt_mle(rho, q) * total;
    if r > 0 {
        let bits: Vec<F192> = (0..rho.len()).map(|k| if (q >> k) & 1 == 1 { F192::ONE } else { F192::ZERO }).collect();
        s += eq_eval(rho, &bits) * mu[..r].iter().copied().sum::<F192>();
    }
    s
}

/// `K̃_ch(σ) = Σ_{x < 2^w} eq(σ, x)·ι(x + 1)·[x + 1 ≤ m]` (BLUEPRINT2's `MS_w^0(σ; m)`): the low four bits as one
/// digit of 16 values (`μ` is not a tensor), then a carry × comparison automaton over bits `4 … w − 1`, low first;
/// accept: no carry out, `x + 1 ≤ m`.
pub fn k_ch_mle(sigma: &[F192], rho: &[F192], mu: &[F192; 16], m: usize) -> F192 {
    let w = sigma.len();
    assert_eq!(rho.len() + 4, w);
    // st[carry][cmp], cmp: 0 lt, 1 eq, 2 gt (of y = x + 1 against m, on the bits so far)
    let mut st = [[F192::ZERO; 3]; 2];
    let e4 = eq_table(&sigma[..4]);
    let m4 = m & 15;
    for d in 0..16usize {
        let y = (d + 1) & 15;
        let c = usize::from(d == 15);
        let cmp = if y < m4 { 0 } else if y == m4 { 1 } else { 2 };
        st[c][cmp] += e4[d] * mu[y];
    }
    for k in 4..w {
        let mk = (m >> k) & 1;
        let mut nx = [[F192::ZERO; 3]; 2];
        for c in 0..2 {
            for cmp in 0..3 {
                let v = st[c][cmp];
                if v == F192::ZERO {
                    continue;
                }
                for xb in 0..2usize {
                    let yb = xb ^ c;
                    let wx = if xb == 1 { sigma[k] } else { F192::ONE + sigma[k] };
                    let wy = if yb == 1 { rho[k - 4] } else { F192::ONE + rho[k - 4] };
                    let ncmp = if yb < mk { 0 } else if yb > mk { 2 } else { cmp };
                    nx[xb & c][ncmp] += v * wx * wy;
                }
            }
        }
        st = nx;
    }
    st[0][0] + st[0][1]
}

/// The verifier's constant of the wiring identity: `ι(0)·⟨ω, Pad43(s)⟩ + ⟨ω, c43⟩·Σ_{i=1}^{m} ι(i)`.
pub fn wire_const(fin: &GkrClaim, s: &Digest, n: usize) -> F192 {
    let iota0 = eq_eval(&fin.point, &vec![F192::ZERO; fin.point.len()]) * fin.mu[0];
    let c43 = crate::keccak::chain_block(&[0u8; 32]);
    let pad_s = crate::keccak::chain_block(s);
    iota0 * omega_dot(&fin.weights, &pad_s) + omega_dot(&fin.weights, &c43) * (iota_prefix_sum(&fin.point, &fin.mu, n) + iota0)
}

/// One round of `Σ a·b` (degree 2), variable 0 first: `(q(0), q₂)`.
fn round_ab(a: &[F192], b: &[F192]) -> (F192, F192) {
    let half = a.len() / 2;
    crate::lv::parallel::fold_reduce(
        half,
        || (F192::ZERO, F192::ZERO),
        |acc, j| {
            let (a0, a1, b0, b1) = (a[2 * j], a[2 * j + 1], b[2 * j], b[2 * j + 1]);
            acc.0 += a0 * b0;
            acc.1 += (a0 + a1) * (b0 + b1);
        },
        |x, y| (x.0 + y.0, x.1 + y.1),
    )
}

fn fold(v: &[F192], r: F192) -> Vec<F192> {
    crate::lv::parallel::map_collect(v.len() / 2, |j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1]))
}

/// The sumcheck of `Σ_{x<2^vars} a(x)·b(x)` from `claim`, with `a` zero and `b` the constant `b_tail` past the stored
/// prefixes (equal lengths). Sends `(c₀, c₂)` per round. Returns `σ`, the final claim, `ã(σ)` and `b̃(σ)` (exact: a
/// constant tail folds to itself).
pub fn sumcheck_ab_live(
    ps: &mut ProverState,
    mut a: Vec<F192>,
    mut b: Vec<F192>,
    b_tail: F192,
    mut claim: F192,
    vars: usize,
) -> (Vec<F192>, F192, F192, F192) {
    assert_eq!(a.len(), b.len());
    let mut point = Vec::with_capacity(vars);
    for _ in 0..vars {
        let m = a.len().max(1);
        let m2 = m + (m & 1);
        a.resize(m2, F192::ZERO);
        b.resize(m2, b_tail);
        let (c0, c2) = round_ab(&a, &b);
        let c1 = claim + c2;
        ps.add_round_poly(&[c0, c1, c2], false);
        let r = ps.sample();
        claim = c0 + r * (c1 + r * c2);
        a = fold(&a, r);
        b = fold(&b, r);
        point.push(r);
    }
    (point, claim, a[0], b[0])
}

/// T3 and T4 (the `Wire` phase). `fin` is the tape GKR's input claim; returns the `D` ring claim on `C_main`.
#[allow(clippy::too_many_arguments)]
pub fn prove_wire(ps: &mut ProverState, lay: &Layout, ch: &Chain, cmain: &[F64], fin: &GkrClaim, s: &Digest, n: usize, dense: bool) -> Claim {
    let ln = lay.log_n;
    let big = 1usize << ln;
    assert!(n >= 1 && n <= big);
    let m = n - 1;
    let (rho, mu, omega) = (&fin.point[..], &fin.mu, &fin.weights[..]);
    assert_eq!(rho.len() + 4, ln);
    let live = if dense { big } else { n };

    // ---- T3: the wiring sumcheck
    let iota = iota_table(rho, mu, (live + 1).min(big));
    let k: Vec<F192> = (0..live).map(|x| if x + 1 <= m { iota[x + 1] } else { F192::ZERO }).collect();
    let w: Vec<[F192; 64]> = (0..4).map(|l| std::array::from_fn(|z| omega[PAD_SHIFT + 64 * l + z])).collect();
    let tw: Vec<Vec<[F192; 256]>> = w.iter().map(byte_tables).collect();
    let g_of = |d: &[u64; 4]| -> F192 { (0..4).map(|l| bitdot(&tw[l], d[l])).sum() };
    let g: Vec<F192> = crate::lv::parallel::map_collect(live, |x| g_of(&ch.y[x]));
    let g_tail = g_of(&ch.y[big - 1]); // a dead row (z*), or a live one when n = 2^log_n (then no tail is read)
    let c = wire_const(fin, s, n);
    let (sigma, fin_claim, k_s, g_s) = sumcheck_ab_live(ps, k, g, g_tail, fin.value + c, ln);
    assert!(k_s == k_ch_mle(&sigma, rho, mu, m), "K̃_ch(σ) in closed form");
    assert!(fin_claim == k_s * g_s, "the wiring identity C_in = const + Σ K_ch·G_D");
    ps.add_scalar(g_s);

    // ---- T4: the D slot reduction (2 rounds over the lane), the 64 slices, the ring switch
    let eqs: Vec<F192> = if dense { eq_table(&sigma) } else { eq_prefix(&sigma, n) };
    let lt: F192 = eqs[..n].iter().copied().sum();
    assert!(lt == lt_mle(&sigma, n), "lt̃_n(σ) in closed form");
    let bmat: Vec<[F192; 64]> = (0..4)
        .map(|l| {
            let mut v = fold_1b_rows(&cmain[lay.d(l)..][..live], &eqs[..live]);
            if !dense && n < big {
                let zl = ch.y[big - 1][l];
                for (q, v) in v.iter_mut().enumerate() {
                    if (zl >> q) & 1 == 1 {
                        *v += F192::ONE + lt;
                    }
                }
            }
            v
        })
        .collect();
    let mut a: Vec<Vec<F192>> = w.iter().map(|v| v.to_vec()).collect();
    let mut b: Vec<Vec<F192>> = bmat.iter().map(|v| v.to_vec()).collect();
    let mut claim = g_s;
    let mut tau = Vec::new();
    for _ in 0..2 {
        let half = a.len() / 2;
        let (mut c0, mut c2) = (F192::ZERO, F192::ZERO);
        for j in 0..half {
            for q in 0..64 {
                let (a0, a1, b0, b1) = (a[2 * j][q], a[2 * j + 1][q], b[2 * j][q], b[2 * j + 1][q]);
                c0 += a0 * b0;
                c2 += (a0 + a1) * (b0 + b1);
            }
        }
        let c1 = claim + c2;
        ps.add_round_poly(&[c0, c1, c2], false);
        let r = ps.sample();
        claim = c0 + r * (c1 + r * c2);
        let f = |v: &Vec<Vec<F192>>| -> Vec<Vec<F192>> {
            (0..half).map(|j| (0..64).map(|q| v[2 * j][q] + r * (v[2 * j][q] + v[2 * j + 1][q])).collect()).collect()
        };
        a = f(&a);
        b = f(&b);
        tau.push(r);
    }
    let slices = b[0].clone();
    assert!(claim == (0..64).map(|q| a[0][q] * slices[q]).sum::<F192>(), "the slot reduction's final");
    ps.add_scalars(&slices);
    let map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
    Claim::Ring { offset: lay.d_off, point: [&sigma[..], &tau[..]].concat(), slices, map }
}

/// Dev checks (`lvm-prover s2check`; the crate's `cargo test` does not build with the vendored modules).
pub mod check {
    use super::*;
    fn rnd(seed: &mut u64) -> F192 {
        let mut x = || {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        };
        F192::new(x(), x(), x())
    }
    pub fn closed_forms_match_brute_force() {
        let mut seed = 0x1234_5678_9abc_def1u64;
        let w = 8;
        let sigma: Vec<F192> = (0..w).map(|_| rnd(&mut seed)).collect();
        let rho: Vec<F192> = (0..w - 4).map(|_| rnd(&mut seed)).collect();
        let mu: [F192; 16] = std::array::from_fn(|_| rnd(&mut seed));
        let iota = iota_table(&rho, &mu, 1 << w);
        let es = eq_table(&sigma);
        for m in [0usize, 1, 2, 15, 16, 17, 100, 255] {
            let brute: F192 = (0..(1usize << w)).filter(|&x| x + 1 <= m).map(|x| es[x] * iota[x + 1]).sum();
            assert_eq!(k_ch_mle(&sigma, &rho, &mu, m), brute, "K_ch at m = {m}");
        }
        for t in [0usize, 1, 15, 16, 17, 100, 256] {
            let brute: F192 = iota[..t].iter().copied().sum();
            assert_eq!(iota_prefix_sum(&rho, &mu, t), brute, "prefix at t = {t}");
        }
    }
}
