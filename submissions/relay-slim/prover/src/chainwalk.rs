//! PORT-12: the CH chain walk's permutation kernel, chosen once per process before `ready`.
//!
//! * `Lv`: the vendored single-state AVX-512 `keccak_f` (5 zmm rows; P-QUICK lever 2), one call per step;
//! * `Vl`: relay-echo's (PR #12) `avx512vl` chain kernel (`keccak_vl`): the whole walk in one asm loop, one
//!   lane per xmm register, round 0 and round 23 specialised to the chain block; it writes `Y_i` per step.
//!
//! Both compute the same chain (`kat keccak` checks `Vl` against `keccak::chain_step`), so the choice never
//! changes a proof byte. `LVM_CHAIN_KERNEL=lv|vl` forces it; otherwise both are timed on a short chain and
//! `Vl` is taken only if it is at least 3 % faster. On the dev VM (Skylake-class, AVX-512 without VPCLMUL)
//! `Lv` wins (≈ 250 against ≈ 340–400 ns per step); relay-echo measured `avx512vl` 1.37× faster than a
//! 5-zmm-row kernel on Zen 5, so the evaluation machine (Zen 4) decides at run time.
use std::sync::OnceLock;
use std::time::Instant;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kernel {
    Lv,
    Vl,
}

/// The choice and the two timings (ns per step; 0 when not timed).
static CHOICE: OnceLock<(Kernel, f64, f64)> = OnceLock::new();

/// The chain block `0x43 ‖ d ‖ 0x01 ‖ 0^101 ‖ 0x80` from the digest's lanes (`keccak::chain_block`).
#[inline(always)]
pub fn block_of_lanes(w: &[u64; 4]) -> [u64; 25] {
    let mut a = [0u64; 25];
    a[0] = 0x43 | (w[0] << 8);
    a[1] = (w[0] >> 56) | (w[1] << 8);
    a[2] = (w[1] >> 56) | (w[2] << 8);
    a[3] = (w[2] >> 56) | (w[3] << 8);
    a[4] = (w[3] >> 56) | (0x01 << 8);
    a[16] = 0x80u64 << 56;
    a
}

/// `y[i]` = lanes 0–3 of chain step `i`'s output, from the start lanes `h`, with `Lv`. Returns the end.
fn walk_lv(mut h: [u64; 4], y: &mut [[u64; 4]]) -> [u64; 4] {
    for yi in y.iter_mut() {
        let mut b = block_of_lanes(&h);
        crate::lv::primitives::hash::keccak_f(&mut b);
        h = [b[0], b[1], b[2], b[3]];
        *yi = h;
    }
    h
}

/// The same with kernel `k` (`Vl` only where this build carries it).
pub fn walk_y(k: Kernel, h: [u64; 4], y: &mut [[u64; 4]]) -> [u64; 4] {
    match k {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl", target_feature = "avx512dq"))]
        Kernel::Vl => crate::keccak_vl::walk(h, y),
        _ => walk_lv(h, y),
    }
}

fn choose() -> (Kernel, f64, f64) {
    match std::env::var("LVM_CHAIN_KERNEL").as_deref() {
        Ok("lv") => return (Kernel::Lv, 0.0, 0.0),
        Ok("vl") if crate::keccak_vl::AVAILABLE => return (Kernel::Vl, 0.0, 0.0),
        _ => {}
    }
    if !crate::keccak_vl::AVAILABLE {
        return (Kernel::Lv, 0.0, 0.0);
    }
    // best of 7 alternating rounds of 4096 steps each (≈ 25 ms in all): interference only slows a round
    const N: usize = 4096;
    let mut y = vec![[0u64; 4]; N];
    let mut h = [0x0123_4567_89ab_cdef, 1, 2, 3];
    let (mut t_lv, mut t_vl) = (f64::MAX, f64::MAX);
    for r in 0..7 {
        for k in if r % 2 == 0 { [Kernel::Lv, Kernel::Vl] } else { [Kernel::Vl, Kernel::Lv] } {
            let t = Instant::now();
            h = walk_y(k, h, &mut y);
            let dt = t.elapsed().as_secs_f64() * 1e9 / N as f64;
            if k == Kernel::Lv { t_lv = t_lv.min(dt) } else { t_vl = t_vl.min(dt) }
        }
    }
    std::hint::black_box(h);
    (if t_vl < 0.97 * t_lv { Kernel::Vl } else { Kernel::Lv }, t_lv, t_vl)
}

/// The kernel for this process (timed once, at the first call: call it before `ready`).
pub fn select() -> Kernel {
    CHOICE.get_or_init(choose).0
}

/// For logs: the choice and its timings.
pub fn info() -> String {
    let (k, a, b) = *CHOICE.get_or_init(choose);
    if a > 0.0 {
        format!("chain kernel {k:?} (lv {a:.0} ns, vl {b:.0} ns per step)")
    } else {
        format!("chain kernel {k:?}")
    }
}

/// The CH walk: `n` steps from `s`; `inputs[i]` the absorbed block of row `i`, `y[i]` lanes 0–3 of its output.
/// `at_end(lanes of chainEnd s n_end)` is called as soon as row `n_end − 1` is done (`n_end = 0`: never; P-QUICK's
/// `Chain::run_notify`). The steps run in blocks of 1024 so that a block's inputs are written while its `Y` is
/// in cache.
pub fn walk(k: Kernel, s: [u64; 4], n: usize, n_end: usize, at_end: impl FnMut([u64; 4])) -> (Vec<[u64; 25]>, Vec<[u64; 4]>) {
    walk_cap(k, s, n, n_end, n, n, at_end)
}

/// [`walk`], with the vectors' capacities given (P-FIX2: S2's gated walk pads them to `2^log_n` rows after).
pub fn walk_cap(
    k: Kernel,
    s: [u64; 4],
    n: usize,
    n_end: usize,
    cap_in: usize,
    cap_y: usize,
    mut at_end: impl FnMut([u64; 4]),
) -> (Vec<[u64; 25]>, Vec<[u64; 4]>) {
    let mut inputs: Vec<[u64; 25]> = Vec::with_capacity(cap_in.max(n));
    let mut y = Vec::with_capacity(cap_y.max(n));
    y.resize(n, [0u64; 4]);
    let mut h = s;
    let cut = if n_end > 0 && n_end <= n { n_end } else { n };
    let (a, b) = y.split_at_mut(cut);
    for (part, last) in [(a, true), (b, false)] {
        if k == Kernel::Lv {
            // one block per step, recorded before the permutation (P-QUICK's loop, on lanes)
            for yi in part.iter_mut() {
                let a = block_of_lanes(&h);
                inputs.push(a);
                let mut b = a;
                crate::lv::primitives::hash::keccak_f(&mut b);
                h = [b[0], b[1], b[2], b[3]];
                *yi = h;
            }
        } else {
            for blk in part.chunks_mut(1024) {
                inputs.push(block_of_lanes(&h));
                h = walk_y(k, h, blk);
                let m = blk.len();
                inputs.extend(blk[..m - 1].iter().map(block_of_lanes));
            }
        }
        if last && n_end > 0 && cut == n_end {
            at_end(h);
        }
    }
    (inputs, y)
}
