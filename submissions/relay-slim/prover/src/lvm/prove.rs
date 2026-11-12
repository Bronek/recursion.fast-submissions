//! The `S` proof (BLUEPRINT §2.1, §4, §11; the Lean `V_S` on lvm/VQ, `LvmDecide.decideProg`, phase by phase).
//! The recursion part (LoopIR tables, `C_rec`'s stream and `σ'`, KS rows `≥ 2^rec`) is WP-15b's: here it is
//! the `b = 0` convention (BLUEPRINT §4.5 Gate): an all-zero stream with honest computations on it, entering
//! through [`RecWitness`].

use std::time::Instant;

use crate::format::Sig;
use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::keccak_gkr::OutputClaim;
use crate::lv::pcs::stack_open::{MixedClaim, RingClaimAt, StackClaim, open_mixed_whir_stacked};
use crate::lv::pcs::whir::{INITIAL_FOLDING_FACTOR, commit};
use crate::lv::pcs::whir_config::config_of_levels;
use crate::lv::primitives::field::{F64, F192};
use crate::lvm::link::{self, Claim};
use crate::lvm::acc::{self, Acc};
use crate::lvm::params::{self, HEADER_BASE, LANES, Level, Params, QClass, RING_STAGES, REC_STREAM_COLS, SIG_BYTES};
use crate::lvm::tables::{self, Chain, Layout, Sponge};
use crate::oracle::{Digest, Trace};

/// The statement part of the header.
#[derive(Clone, Debug)]
pub struct Header {
    pub b: u64,
    pub vk: Digest,
    pub c_l: Digest,
    pub s: Digest,
    pub n: u64,
    pub h: Digest,
    pub sig_leaf: Option<Sig>,
    /// The incoming accumulator (A23): `(0, Φ̃(0))` for an `S,0` proof, else the left child's `accOutOf`.
    pub acc_in: Acc,
}

impl Header {
    /// `'S' pad[7] | b | vk | c_L | s | n | h | σ_leaf | acc_in` (4,928 B + 24 (D + 1)).
    pub fn bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(HEADER_BASE + 24 * (self.acc_in.pt.len() + 1));
        v.push(b'S');
        v.extend_from_slice(&[0u8; 7]);
        v.extend_from_slice(&self.b.to_le_bytes());
        v.extend_from_slice(&self.vk);
        v.extend_from_slice(&self.c_l);
        v.extend_from_slice(&self.s);
        v.extend_from_slice(&self.n.to_le_bytes());
        v.extend_from_slice(&self.h);
        match &self.sig_leaf {
            Some(sig) => crate::format::put_sig(&mut v, sig),
            None => v.extend_from_slice(&[0u8; SIG_BYTES]),
        }
        assert_eq!(v.len(), HEADER_BASE);
        v.extend_from_slice(&self.acc_in.bytes());
        v
    }
}

pub use crate::lvm::rec::RecWitness;

pub struct SProof {
    pub proof: Vec<u8>,
    pub trace: Trace,
    pub h: Digest,
    /// The outgoing accumulator (`accOutOf` of this proof's stream).
    pub acc_out: Acc,
    pub stages: Vec<(&'static str, f64)>,
    /// PI-GRIND: per WHIR level (`C_rec`'s, then `C_main`'s), the attempts up to its accepted nonce
    pub grind_attempts: Vec<u64>,
}

/// `Σ (8 + |q| + 32)` + 1: the hashed length of the trace digest, and its sponge blocks.
pub fn sponge_blocks(p: &Params) -> usize {
    let l: usize = 1 + params::query_list(p).iter().map(|(_, len)| 40 + len).sum::<usize>();
    l / 136 + 1
}

fn e(x: u64) -> F192 {
    F192::new(x, 0, 0)
}

fn bits_point(x: usize, n: usize) -> Vec<F192> {
    (0..n).map(|i| e(((x >> i) & 1) as u64)).collect()
}

fn mixed(c: Claim) -> MixedClaim {
    match c {
        Claim::Point { terms, value } => MixedClaim::Point { terms, value },
        Claim::Ring { offset, point, slices, map } => MixedClaim::Ring(RingClaimAt { offset, point, slices, map }),
    }
}

/// `words` around two disjoint blocks `a` and `b`: the two blocks, mutable, and the words outside both, as `(offset,
/// words)` pieces.
fn carve(words: &mut [F64], a: std::ops::Range<usize>, b: std::ops::Range<usize>) -> (&mut [F64], &mut [F64], [(usize, &[F64]); 3]) {
    assert!(a.end <= b.start || b.end <= a.start, "the blocks are disjoint");
    let (x, y) = if a.start < b.start { (a.clone(), b.clone()) } else { (b.clone(), a.clone()) };
    let (p0, r) = words.split_at_mut(x.start);
    let (bx, r) = r.split_at_mut(x.end - x.start);
    let (p1, r) = r.split_at_mut(y.start - x.end);
    let (by, p2) = r.split_at_mut(y.end - y.start);
    let rest = [(0, &*p0), (x.end, &*p1), (y.end, &*p2)];
    if a.start < b.start { (bx, by, rest) } else { (by, bx, rest) }
}

/// P2 and P1: the tape witness's lanes that run beside the recursion-table build; the others start when the tables are
/// built. A block writes 25 rounds of 1600 × 512 bits (2.5 MB) and is bound by memory bandwidth more than by the
/// core, so two lanes all but keep pace with the walk, while seven slow the walk (an SMT sibling's share) and starve
/// the table build, the stage's critical path at short chains (measured on 4C/8T Zen 5: two lanes until the tables are
/// built, then all, beat seven throughout by 7–20 ms per step at 2^17–2^19).
const TAPE_EARLY_LANES: usize = 2;

fn whir_config(levels: &[Level], grind: usize, ood: bool) -> crate::lv::pcs::whir::ProverConfig {
    config_of_levels(&levels.iter().map(|l| (l.fold, l.rate, l.cap, l.t)).collect::<Vec<_>>(), grind, ood)
}

/// Builds the recursion tables once the commitments' fixed contents are written (CH, KS, the stream, `σ'`)
/// and the header is complete (`h`): `(header, C_main, C_rec) ↦ tables` (WP-15c: the M3 section's tables,
/// whose aliased input arrays read the commitments and whose public array reads the header).
/// The second argument reads `len` words at offset `o` of `C_rec` (`true`) or `C_main` (`false`).
pub type Col<'a> = dyn Fn(bool, usize, usize) -> Vec<F64> + 'a;
pub type Build<'a> = dyn Fn(&Header, &Col) -> Vec<crate::lvm::m3::TableW> + Sync + 'a;
/// P1: `(from, to, tables)` turns the tables built for header `from` into those of `to`, which differs from
/// `from` in `h` alone; false if they must be rebuilt instead (`Ctx::patch_tables`).
pub type Patch<'a> = dyn Fn(&Header, &Header, &mut [crate::lvm::m3::TableW]) -> bool + Sync + 'a;

/// Prove the `S` statement of `hd` (with `hd.h` filled in here) at parameter set `p` on the installed oracle.
/// The recursion tables are `rec.tables`, or `build`'s (then `p` must already carry their M3 numbers). With `patch`,
/// `build` runs from the start on `hd` as given (its `h` a placeholder), and `patch` brings the tables to the real `h`.
pub fn prove(p: &Params, mut hd: Header, mut rec: RecWitness, build: Option<&Build>, patch: Option<&Patch>) -> SProof {
    rec.tables.retain(crate::lvm::m3::active);
    // with recursion tables, the schedule's bus and table numbers are theirs (the program `Q` fixes them;
    // the record `P20`/`P8` carries them once `Q` is final)
    let p_rec;
    let p = if rec.tables.is_empty() {
        p
    } else {
        let (d, l, r, e) = crate::lvm::m3::shape(&rec.tables);
        p_rec = Params { bus_depth: d, leafdec_reads: l, table_rounds: r, table_evals: e, ..p.clone() };
        &p_rec
    };
    let lay = Layout::new(p);
    let mut stages = Vec::new();
    let mut t = Instant::now();
    let prof = crate::lv::tracing::enabled();
    let mut c0 = if prof { crate::lv::tracing::cpu_now() } else { (0.0, 0.0) };
    let mut lap = |name: &'static str, stages: &mut Vec<(&'static str, f64)>| {
        let s = t.elapsed().as_secs_f64();
        crate::lv::tracing::record(name, s);
        if prof {
            let c = crate::lv::tracing::cpu_now();
            eprintln!("  PCPU {name:<14} wall {s:.3} cpu {:.3} svc {:.2}", c.0 - c0.0, c.1 - c0.1);
            c0 = c;
        }
        crate::alloc::memlog(name);
        stages.push((name, s));
        t = Instant::now();
    };
    assert_eq!(hd.acc_in.pt.len(), p.acc_d(), "acc_in has D coordinates");
    let n = hd.n as usize;
    assert!(n >= 1 && n <= 1 << p.log_n, "1 ≤ n ≤ 2^log_n (A1)");
    // S1 (BLUEPRINT2 §2.1): rows ≥ n hold the zero input and the CH link is gated by `[k ≤ m]`. The prover runs the
    // written prefix with leanVM's padding block and sums the padding in closed form; `LVM_PGATE=dense` runs and sums
    // every row instead, the byte-identity oracle (the same proof bytes).
    let dense = std::env::var("LVM_PGATE").is_ok_and(|m| m == "dense");

    // ---- witness: CH, KS, C_main, C_rec
    // the two sequential Keccak walks, side by side
    let cont = tables::cont_column(p.ks_log, p.rec_rows_log, sponge_blocks(p));
    if let Ok(path) = std::env::var("LVM_REC_DUMP") {
        std::fs::write(&path, rec.dump()).expect("LVM_REC_DUMP");
    }
    // P-QUICK lever 3 (prover-only: the same columns and tables, computed in another order): the serial chain
    // walk runs on its own thread; meanwhile this thread runs the sponge walk, allocates the commitments and
    // writes KS's lanes, σ' and the stream. The recursion tables need `h = chainEnd s n` (the header) and read C_rec
    // and C_main outside the `D` block: they are built on a third thread once the walk is done. P-FIX: KS's GKR
    // witness is generated on a fourth thread beside the walk, into the KS slots `[ks_off, ks_off + 50·2^ks_log)`, so
    // that the build starts as soon as `h` is known. A read that would touch `D` or those slots is not served there:
    // the build is then redone after both are written (the old order). P2: the tape's GKR witness (which commits
    // nothing) runs behind the walk on the fourth thread once KS's is done, on the pool's thread count less the
    // walk's, each block as soon as the walk has published the `Y` rows its inputs read ([`tables::Feed`]); all but
    // `TAPE_EARLY_LANES` of those threads wait for the tables. P1: with `patch`, the tables are built from the
    // start on the header's placeholder `h` and patched once the walk has ended (`h` reaches them through the header
    // array's value column alone: `Ctx::patch_tables`, which says when it cannot apply and the tables are rebuilt).
    let (d_lo, d_hi) = (lay.d_off, lay.d_off + (1usize << lay.d_vars()));
    let (k_lo, k_hi) = (lay.ks_off, lay.ks_off + (50usize << lay.ks_log));
    let rec_msg = std::mem::take(&mut rec.msg);
    let t0w = Instant::now();
    let tl = std::env::var_os("LVM_LOG").is_some();
    let big = 1usize << p.log_n;
    // the tape's written rows (S1): the `n` live ones, or every row (dense: rows `≥ n` hold the zero input)
    let rows = if dense { big } else { n };
    // SAFETY: every element is written before it is read. `Y`'s live rows are written by the walk, and read only
    // after it has published their block; its dead rows by the walk's thread once the walk is done, before the scope
    // ends. Each block of tape inputs is written by the lane the counter hands the block to, before the block runs.
    let mut y = unsafe { crate::lv::primitives::uninit_vec::<[u64; 4]>(big) };
    let mut tape_in = unsafe { crate::lv::primitives::uninit_vec::<[u64; LANES]>(rows) };
    let (y_live, y_dead) = y.split_at_mut(n);
    let feed = tables::Feed::new(&hd.s, n);
    let in_blocks: Vec<std::sync::Mutex<Option<&mut [[u64; LANES]]>>> =
        tape_in.chunks_mut(crate::lv::keccak_gkr::witness::BLOCK).map(|b| std::sync::Mutex::new(Some(b))).collect();
    let lanes = crate::lv::parallel::num_threads().saturating_sub(1).max(1);
    // the tape's lanes past the first `TAPE_EARLY_LANES` start once the recursion tables are built
    let tables_done = std::sync::OnceLock::<()>::new();
    if build.is_none() {
        let _ = tables_done.set(());
    }
    let (ks, mut cmain, mut crec, tape_w, ks_w, built, h) = std::thread::scope(|sc| {
        let (tx, rx) = std::sync::mpsc::channel();
        let (feed, in_blocks, tables_done) = (&feed, &in_blocks, &tables_done);
        let walk = sc.spawn(move || {
            let h = feed.walk(y_live);
            tx.send(tables::lanes_digest(&h)).expect("the end of the chain");
            // rows `≥ n`: `Y = Keccak-f(0)[0..4)`
            let mut z = [0u64; LANES];
            crate::lv::primitives::hash::keccak_f(&mut z);
            y_dead.fill([z[0], z[1], z[2], z[3]]);
            t0w.elapsed().as_secs_f64()
        });
        let ks = Sponge::run(p.ks_log, cont, rec_msg);
        let t_s = t0w.elapsed().as_secs_f64();
        let mut cmain = vec![F64::ZERO; 1 << p.nu_main];
        let mut crec = vec![F64::ZERO; 1 << p.nu_rec()];
        let t_a = t0w.elapsed().as_secs_f64();
        tables::write_ks_lanes(&lay, &ks, &mut cmain, &mut crec);
        for (i, &w) in rec.sigma.iter().enumerate() {
            crec[lay.rec_col(REC_STREAM_COLS) + i] = F64(w);
        }
        let (ks_w, tape_w, built, h) = std::thread::scope(|si| {
            // C_main around the two blocks written beside the table build: `D` (this thread, once the walk has ended)
            // and KS's GKR slots (KS's witness); the build reads the rest
            let (dblk, kblk, rest) = carve(&mut cmain, d_lo..d_hi, k_lo..k_hi);
            let (cr, ks_r) = (&crec, &ks);
            let tables_for = |hd_b: Header| {
                build.map(|b| {
                    si.spawn(move || {
                        let hit = std::cell::Cell::new(false);
                        let col = |r: bool, o: usize, len: usize| -> Vec<F64> {
                            let e = o + len;
                            if r {
                                cr[o..e].to_vec()
                            } else if let Some((at, w)) = rest.iter().find(|(at, w)| *at <= o && e <= at + w.len()) {
                                w[o - at..e - at].to_vec()
                            } else {
                                // the read touches `D` or KS's slots
                                hit.set(true);
                                vec![F64::ZERO; len]
                            }
                        };
                        let t = b(&hd_b, &col);
                        let _ = tables_done.set(());
                        let t_b = t0w.elapsed().as_secs_f64();
                        (!hit.get()).then_some((t, t_b))
                    })
                })
            };
            // P1: with a patch, the tables are built from the start, on the placeholder `h`
            let early = if patch.is_some() { tables_for(hd.clone()) } else { None };
            // KS's GKR witness beside the walk, into its slots; then the tape's, behind the walk
            let wj = si.spawn(move || {
                let w = crate::lv::keccak_gkr::Witness::generate(ks_r.shape, &ks_r.inputs, kblk);
                let t_k = t0w.elapsed().as_secs_f64();
                let start = |i: usize| {
                    if i >= TAPE_EARLY_LANES {
                        tables_done.wait();
                    }
                };
                let tape = crate::lv::keccak_gkr::Witness::generate_uncommitted_by(Chain::tape_shape(p.log_n), rows, lanes, start, |g| {
                    let block = in_blocks[g].lock().unwrap().take().expect("a block of tape inputs is taken once");
                    let inputs = feed.inputs(g, block);
                    #[cfg(feature = "np12-faults")]
                    let inputs = tables::fault::tape_block(g, inputs);
                    inputs
                });
                #[cfg(feature = "np12-faults")]
                let tape = {
                    let mut tape = tape;
                    tables::fault::tape_word(&mut tape);
                    tape
                };
                (w, t_k, tape, t0w.elapsed().as_secs_f64())
            });
            let h = rx.recv().expect("the walk reaches row n − 1");
            let t_h = t0w.elapsed().as_secs_f64();
            let tabs = if patch.is_some() {
                early
            } else {
                let mut hd_b = hd.clone();
                hd_b.h = h;
                tables_for(hd_b)
            };
            // `D` (S2) from the published rows, beside the tape witness and the tables
            let mut z = [0u64; LANES];
            crate::lv::primitives::hash::keccak_f(&mut z);
            feed.write_d(dblk, [z[0], z[1], z[2], z[3]]);
            let t_w = walk.join().expect("the chain walk");
            let (ks_w, t_k, tape_w, t_g) = wj.join().expect("KS's and the tape's GKR witnesses");
            let built = tabs.map(|t| t.join().expect("the recursion tables"));
            if tl {
                let t_b = built.as_ref().and_then(|b| b.as_ref().map(|x| x.1));
                eprintln!(
                    "lvm: witness timeline n={n}: sponge {t_s:.3}, alloc {t_a:.3}, h at {t_h:.3}, KS witness {t_k:.3}, walk {t_w:.3}, tape witness {t_g:.3}, tables {t_b:?} s"
                );
            }
            (ks_w, tape_w, built.map(|b| b.map(|x| x.0)), h)
        });
        (ks, cmain, crec, tape_w, ks_w, built, h)
    });
    drop((in_blocks, feed));
    let chain = Chain { shape: Chain::tape_shape(p.log_n), inputs: tape_in, y };
    let hd_early = patch.map(|_| hd.clone());
    hd.h = chain.end(n);
    assert_eq!(hd.h, h, "chainEnd s n");
    lap("chain+sponge", &mut stages);
    if let Some(b) = build {
        let rebuild = |hd: &Header| b(hd, &|r: bool, o: usize, len: usize| (if r { &crec } else { &cmain })[o..o + len].to_vec());
        rec.tables = match (built.flatten(), patch.zip(hd_early.as_ref())) {
            (Some(t), None) => t,
            (Some(mut t), Some((f, from))) => {
                let ok = f(from, &hd, &mut t);
                if tl {
                    eprintln!("lvm: recursion tables built on the placeholder h, {}", if ok { "patched" } else { "rebuilt (the patch does not apply)" });
                }
                if ok { t } else { rebuild(&hd) }
            }
            (None, _) => rebuild(&hd),
        };
        rec.tables.retain(crate::lvm::m3::active);
        let sh = crate::lvm::m3::shape(&rec.tables);
        assert_eq!(sh, (p.bus_depth, p.leafdec_reads, p.table_rounds, p.table_evals), "the tables' M3 numbers are the record's");
    }
    // A stack's root leaves carry its occupied lanes alone (the record's level-0 row, `params::occ_lanes`): the lanes
    // past them hold no data, so they are not encoded, hashed or sent, and the verifier reads them as zero.
    let (occ_main, occ_rec) = (params::occ_lanes(&p.main_levels), params::occ_lanes(&p.rec_levels));
    let main_words = occ_main << (p.nu_main - INITIAL_FOLDING_FACTOR);
    let rec_words = occ_rec << (p.nu_rec() - INITIAL_FOLDING_FACTOR);
    let rec_place = crate::lvm::m3::place(&rec.tables, lay.free_lo(), p.nu_main);
    // written placements (the prover's or the M3 section's) lie above WP-15a's tables or in C_rec's free
    // columns (18–31), below the stack's occupied lanes (so none lies in C_rec while its leaves carry the stream
    // and σ' alone), and do not overlap
    let mut spans: Vec<(bool, usize, usize)> = Vec::new();
    for (tw, pl) in rec.tables.iter().zip(&rec_place) {
        for c in tw.committed() {
            let w = match (pl[c], tw.pre_of(c)) {
                (Some(o), _) => Some((false, o)),
                (None, Some(x)) if tw.pre_writes(c) => Some(x),
                _ => None,
            };
            if let Some((r, o)) = w {
                let (lo, hi) = if r { ((REC_STREAM_COLS + 1) << lay.rec_log, rec_words) } else { (lay.free_lo(), main_words) };
                assert!(
                    lo <= o && o + (1 << tw.tau) <= hi,
                    "a written table column stays in the free region, below its stack's occupied lanes"
                );
                spans.push((r, o, o + (1 << tw.tau)));
            }
        }
    }
    spans.sort();
    assert!(spans.windows(2).all(|w| w[0].0 != w[1].0 || w[0].2 <= w[1].1), "written table columns do not overlap");
    for (tw, pl) in rec.tables.iter().zip(&rec_place) {
        for (c, (col, o)) in tw.cols.iter().zip(pl).enumerate() {
            if let Some(o) = o {
                cmain[*o..*o + col.len()].copy_from_slice(col);
            }
            if let Some((r, o)) = tw.pre_of(c) {
                let dst = if r { &mut crec[o..o + col.len()] } else { &mut cmain[o..o + col.len()] };
                if tw.pre_writes(c) {
                    dst.copy_from_slice(col);
                } else {
                    assert!(dst == &col[..], "a pre-placed column holds the table's values");
                }
            }
        }
    }
    lap("witness", &mut stages);

    // ---- commit
    // The controls' build (cargo feature `np12-faults`) and debug builds check that nothing lies past the placements:
    // C_main's words are written below `free_lo` (the fixed blocks) and in the placed table columns (`spans`), C_rec's
    // in the stream, `σ'` and its placed columns.
    #[cfg(any(debug_assertions, feature = "np12-faults"))]
    {
        let past_main = spans.iter().filter(|s| !s.0).map(|s| s.2).fold(lay.free_lo(), usize::max);
        let past_rec = spans.iter().filter(|s| s.0).map(|s| s.2).fold(lay.rec_col(REC_STREAM_COLS) + rec.sigma.len(), usize::max);
        #[cfg(feature = "np12-faults")]
        if std::env::var_os("LVM_LANES_FAULT_PAST").is_some() {
            eprintln!("lvm: np12-fault: a word of C_main past the placements");
            cmain[past_main].0 ^= 1;
        }
        assert!(cmain[past_main..].iter().all(|w| w.0 == 0) && crec[past_rec..].iter().all(|w| w.0 == 0), "nothing past the placements");
    }
    if tl {
        eprintln!("lvm: committed lanes: C_main {occ_main} of 64, C_rec {occ_rec} of 64");
    }
    let header = hd.bytes();
    let mut ps = ProverState::seeded(&header);
    let (m0, r0) = (p.main_levels[0], p.rec_levels[0]);
    // Each stack is committed truncated to its occupied lanes (`main_words`, `rec_words`, above); every claim must lie
    // in the committed lanes (`open_mixed_whir_stacked` asserts it).
    #[cfg(feature = "selfcheck")]
    {
        assert!(cmain[main_words..].iter().all(|w| *w == F64::ZERO), "C_main past its {occ_main} occupied lanes is zero");
        assert!(crec[rec_words..].iter().all(|w| *w == F64::ZERO), "C_rec past its {occ_rec} occupied lanes is zero");
    }
    let (cm, main_data) = commit(&cmain[..main_words], p.nu_main, INITIAL_FOLDING_FACTOR, m0.rate, m0.cap, occ_main);
    let (cr, rec_data) = commit(&crec[..rec_words], p.nu_rec(), INITIAL_FOLDING_FACTOR, r0.rate, r0.cap, occ_rec);
    ps.add_cap(&cm.cap);
    ps.add_cap(&cr.cap);
    lap("commit", &mut stages);

    // ---- bus, tables: the real ones over the recursion tables, else WP-15a's null instance
    let mut main_claims: Vec<Claim> = Vec::new();
    let mut rec_claims: Vec<Claim> = Vec::new();
    let (table_point, v_fix) = if rec.tables.is_empty() {
        crate::lvm::bus::prove_null_bus(&mut ps, p);
        (crate::lvm::bus::prove_null_tables(&mut ps, p), Vec::new())
    } else {
        let mo = crate::lvm::m3::prove(&mut ps, &rec.tables);
        // the tables' column claims (V_S: `bus.claims ++ m.tableClaims evals ++ …`): committed columns only
        for ((cl, tw), pl) in mo.claims.iter().zip(&rec.tables).zip(&rec_place) {
            for c in tw.committed() {
                match tw.pre_of(c) {
                    Some((true, o)) => rec_claims.push(Claim::point(o, cl.chi.clone(), cl.evals[c])),
                    Some((false, o)) => main_claims.push(Claim::point(o, cl.chi.clone(), cl.evals[c])),
                    None => main_claims.push(Claim::point(pl[c].unwrap(), cl.chi.clone(), cl.evals[c])),
                }
            }
        }
        let point = mo.claims.iter().map(|c| &c.chi).max_by_key(|c| c.len()).cloned().unwrap_or_default();
        let evals: Vec<F192> = mo.claims.iter().flat_map(|c| c.evals.iter().copied()).collect();
        (point, acc::fix_index(&rec.tables, p.pub_tab).into_iter().map(|i| evals[i]).collect())
    };
    lap("bus+tables", &mut stages);

    // ---- phase 3b (A23): fold acc_in with this proof's fixed-column claims
    let fold = acc::prove(&mut ps, p, &hd.acc_in, &table_point, &v_fix, &acc::fix_cols(&rec.tables, p.pub_tab));
    stages.push(("line eval", fold.secs));
    lap("acc", &mut stages);

    // ---- Tape (BLUEPRINT2 §1.2 T1–T2, S2; T-P1 C.3–C.4): r, the 25 output lanes, the depth-24 GKR to the input claim
    let r = ps.sample_vec(p.log_n);
    let out = if dense {
        OutputClaim::of_inputs(chain.shape, &chain.inputs, r.clone())
    } else {
        OutputClaim::of_inputs_padded(chain.shape, &chain.inputs, r.clone())
    };
    ps.add_scalars(&out.lanes);
    let fin = tape_w.prove_tape(&mut ps, &out);
    drop(tape_w);
    lap("tape", &mut stages);

    // ---- Wire (T3–T4; T-P1 C.5–C.6), then the CH claims in the order of C.7: T1's words, the D ring, the boundary
    let d_ring = crate::lvm::wire::prove_wire(&mut ps, &lay, &chain, &cmain, &fin, &hd.s, n, dense);
    for l in 0..4 {
        main_claims.push(Claim::point(lay.d(l), r.clone(), out.lanes[l]));
    }
    main_claims.push(d_ring);
    let hl = tables::digest_lanes(&hd.h);
    for l in 0..4 {
        main_claims.push(Claim::point(lay.d(l), bits_point(n - 1, p.log_n), e(hl[l])));
    }
    drop(chain);
    lap("wire", &mut stages);

    // ---- KS
    let ks_block = lay.ks_off..lay.ks_off + (1 << lay.ks_vars());
    let rk = ps.sample_vec(p.ks_log);
    let kout = OutputClaim::of_inputs(ks.shape, &ks.inputs, rk.clone());
    ps.add_scalars(&kout.lanes);
    let kopen = ks_w.prove(&mut ps, &cmain[ks_block], &kout);
    drop(ks_w);
    let (kring, kword) = kopen.into_pcs_claims(lay.ks_off);
    let ks_map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
    let StackClaim::Point { offset, low_point, value } = kword.expect("the KS word claim");
    main_claims.push(Claim::point(offset, low_point, value));
    let krc = kring.claims.into_iter().next().unwrap();
    main_claims.push(Claim::Ring { offset: lay.ks_off, point: krc.suffix_point, slices: krc.s_hat_v.unwrap(), map: ks_map });
    lap("KS gkr", &mut stages);

    // ---- KS link
    let klink = link::prove_ks(&mut ps, &lay, &ks);
    drop(ks);
    lap("KS link", &mut stages);

    // ---- the claim lists (S2, T-P1 C.7: bus ++ tables ++ (T1 words ++ D ring ++ boundary) ++ KS ++ KS outputs ++ KS link)
    for l in 0..LANES {
        main_claims.push(Claim::point(lay.ks_y(l), rk.clone(), kout.lanes[l]));
    }
    for (i, c) in klink.into_iter().enumerate() {
        if i == 2 { rec_claims.push(c) } else { main_claims.push(c) }
    }
    // KS link order is [Y, in, M, X]: M is the C_rec one; the others keep their order on main.

    // ---- openings: C_rec, then C_main, each of its committed lanes
    crec.truncate(rec_words);
    cmain.truncate(main_words);
    open_mixed_whir_stacked(&mut ps, p.nu_rec(), crec, rec_data, &whir_config(&p.rec_levels, p.grind, false), rec_claims.into_iter().map(mixed).collect());
    lap("open rec", &mut stages);
    open_mixed_whir_stacked(&mut ps, p.nu_main, cmain, main_data, &whir_config(&p.main_levels, p.grind, p.main_ood), main_claims.into_iter().map(mixed).collect());
    lap("open main", &mut stages);

    assert!(ps.nothing_pending(), "the schedule ends with an FS query");
    let grind_attempts = std::mem::take(&mut ps.grind_attempts);
    assert_eq!(grind_attempts.len(), if p.grind > 0 { p.rec_levels.len() + p.main_levels.len() } else { 0 }, "one grind per WHIR level");
    let proof = std::mem::take(&mut ps.body);
    let trace = std::mem::take(&mut ps.trace);
    check_shape(p, &proof, &trace);
    SProof { proof, trace, h: hd.h, acc_out: fold.out, stages, grind_attempts }
}

/// The proof has the schedule's size and the trace the schedule's query classes and lengths, in order.
pub fn check_shape(p: &Params, proof: &[u8], trace: &Trace) {
    assert_eq!(proof.len(), params::pi_size(p), "piSize");
    let want = params::query_list(p);
    assert_eq!(trace.len(), want.len(), "qS");
    for (i, ((q, _), (cls, len))) in trace.iter().zip(&want).enumerate() {
        assert_eq!(q.len(), *len, "query {i} ({cls:?}) length");
        if *cls == QClass::Seed {
            assert_eq!(&q[32..], &proof[8..params::header_bytes(p)], "the seed carries the header");
        }
    }
}
