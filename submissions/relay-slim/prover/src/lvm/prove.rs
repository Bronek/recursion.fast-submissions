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

fn whir_config(levels: &[Level], grind: usize, ood: bool) -> crate::lv::pcs::whir::ProverConfig {
    config_of_levels(&levels.iter().map(|l| (l.fold, l.rate, l.cap, l.t)).collect::<Vec<_>>(), grind, ood)
}

/// Builds the recursion tables once the commitments' fixed contents are written (CH, KS, the stream, `σ'`)
/// and the header is complete (`h`): `(header, C_main, C_rec) ↦ tables` (WP-15c: the M3 section's tables,
/// whose aliased input arrays read the commitments and whose public array reads the header).
/// The second argument reads `len` words at offset `o` of `C_rec` (`true`) or `C_main` (`false`).
pub type Col<'a> = dyn Fn(bool, usize, usize) -> Vec<F64> + 'a;
pub type Build<'a> = dyn Fn(&Header, &Col) -> Vec<crate::lvm::m3::TableW> + Sync + 'a;

/// Prove the `S` statement of `hd` (with `hd.h` filled in here) at parameter set `p` on the installed oracle.
/// The recursion tables are `rec.tables`, or `build`'s (then `p` must already carry their M3 numbers).
pub fn prove(p: &Params, mut hd: Header, mut rec: RecWitness, build: Option<&Build>) -> SProof {
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
    // and C_main outside the `D` block: they are built on a third thread once the walk is done, beside the tape's
    // GKR witness (which commits nothing). P-FIX: KS's GKR witness is generated on a fourth thread beside the walk,
    // into the KS slots `[ks_off, ks_off + 50·2^ks_log)`, so that the build starts as soon as `h` is known. A read that would touch `D` or those slots is not served there:
    // the build is then redone after both are written (the old order).
    let (d_lo, d_hi) = (lay.d_off, lay.d_off + (1usize << lay.d_vars()));
    let (k_lo, k_hi) = (lay.ks_off, lay.ks_off + (50usize << lay.ks_log));
    let rec_msg = std::mem::take(&mut rec.msg);
    let t0w = Instant::now();
    let tl = std::env::var_os("LVM_LOG").is_some();
    let (chain, ks, mut cmain, mut crec, tape_w, ks_w, built, h) = std::thread::scope(|sc| {
        let (tx, rx) = std::sync::mpsc::channel();
        let s = hd.s;
        let walk = sc.spawn(move || Chain::run_gated_notify(p.log_n, &s, n, dense, move |h| tx.send(h).expect("the end of the chain")));
        let ks = Sponge::run(p.ks_log, cont, rec_msg);
        let t_s = t0w.elapsed().as_secs_f64();
        let mut cmain = vec![F64::ZERO; 1 << p.nu_main];
        let mut crec = vec![F64::ZERO; 1 << p.nu_rec()];
        let t_a = t0w.elapsed().as_secs_f64();
        tables::write_ks_lanes(&lay, &ks, &mut cmain, &mut crec);
        for (i, &w) in rec.sigma.iter().enumerate() {
            crec[lay.rec_col(REC_STREAM_COLS) + i] = F64(w);
        }
        let (chain, ks_w, tape_w, built, h) = std::thread::scope(|si| {
            let (lo, rest) = cmain.split_at_mut(k_lo);
            let (kblk, hi) = rest.split_at_mut(k_hi - k_lo);
            let (lo, hi, cr, ks_r) = (&*lo, &*hi, &crec, &ks);
            // KS's GKR witness beside the walk, into its slots
            let ksj = si.spawn(move || {
                let w = crate::lv::keccak_gkr::Witness::generate(ks_r.shape, &ks_r.inputs, kblk);
                (w, t0w.elapsed().as_secs_f64())
            });
            let h = rx.recv().expect("the walk reaches row n − 1");
            let t_h = t0w.elapsed().as_secs_f64();
            let mut hd_b = hd.clone();
            hd_b.h = h;
            let tabs = build.map(|b| {
                si.spawn(move || {
                    let hit = std::cell::Cell::new(false);
                    let col = |r: bool, o: usize, len: usize| -> Vec<F64> {
                        let e = o + len;
                        if r {
                            cr[o..e].to_vec()
                        } else if (o < d_hi && e > d_lo) || (o < k_hi && e > k_lo) {
                            hit.set(true);
                            vec![F64::ZERO; len]
                        } else if e <= k_lo {
                            lo[o..e].to_vec()
                        } else {
                            hi[o - k_hi..e - k_hi].to_vec()
                        }
                    };
                    let t = b(&hd_b, &col);
                    let t_b = t0w.elapsed().as_secs_f64();
                    (!hit.get()).then_some((t, t_b))
                })
            });
            let chain = walk.join().expect("the chain walk");
            let t_w = t0w.elapsed().as_secs_f64();
            let tape_w = crate::lv::keccak_gkr::Witness::generate_uncommitted(chain.shape, &chain.inputs);
            let t_g = t0w.elapsed().as_secs_f64();
            let (ks_w, t_k) = ksj.join().expect("KS's GKR witness");
            let built = tabs.map(|t| t.join().expect("the recursion tables"));
            if tl {
                let t_b = built.as_ref().and_then(|b| b.as_ref().map(|x| x.1));
                eprintln!(
                    "lvm: witness timeline n={n}: sponge {t_s:.3}, alloc {t_a:.3}, h at {t_h:.3}, KS witness {t_k:.3}, walk {t_w:.3}, tape witness {t_g:.3}, tables {t_b:?} s"
                );
            }
            (chain, ks_w, tape_w, built.map(|b| b.map(|x| x.0)), h)
        });
        tables::write_d(&lay, &chain, &mut cmain);
        (chain, ks, cmain, crec, tape_w, ks_w, built, h)
    });
    hd.h = chain.end(n);
    assert_eq!(hd.h, h, "chainEnd s n");
    lap("chain+sponge", &mut stages);
    if let Some(b) = build {
        rec.tables = match built.flatten() {
            Some(t) => t,
            None => b(&hd, &|r: bool, o: usize, len: usize| (if r { &crec } else { &cmain })[o..o + len].to_vec()),
        };
        rec.tables.retain(crate::lvm::m3::active);
        let sh = crate::lvm::m3::shape(&rec.tables);
        assert_eq!(sh, (p.bus_depth, p.leafdec_reads, p.table_rounds, p.table_evals), "the tables' M3 numbers are the record's");
    }
    let rec_place = crate::lvm::m3::place(&rec.tables, lay.free_lo(), p.nu_main);
    // written placements (the prover's or the M3 section's) lie above WP-15a's tables or in C_rec's free
    // columns (18–31), and do not overlap
    let mut spans: Vec<(bool, usize, usize)> = Vec::new();
    for (tw, pl) in rec.tables.iter().zip(&rec_place) {
        for c in tw.committed() {
            let w = match (pl[c], tw.pre_of(c)) {
                (Some(o), _) => Some((false, o)),
                (None, Some(x)) if tw.pre_writes(c) => Some(x),
                _ => None,
            };
            if let Some((r, o)) = w {
                let (lo, hi) = if r { ((REC_STREAM_COLS + 1) << lay.rec_log, 1 << p.nu_rec()) } else { (lay.free_lo(), 1 << p.nu_main) };
                assert!(lo <= o && o + (1 << tw.tau) <= hi, "a written table column stays in the free region");
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
    let header = hd.bytes();
    let mut ps = ProverState::seeded(&header);
    let (m0, r0) = (p.main_levels[0], p.rec_levels[0]);
    let (cm, main_data) = commit(&cmain, p.nu_main, INITIAL_FOLDING_FACTOR, m0.rate, m0.cap);
    let (cr, rec_data) = commit(&crec, p.nu_rec(), INITIAL_FOLDING_FACTOR, r0.rate, r0.cap);
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

    // ---- openings: C_rec, then C_main
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
