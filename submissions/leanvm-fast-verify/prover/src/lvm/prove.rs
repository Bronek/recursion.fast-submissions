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

fn whir_config(levels: &[Level]) -> crate::lv::pcs::whir::ProverConfig {
    config_of_levels(&levels.iter().map(|l| (l.fold, l.rate, l.cap, l.t)).collect::<Vec<_>>())
}

/// Builds the recursion tables once the commitments' fixed contents are written (CH, KS, the stream, `σ'`)
/// and the header is complete (`h`): `(header, C_main, C_rec) ↦ tables` (WP-15c: the M3 section's tables,
/// whose aliased input arrays read the commitments and whose public array reads the header).
pub type Build<'a> = dyn Fn(&Header, &[F64], &[F64]) -> Vec<crate::lvm::m3::TableW> + 'a;

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
    let mut lap = |name: &'static str, stages: &mut Vec<(&'static str, f64)>| {
        let s = t.elapsed().as_secs_f64();
        crate::lv::tracing::record(name, s);
        crate::alloc::memlog(name);
        stages.push((name, s));
        t = Instant::now();
    };
    assert_eq!(hd.acc_in.pt.len(), p.acc_d(), "acc_in has D coordinates");
    let n = hd.n as usize;
    assert!(n >= 1 && n <= 1 << p.log_n, "1 ≤ n ≤ 2^log_n (A1)");

    // ---- witness: CH, KS, C_main, C_rec
    // the two sequential Keccak walks, side by side
    let cont = tables::cont_column(p.ks_log, p.rec_rows_log, sponge_blocks(p));
    if let Ok(path) = std::env::var("LVM_REC_DUMP") {
        std::fs::write(&path, rec.dump()).expect("LVM_REC_DUMP");
    }
    let (chain, ks) = std::thread::scope(|sc| {
        let k = sc.spawn(|| Sponge::run(p.ks_log, cont, rec.msg));
        let c = Chain::run(p.log_n, &hd.s);
        (c, k.join().expect("the sponge walk"))
    });
    hd.h = chain.end(n);
    lap("chain+sponge", &mut stages);
    // SAFETY: zeroed below by `vec!`; F64 is a plain word.
    let mut cmain = vec![F64::ZERO; 1 << p.nu_main];
    let mut crec = vec![F64::ZERO; 1 << p.nu_rec()];
    let ch_w = tables::write_ch(&lay, &chain, &mut cmain);
    let ks_w = tables::write_ks(&lay, &ks, &mut cmain, &mut crec);
    for (i, &w) in rec.sigma.iter().enumerate() {
        crec[lay.rec_col(REC_STREAM_COLS) + i] = F64(w);
    }
    if let Some(b) = build {
        rec.tables = b(&hd, &cmain, &crec);
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
    let (cm, main_data) = commit(&cmain, &[], p.nu_main, INITIAL_FOLDING_FACTOR, m0.rate, m0.cap);
    let (cr, rec_data) = commit(&crec, &[], p.nu_rec(), INITIAL_FOLDING_FACTOR, r0.rate, r0.cap);
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

    // ---- CH: instance point, 25 lanes, the Keccak GKR, ring switch; fixed claims (Lean `chFixedClaims`)
    let ch_block = lay.ch_off..lay.ch_off + (1 << lay.ch_vars());
    let r = ps.sample_vec(p.log_n);
    let out = OutputClaim::of_inputs(chain.shape, &chain.inputs, r.clone());
    ps.add_scalars(&out.lanes);
    let openings = ch_w.prove(&mut ps, &cmain[ch_block.clone()], &out);
    drop(ch_w);
    let (ring, word) = openings.into_pcs_claims(lay.ch_off);
    let ch_map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
    let word = word.expect("two segments: the committed outputs' word claim");
    let StackClaim::Point { offset, low_point, value } = word;
    main_claims.push(Claim::point(offset, low_point, value));
    let rc = ring.claims.into_iter().next().unwrap();
    main_claims.push(Claim::Ring { offset: lay.ch_off, point: rc.suffix_point, slices: rc.s_hat_v.unwrap(), map: ch_map });
    for m in 0..4 {
        main_claims.push(Claim::point(lay.ch_y(m), r.clone(), out.lanes[m]));
    }
    let pad = crate::keccak::chain_block(&hd.s);
    for (l, &w) in pad.iter().enumerate() {
        main_claims.push(Claim::point(lay.ch_slot(l), bits_point(0, p.log_n), e(w)));
    }
    let hl = tables::digest_lanes(&hd.h);
    for m in 0..4 {
        main_claims.push(Claim::point(lay.ch_y(m), bits_point(n - 1, p.log_n), e(hl[m])));
    }
    lap("CH gkr", &mut stages);

    // ---- CH link
    let link_claims = link::prove_ch(&mut ps, &lay, &chain, &cmain);
    drop(chain);
    lap("CH link", &mut stages);

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

    // ---- the claim lists (Lean: bus ++ tables ++ (CH ++ KS) ++ link ++ KS outputs ++ KS link), by commitment
    main_claims.extend(link_claims);
    for l in 0..LANES {
        main_claims.push(Claim::point(lay.ks_y(l), rk.clone(), kout.lanes[l]));
    }
    for (i, c) in klink.into_iter().enumerate() {
        if i == 2 { rec_claims.push(c) } else { main_claims.push(c) }
    }
    // KS link order is [Y, in, M, X]: M is the C_rec one; the others keep their order on main.

    // ---- openings: C_rec, then C_main
    open_mixed_whir_stacked(&mut ps, p.nu_rec(), crec, rec_data, &whir_config(&p.rec_levels), rec_claims.into_iter().map(mixed).collect());
    lap("open rec", &mut stages);
    open_mixed_whir_stacked(&mut ps, p.nu_main, cmain, main_data, &whir_config(&p.main_levels), main_claims.into_iter().map(mixed).collect());
    lap("open main", &mut stages);

    assert!(ps.nothing_pending(), "the schedule ends with an FS query");
    let proof = std::mem::take(&mut ps.body);
    let trace = std::mem::take(&mut ps.trace);
    check_shape(p, &proof, &trace);
    SProof { proof, trace, h: hd.h, acc_out: fold.out, stages }
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
