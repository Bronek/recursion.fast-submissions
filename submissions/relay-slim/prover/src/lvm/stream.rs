//! The stream driver (PROVER.md §3; BLUEPRINT §0, §11 A2): `first` = `S,0` on chain A, then `S,1` on chain B
//! whose left child is that proof (3 SIGNs: the empty trace once for `σ_leaf`, A, the output); `step` = one
//! `S,1` on the new chain with the previous signed proof as the left child, `σ_leaf` reused from its header
//! (1 SIGN). The trace of every proof is the verifier's query sequence, which the prover recorded while
//! proving (the same queries and answers `V_S` replays), signed by one `SIGN`; the file is FORMAT.md's.
//! The recursion witness of every `S,1` proof is its left child's (`RecWitness::from_child`, WP-15b);
//! `S,0` keeps the zero convention. Dev only: `LVM_SAVE_CHILD=FILE` writes step 1's intermediate `S,0` proof.

use std::time::Instant;

use crate::format::{self, Sig, Signed};
use crate::lv::primitives::field::F64;
use crate::keccak::{leaf_stmt, node_stmt};
use crate::lvm::acc::{self, Acc};
use crate::lvm::params::{self, HEADER_BASE, Params};
use crate::lvm::prove::{Header, RecWitness, prove};
use crate::oracle::Digest;
use crate::service::{Service, fatal};

/// The node programs (WP-16a, `qasm gen P20|P8`: program, M3B tables, PUBX): every `S` proof carries its tables.
pub const Q_P20: &str = include_str!("q-p20.blob");
pub const Q_P8: &str = include_str!("q-p8.blob");

pub fn unhex(s: &str) -> Digest {
    let s = s.trim();
    if s.len() != 64 || !s.bytes().all(|c| c.is_ascii_hexdigit()) {
        fatal(&format!("not a 64-hex digest: {s:?}"));
    }
    std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

fn read(dir: &str, name: &str) -> Vec<u8> {
    std::fs::read(format!("{dir}/{name}")).unwrap_or_else(|e| fatal(&format!("{dir}/{name}: {e}")))
}

/// The statement an `S` header proves (`Header.stmt` of the Lean driver).
pub fn stmt_of(hd: &Header) -> Digest {
    let leaf = leaf_stmt(&hd.h, hd.n);
    if hd.b == 0 { leaf } else { node_stmt(&hd.c_l, &leaf) }
}

/// The header fields of a proof at `p`.
pub fn header_of(p: &Params, pi: &[u8]) -> Header {
    let hb = params::header_bytes(p);
    if pi.len() < hb || pi[0] != b'S' {
        fatal("the proof is not an S proof with a header");
    }
    let d = |o: usize| -> Digest { pi[o..o + 32].try_into().unwrap() };
    let u = |o: usize| u64::from_le_bytes(pi[o..o + 8].try_into().unwrap());
    let sig = format::from_sig_bytes(&pi[152..HEADER_BASE]);
    let acc_in = Acc::parse(&pi[HEADER_BASE..hb], p.acc_d());
    Header { b: u(8), vk: d(16), c_l: d(48), s: d(80), n: u(112), h: d(120), sig_leaf: Some(sig), acc_in }
}

pub struct Ctx {
    pub p: Params,
    pub svc: &'static Service,
    pub vk: Digest,
    pub log: bool,
    /// The LoopIR program whose tables every proof carries (dev: `LVM_LOOP_BLOB`; its inputs are the
    /// stream lanes), with its blob's M3 section if any; `None`: WP-15a's null bus.
    pub q: Option<(crate::lvm::loopir::Compiled, Option<crate::lvm::loopir::M3Spec>)>,
    /// `Φ̃(0)` (A23: step 1's `S,0` carries `acc_in = (0, Φ̃(0))`), from the zero build.
    pub phi0: crate::lv::primitives::field::F192,
}

impl Ctx {
    /// Attach the program (dev: `LVM_LOOP_BLOB`) and fix the schedule numbers its tables make (they replace
    /// the record's when they differ: test programs; the real `Q`'s are the record's).
    pub fn with_loop(mut self) -> Self {
        // the shipped prover carries the node program of its parameter set (WP-16a: `qasm gen`'s blobs);
        // dev: `LVM_LOOP_BLOB` replaces it, `LVM_LOOP_BLOB=none` runs without one (WP-15a's null bus)
        let blob = match std::env::var("LVM_LOOP_BLOB") {
            Ok(path) if path == "none" => None,
            Ok(path) => Some(std::fs::read_to_string(&path).unwrap_or_else(|e| fatal(&format!("{path}: {e}")))),
            Err(_) => match self.p.name {
                "P20" => Some(Q_P20.to_string()),
                "P8" => Some(Q_P8.to_string()),
                _ => None,
            },
        };
        if let Some(text) = blob {
            let (q, spec) = crate::lvm::loopir::parse_blob(&text);
            // A23: the header array selects the header lanes from byte 8 (`Pub.hdrLanes` = `pub_lanes` without `c`),
            // every other public array the constant lanes after them (PUBX)
            if let Some(s) = &spec {
                let hl = crate::lvm::m3::pub_lanes_len(&self.p);
                let want: Vec<usize> = (0..5).chain(9..hl).collect();
                for a in s.arrs.iter().filter(|a| a.kind == crate::lvm::loopir::ArrKind::Public) {
                    if a.sel.iter().any(|&i| i < hl) && a.sel != want {
                        fatal("the blob's header array does not select the A23 header lanes (regenerate it: qasm gen)");
                    }
                }
            }
            self.q = Some((crate::lvm::loopir::Compiled::new(q), spec));
            let z = match &self.q {
                Some((_, Some(_))) => self.build_tables(&|_, _, n| vec![F64::ZERO; n], &vec![0; crate::lvm::m3::pub_lanes_len(&self.p)]),
                _ => self.attach(RecWitness::zero(&self.p)).tables,
            };
            let z: Vec<_> = z.into_iter().filter(crate::lvm::m3::active).collect();
            let (d, l, r, e) = crate::lvm::m3::shape(&z);
            if (d, l, r, e) != (self.p.bus_depth, self.p.leafdec_reads, self.p.table_rounds, self.p.table_evals) {
                if std::env::var_os("LVM_M3_OVERRIDE").is_none() {
                    fatal(&format!("the program's M3 numbers ({d}, {l}, {r}, {e}) are not {}'s (dev: LVM_M3_OVERRIDE=1)", self.p.name));
                }
                eprintln!(
                    "lvm: the program's M3 numbers ({d}, {l}, {r}, {e}) replace {}'s ({}, {}, {}, {})",
                    self.p.name, self.p.bus_depth, self.p.leafdec_reads, self.p.table_rounds, self.p.table_evals
                );
            }
            // A23: PUB is the record's sumcheck table, Φ's columns fit 2^dk (header-independent: the zero build's)
            if !z.is_empty() && acc::hdr_tab(&z) != Some(self.p.pub_tab) {
                match (acc::hdr_tab(&z), std::env::var_os("LVM_M3_OVERRIDE")) {
                    (Some(t), Some(_)) => {
                        eprintln!("lvm: the program's pubTab {t} replaces {}'s {}", self.p.name, self.p.pub_tab);
                        self.p = Params { pub_tab: t, ..self.p.clone() };
                    }
                    _ => fatal(&format!("the header array is sumcheck table {:?}, not {}'s pubTab {}", acc::hdr_tab(&z), self.p.name, self.p.pub_tab)),
                }
            }
            self.p = Params { bus_depth: d, leafdec_reads: l, table_rounds: r, table_evals: e, ..self.p.clone() };
            let cols = acc::fix_cols(&z, self.p.pub_tab);
            if cols.len() > 1 << self.p.acc_log() {
                fatal(&format!("Φ has {} columns > 2^{} (accVars − tableRounds)", cols.len(), self.p.acc_log()));
            }
            // Φ̃(0) = Φ(0) = F_0(0)
            self.phi0 = cols.first().map_or(crate::lv::primitives::field::F192::ZERO, |c| c[0].into());
            if self.log {
                eprintln!("lvm: Φ: {} fixed columns, {} cells, D = {}, dk = {}", cols.len(), cols.iter().map(|c| c.len()).sum::<usize>(), self.p.acc_d(), self.p.acc_log());
            }
        }
        self
    }

    /// The tables of a program without an M3 section (WP-15b's stream programs: inputs = the stream lanes).
    fn attach(&self, mut rec: RecWitness) -> RecWitness {
        if let Some((c, None)) = &self.q {
            rec.tables = crate::lvm::m3::stream_program_tables(c, self.p.rec_rows_log, &rec.msg);
        }
        rec
    }

    /// The tables of the program's M3 section: the input cells from the arrays (aliased: `col(rec, off, len)`
    /// of the commitments; public: `pub_lanes`), the BITS outputs by a fixpoint (run, set every output cell
    /// to its word function, until nothing changes: the program defines each word before it reads the
    /// word's outputs, so this ends after the BITS dependency depth + 1 runs), then WP-9's tables.
    pub fn build_tables(&self, col: &dyn Fn(bool, usize, usize) -> Vec<F64>, pub_lanes: &[u64]) -> Vec<crate::lvm::m3::TableW> {
        build_q_tables(&self.q, col, pub_lanes)
    }

    /// The builder `prove` calls (M3 section present): aliased columns from the commitments, public lanes from
    /// the header and its statement.
    fn builder(&self) -> Option<impl Fn(&Header, &crate::lvm::prove::Col) -> Vec<crate::lvm::m3::TableW> + Sync + '_> {
        matches!(&self.q, Some((_, Some(_)))).then_some(move |hd: &Header, col: &crate::lvm::prove::Col| {
            self.build_tables(col, &crate::lvm::m3::pub_lanes(&hd.bytes(), &stmt_of(hd)))
        })
    }

    fn sign(&self, pi: Vec<u8>, tr: crate::oracle::Trace) -> Signed {
        let t = Instant::now();
        let sig = crate::proc::sign_checked(self.svc, &tr);
        if !format::sig_ok(&self.vk, &format::trace_digest(&tr), &sig) {
            fatal("SIGN: SigOk fails on the returned signature");
        }
        if self.log {
            eprintln!("lvm: SIGN {} queries in {:.3} s (idx {})", tr.len(), t.elapsed().as_secs_f64(), sig.idx);
        }
        Signed { pi, tr, sig }
    }

    /// One `S` proof, signed; checks its own statement against `want`.
    fn s_proof(&self, hd: Header, rec: RecWitness, want: Option<&Digest>) -> (Signed, Digest, Acc) {
        let t = Instant::now();
        let b = self.builder();
        let sp = prove(&self.p, hd.clone(), rec, b.as_ref().map(|f| f as &crate::lvm::prove::Build));
        let sp_stages = sp.stages.clone();
        let mut hd = hd;
        hd.h = sp.h;
        let c = stmt_of(&hd);
        if let Some(w) = want {
            assert_eq!(&c, w, "the proof's statement");
        }
        if self.log {
            let st: Vec<String> = sp_stages.iter().map(|(k, v)| format!("{k} {v:.2}")).collect();
            eprintln!("lvm: S,{} n={} proved in {:.3} s [{}]", hd.b, hd.n, t.elapsed().as_secs_f64(), st.join(", "));
        }
        let acc_out = sp.acc_out.clone();
        let signed = self.sign(sp.proof, sp.trace);
        // the replay a later step does on this file gives the prover's own accumulator
        assert_eq!(acc::acc_out_of(&self.p, &signed.pi, &signed.tr), acc_out, "accOutOf replays the proof's fold");
        (signed, c, acc_out)
    }

    /// `acc_in` of an `S,1` proof over `child`: `accOutOf` of the child's stream (A23).
    fn acc_of_child(&self, child: &Signed) -> Acc {
        acc::acc_out_of(&self.p, &child.pi, &child.tr)
    }

    /// `σ_leaf`: the signature of the empty trace (`traceDigest []` is a constant, A2).
    pub fn sig_leaf(&self) -> Sig {
        self.sign(Vec::new(), Vec::new()).sig
    }

    /// Step 1: `nodeStmt (leafStmt hA nA) (leafStmt hB nB)`.
    pub fn first(&self, (na, sa): (u64, Digest), (nb, sb): (u64, Digest)) -> Signed {
        let sig_leaf = self.sig_leaf();
        let ha = Header { b: 0, vk: self.vk, c_l: [0; 32], s: sa, n: na, h: [0; 32], sig_leaf: None, acc_in: Acc::zero(self.p.acc_d(), self.phi0) };
        let (a, ca, _) = self.s_proof(ha, self.attach(RecWitness::zero(&self.p)), None);
        if let Ok(path) = std::env::var("LVM_SAVE_CHILD") {
            std::fs::write(&path, format::to_file(&a)).expect("LVM_SAVE_CHILD");
        }
        let hb = Header { b: 1, vk: self.vk, c_l: ca, s: sb, n: nb, h: [0; 32], sig_leaf: Some(sig_leaf), acc_in: self.acc_of_child(&a) };
        let rec = self.attach(RecWitness::from_child(&self.p, &a));
        self.s_proof(hb, rec, None).0
    }

    /// Step i ≥ 2: `nodeStmt prev (leafStmt h n)`.
    pub fn step(&self, prev_stmt: &Digest, prev: &Signed, (n, s): (u64, Digest)) -> Signed {
        let ph = header_of(&self.p, &prev.pi);
        if &stmt_of(&ph) != prev_stmt {
            fatal("prev.bin does not prove prev.stmt");
        }
        let sig_leaf = if ph.b == 1 { ph.sig_leaf.clone().unwrap() } else { self.sig_leaf() };
        let hd = Header { b: 1, vk: self.vk, c_l: *prev_stmt, s, n, h: [0; 32], sig_leaf: Some(sig_leaf), acc_in: self.acc_of_child(prev) };
        let rec = self.attach(RecWitness::from_child(&self.p, prev));
        self.s_proof(hd, rec, None).0
    }
}

/// [`Ctx::build_tables`] on a program alone (no service: the `tbench` dev command times it).
pub fn build_q_tables(
    q: &Option<(crate::lvm::loopir::Compiled, Option<crate::lvm::loopir::M3Spec>)>,
    col: &dyn Fn(bool, usize, usize) -> Vec<F64>,
    pub_lanes: &[u64],
) -> Vec<crate::lvm::m3::TableW> {
    use crate::lv::primitives::field::F192;
    use crate::lvm::loopir::{ArrKind, Ty};
    let Some((c, Some(spec))) = q else { return Vec::new() };
    let lanes: Vec<u64> = pub_lanes.iter().chain(&spec.pubx).copied().collect();
    let pub_lanes = &lanes[..];
    let mut in_k = vec![F64::ZERO; c.q.n_in[0]];
    let mut in_e = vec![F192::ZERO; c.q.n_in[1]];
    for a in &spec.arrs {
        let n = 1usize << a.tau;
        let cols: Vec<Vec<F64>> = match a.kind {
            ArrKind::Aliased => a.val.iter().map(|&(r, o)| col(r, o, n)).collect(),
            ArrKind::Public => vec![(0..n).map(|x| F64(a.sel.get(x).and_then(|&i| pub_lanes.get(i).copied()).unwrap_or(0))).collect()],
            ArrKind::Written => continue,
        };
        for x in 0..n {
            match a.ty {
                Ty::K => in_k[a.base + a.stride * x] = cols[0][x],
                Ty::E => in_e[a.base + a.stride * x] = F192::new(cols[0][x].0, cols[1][x].0, cols[2][x].0),
            }
        }
    }
    // every BITS output cell is a K input cell outside the aliased/public arrays, written once
    let mut owner = vec![0u8; c.q.n_in[0]];
    for a in spec.arrs.iter().filter(|a| a.ty == Ty::K && a.kind != ArrKind::Written) {
        for x in 0..1usize << a.tau {
            owner[a.base + a.stride * x] = 1;
        }
    }
    for b in &spec.bits {
        for o in &b.oc {
            for &e in o {
                assert!(e < c.q.n_in[0], "a BITS output is a K input cell ({e})");
                assert!(owner[e] != 1, "a BITS output cell lies in an aliased or public array ({e})");
                assert!(owner[e] != 2, "two BITS outputs write cell {e}");
                owner[e] = 2;
            }
        }
    }
    let mut runs = 0;
    let run = loop {
        let run = crate::lv::tracing::info_span!("B interp").in_scope(|| c.interp(&in_k, &in_e));
        runs += 1;
        let mut changed = false;
        for (bi, b) in spec.bits.iter().enumerate() {
            for x in 0..b.n {
                let w = match spec.free.iter().find(|f| f.0 == bi) {
                    // the WOTS checksum of the digest's 32 bytes (4 digits per byte, low bits first)
                    Some(&(_, 0, cell)) => crate::lvm::m3::free_checksum(&in_k[cell..cell + 4]),
                    Some(&(_, k, _)) => panic!("LoopIR blob: free word kind {k}"),
                    None => run.kc[b.wc[x]].0,
                };
                for (j, o) in b.outs.iter().enumerate() {
                    let e = b.oc[j][x];
                    let v = F64(o.word(w));
                    if in_k[e] != v {
                        in_k[e] = v;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break run;
        }
        assert!(runs < 64, "the BITS outputs settle");
    };
    if !run.ok || !run.inb {
        if std::env::var_os("LVM_QDEBUG").is_some() { eprintln!("lvm qdebug: ---- end of run"); }
        if let Some(path) = std::env::var_os("LVM_QDEBUG_DUMP") {
            let b: Vec<u8> = in_k.iter().flat_map(|v| v.0.to_le_bytes()).collect();
            let _ = std::fs::write(path, b);
        }
        eprintln!("lvm: the node program's run on these inputs: ok {} inb {} (dev: LVM_QDEBUG=1 lists the rows)", run.ok, run.inb);
    }
    crate::lv::tracing::info_span!("B spec_tables").in_scope(|| crate::lvm::m3::spec_tables(c, &run, spec, col, pub_lanes, pub_lanes.len() - spec.pubx.len()))
}

/// `first`/`step` inputs from `/work`.
pub fn run(ctx: &Ctx, mode: &str, dir: &str) -> Vec<u8> {
    let chain = |name: &str| crate::proc::read_chain(&std::path::Path::new(dir).join(name));
    let out = match mode {
        "first" => ctx.first(chain("chainA.json"), chain("chainB.json")),
        "step" => {
            let prev_stmt = unhex(&String::from_utf8_lossy(&read(dir, "prev.stmt")));
            let prev = format::from_file(&read(dir, "prev.bin")).unwrap_or_else(|| fatal("prev.bin is not a signed file"));
            ctx.step(&prev_stmt, &prev, chain("chain.json"))
        }
        _ => unreachable!(),
    };
    let file = format::to_file(&out);
    assert_eq!(format::from_file(&file).as_ref(), Some(&out), "the file parses back");
    file
}
