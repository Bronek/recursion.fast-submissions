//! `lvm-prover`: the native prover of the `leanvm-inspired` entry (BLUEPRINT §8; WP-4 skeleton).
//!
//! The submitted program is several builds of this crate, one per CPU variant (`build-asm.sh`), each with its
//! symbols suffixed, behind a `cpuid` stub (`dispatch.s`) that calls the variant's `lvm_main_<v>(argc, argv)`.
//!
//! Modes:
//!   lvm-prover info                       the variant and its run-time choices
//!   lvm-prover kat [keccak|field|oracle|all]  known-answer tests of this variant's kernels
//!   lvm-prover batch --log-n N [--local] [--sign] [--seed S] [--out FILE]
//!                                         WP-4: leanVM's Keccak batch proof on the oracle (`$RF_ORACLE`, or
//!                                         an in-process keyed hash with `--local`), with the report
//!   lvm-prover setup DIR                  nothing to set up (exit 0)
//!   lvm-prover first DIR | step DIR       the stream (PROVER.md §3): handshake only until WP-15
//! Environment: LEANVM_NUM_THREADS (default: every CPU), LVM_PROF=1 (span times), LVM_MEMLOG=1,
//! LVM_ALLOC=system, LVM_CLMUL / LVM_PCLMUL (portable K product tier, `kat`).
#![no_main]
#![allow(clippy::needless_range_loop, clippy::too_many_arguments, dead_code)]

mod alloc;
mod batch;
mod chainwalk;
mod format;
mod kat;
mod keccak;
mod keccak_vl;
mod lv;
mod lvm;
mod oracle;
mod proc;
mod service;

use keccak::Digest;
use std::ffi::{CStr, c_char, c_int};
use std::io::Write;
use std::time::Instant;

#[global_allocator]
static ALLOC: alloc::Cache = alloc::Cache;

/// The CPU variant this build is (`build-asm.sh` sets `LVM_VARIANT` at compile time).
pub const VARIANT: &str = match option_env!("LVM_VARIANT") {
    Some(v) => v,
    None => "native-build",
};

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

fn unhex(s: &str) -> Digest {
    let s = s.trim();
    assert_eq!(s.len(), 64, "a digest is 64 hex characters");
    std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex"))
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Peak resident set (`VmHWM`), MiB.
pub fn peak_rss_mb() -> f64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines()
        .find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l[6..].trim().trim_end_matches("kB").trim().parse::<f64>().ok())
        .map_or(0.0, |kb| kb / 1024.0)
}

/// One line on stdout, flushed (`ready`, `done`).
fn say(word: &str) {
    let mut o = std::io::stdout().lock();
    let _ = writeln!(o, "{word}");
    let _ = o.flush();
}

/// Block until the runner writes `go` on stdin.
fn wait_go() {
    let mut line = String::new();
    loop {
        line.clear();
        match std::io::stdin().read_line(&mut line) {
            Ok(0) => service::fatal("stdin closed before `go`"),
            Ok(_) if line.trim() == "go" => return,
            Ok(_) => {}
            Err(e) => service::fatal(&format!("stdin: {e}")),
        }
    }
}

fn cmd_batch(args: &[String]) {
    let log_n: usize = arg(args, "--log-n").map_or(10, |v| v.parse().expect("--log-n"));
    let seed: u64 = arg(args, "--seed").map_or(1, |v| v.parse().expect("--seed"));
    let local = args.iter().any(|a| a == "--local");
    let sign = args.iter().any(|a| a == "--sign");
    let t_start = Instant::now();
    let (vk, svc): (Digest, Option<&'static service::Service>) = if local {
        oracle::install(Box::new(oracle::Local::keyed(&[0x5A; 32])));
        ([0u8; 32], None)
    } else {
        let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set (or use --local)"));
        let s = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
        s.warm(lv::parallel::num_threads().min(service::MAX_CONNS));
        let vk = s.vk();
        let s: &'static service::Service = Box::leak(Box::new(s));
        oracle::install(Box::new(Shared(s)));
        (vk, Some(s))
    };
    lv::parallel::init();
    eprintln!("{}", kat::info());
    oracle::reset_stats();
    let t0 = Instant::now();
    let rep = batch::prove(log_n, seed, &vk);
    let prove_s = t0.elapsed().as_secs_f64();
    let c = &rep.config;
    println!("batch log_n={} mu={} prove_s={prove_s:.3} peak_rss_mib={:.0}", rep.log_n, rep.mu, peak_rss_mb());
    println!(
        "  whir: rates {:?} folds {}+{:?} queries {:?} caps {:?} ood {:?} grind {:?}",
        c.log_inv_rates, c.initial_k, c.level_ks, c.queries, c.cap_logs, c.ood_samples, c.grinding_bits
    );
    for (name, s) in &rep.stages {
        println!("  stage {name:<14} {s:>9.3} s");
    }
    print!("{}", lv::tracing::report());
    let classes = |pred: &dyn Fn(usize) -> bool| rep.trace.iter().filter(|(q, _)| pred(q.len())).count();
    println!(
        "  proof_bytes={} qS={} (fs {} incl. seed 2, leaf {}, node {}) trace_bytes={} fs_round_trips={}",
        rep.proof.len(),
        rep.trace.len(),
        classes(&|l| l != 64 && l != 384 && l != 512),
        classes(&|l| l == 384 || l == 512),
        classes(&|l| l == 64),
        rep.trace_bytes(),
        rep.fs_queries
    );
    print!("{}", oracle::report());
    if let Some(out) = arg(args, "--out") {
        std::fs::write(&out, &rep.proof).unwrap_or_else(|e| service::fatal(&format!("{out}: {e}")));
    }
    if sign {
        let svc = svc.unwrap_or_else(|| service::fatal("--sign needs the service"));
        let t = Instant::now();
        let qs: Vec<&[u8]> = rep.trace.iter().map(|(q, _)| q.as_slice()).collect();
        let (answers, sig) = svc.sign(&qs);
        let ok_answers = answers.iter().zip(&rep.trace).all(|(a, (_, b))| a == b);
        let digest = format::trace_digest(&rep.trace);
        let ok_sig = format::sig_ok(&vk, &digest, &sig);
        println!(
            "  sign: {} items, answers {} , SigOk {} , {:.3} s (idx {})",
            qs.len(),
            if ok_answers { "match" } else { "DIFFER" },
            ok_sig,
            t.elapsed().as_secs_f64(),
            sig.idx
        );
        assert!(ok_answers && ok_sig, "the signed trace");
    }
    if let Some(s) = svc {
        println!("  service: {}", s.report());
    }
    println!("  total_s={:.3}", t_start.elapsed().as_secs_f64());
}

/// The service behind the `'static` handle the oracle needs.
struct Shared(&'static service::Service);
impl oracle::Oracle for Shared {
    fn ask(&self, q: &[u8]) -> Digest {
        oracle::Oracle::ask(self.0, q)
    }
    fn ask_many_here(&self, out: &mut [Digest], build: &oracle::Builder) {
        oracle::Oracle::ask_many_here(self.0, out, build)
    }
    fn ask_rows_here(&self, out: &mut [Digest], rows: &[u8], row_bytes: usize, pad: usize) {
        oracle::Oracle::ask_rows_here(self.0, out, rows, row_bytes, pad)
    }
}

/// `sprove --params P8|P20 [--local] [--n N] [--seed S] [--b 0|1] [--out FILE] [--trace FILE] [--sign FILE]`: one
/// `S` proof with the recursion part zero; `--sign` writes the signed file (FORMAT.md).
/// WP-15b checks: the recursion witness, the LoopIR filler.
fn cmd_rqtest(args: &[String]) {
    lvm::rec::check::padding_matches_keccak256();
    lvm::rec::check::wots_rows_reach_the_key();
    println!("rqtest rec: ok");
    {
        use lvm::bits::*;
        let words: Vec<u64> = (0..1000u64).map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 40)).collect();
        let t = BitsTable::fill(10, &words);
        let outs = [BOut::Shl(8), BOut::Shr(56), BOut::Shl(24), BOut::Shr(40), BOut::Bit(0), BOut::Bit(63)];
        assert!(t.check(&outs), "BITS rows");
        println!("rqtest bits: ok");
    }
    // rqtest BLOB INPUTS OUT: run a LoopIR program (blob) on inputs (u64 LE: nK, K words, nE, 3·nE limbs), dump
    // its tables and messages for the Lean check
    if let (Some(blob), Some(inp), Some(out)) = (args.get(2), args.get(3), args.get(4)) {
        use lvm::loopir::*;
        let t = Instant::now();
        let c = Compiled::new(Program::parse(&std::fs::read_to_string(blob).expect("blob")));
        let b = std::fs::read(inp).expect("inputs");
        let w: Vec<u64> = b.chunks(8).map(|x| u64::from_le_bytes(x.try_into().unwrap())).collect();
        let nk = w[0] as usize;
        let in_k: Vec<lv::primitives::field::F64> = w[1..1 + nk].iter().map(|&x| lv::primitives::field::F64(x)).collect();
        let ne = w[1 + nk] as usize;
        let in_e: Vec<lv::primitives::field::F192> =
            (0..ne).map(|i| lv::primitives::field::F192::new(w[2 + nk + 3 * i], w[3 + nk + 3 * i], w[4 + nk + 3 * i])).collect();
        let t_c = t.elapsed().as_secs_f64();
        let run = c.interp(&in_k, &in_e);
        let t_i = t.elapsed().as_secs_f64();
        let tb = c.tables(&run);
        let t_t = t.elapsed().as_secs_f64();
        let msgs = c.messages(&run, &tb);
        println!(
            "rqtest loopir: blocks {} pieces {} cells K {} E {} ok {} inb {} committed words {} messages {} balanced {} (compile {:.3} s, interp {:.3} s, tables {:.3} s)",
            c.q.blocks.len(), c.pieces.len(), c.cells[0], c.cells[1], run.ok, run.inb, c.committed_words(), msgs.len(),
            balanced(&msgs), t_c, t_i - t_c, t_t - t_i
        );
        std::fs::write(out, dump(&c, &run, &tb, &msgs)).expect("out");
        let tabs = lvm::m3::loop_tables(&c, &tb, &in_k, &in_e);
        let hold = tabs.iter().all(|t| t.constraints_hold());
        oracle::install(Box::new(oracle::Local::keyed(&[0x5A; 32])));
        let mut ps = lv::fiat_shamir::transcript::ProverState::seeded(&vec![0u8; lvm::params::HEADER_BASE]);
        let t0 = Instant::now();
        let mo = lvm::m3::prove(&mut ps, &tabs);
        let _ = ps.sample(); // flush the last evaluations into an FS query
        println!(
            "rqtest m3: tables {} constraints hold {hold}; bus depth {} table rounds {} table evals {}; {} scalars, {} queries ({:.3} s)",
            tabs.len(), mo.bus_depth, mo.table_rounds, mo.table_evals, ps.body.len() / 24, ps.trace.len(), t0.elapsed().as_secs_f64()
        );
        if let Some(tr) = args.get(5) {
            let mut v = Vec::new();
            for (q, a) in &ps.trace {
                v.extend_from_slice(&(q.len() as u64).to_le_bytes());
                v.extend_from_slice(q);
                v.extend_from_slice(a);
            }
            std::fs::write(tr, &v).expect("trace out");
        }
    }
}

/// P-GATE: `pgbench commit NU REPS [--local]`: commit a pseudo-random `2^NU`-word vector at `C_main`'s level-0
/// rate and cap (P20), on the service (`RF_ORACLE`) unless `--local`; prints the wall time per rep.
fn cmd_pgbench(args: &[String]) {
    let p = lvm::params::Params::by_name("P20").unwrap();
    let nu: usize = args.get(3).map_or(26, |v| v.parse().expect("NU"));
    let reps: usize = args.get(4).map_or(3, |v| v.parse().expect("REPS"));
    if args.iter().any(|a| a == "--local") {
        oracle::install(Box::new(oracle::Local::keyed(&[0x5A; 32])));
    } else {
        let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set (or use --local)"));
        let s = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
        s.warm(lv::parallel::num_threads().min(service::MAX_CONNS));
        let s: &'static service::Service = Box::leak(Box::new(s));
        oracle::install(Box::new(Shared(s)));
    }
    lv::parallel::init();
    let m0 = p.main_levels[0];
    let msg: Vec<lv::primitives::field::F64> =
        (0..1u64 << nu).map(|x| lv::primitives::field::F64(x.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (x << 29))).collect();
    for r in 0..reps {
        oracle::reset_stats();
        let t = Instant::now();
        let (c, d) = lv::pcs::whir::commit(&msg, nu, lv::pcs::whir::INITIAL_FOLDING_FACTOR, m0.rate, m0.cap);
        let s = t.elapsed().as_secs_f64();
        println!("pgbench commit nu={nu} rep={r} wall_s={s:.3} cap0={:02x}", c.cap[0][0]);
        drop(d);
    }
}

fn cmd_sprove(args: &[String]) {
    let p = lvm::params::Params::by_name(&arg(args, "--params").unwrap_or_else(|| "P8".into()))
        .unwrap_or_else(|| service::fatal("--params P8|P20"));
    let n: u64 = arg(args, "--n").map_or(1 << p.log_n, |v| v.parse().expect("--n"));
    let seed: u64 = arg(args, "--seed").map_or(1, |v| v.parse().expect("--seed"));
    let local = args.iter().any(|a| a == "--local");
    let t_start = Instant::now();
    let (vk, svc): (Digest, Option<&'static service::Service>) = if local {
        oracle::install(Box::new(oracle::Local::keyed(&[0x5A; 32])));
        ([0u8; 32], None)
    } else {
        let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set (or use --local)"));
        let s = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
        s.warm(lv::parallel::num_threads().min(service::MAX_CONNS));
        let vk = s.vk();
        let s: &'static service::Service = Box::leak(Box::new(s));
        oracle::install(Box::new(Shared(s)));
        (vk, Some(s))
    };
    lv::parallel::init();
    eprintln!("{}", kat::info());
    let mut s = [0u8; 32];
    s[..8].copy_from_slice(&seed.to_le_bytes());
    let hd = lvm::prove::Header { b: 0, vk, c_l: [0; 32], s, n, h: [0; 32], sig_leaf: None, acc_in: lvm::acc::Acc::zero(p.acc_d(), lv::primitives::field::F192::ZERO) };
    let mut rec = lvm::prove::RecWitness::zero(&p);
    // --loop BLOB INPUTS: attach a LoopIR program's tables (the real bus and table sumcheck; dev test)
    if let Some(i) = args.iter().position(|a| a == "--loop") {
        use lvm::loopir::*;
        let c = Compiled::new(Program::parse(&std::fs::read_to_string(&args[i + 1]).expect("blob")));
        let w: Vec<u64> = std::fs::read(&args[i + 2]).expect("inputs").chunks(8).map(|x| u64::from_le_bytes(x.try_into().unwrap())).collect();
        let nk = w[0] as usize;
        let in_k: Vec<lv::primitives::field::F64> = w[1..1 + nk].iter().map(|&x| lv::primitives::field::F64(x)).collect();
        let ne = w[1 + nk] as usize;
        let in_e: Vec<lv::primitives::field::F192> =
            (0..ne).map(|i| lv::primitives::field::F192::new(w[2 + nk + 3 * i], w[3 + nk + 3 * i], w[4 + nk + 3 * i])).collect();
        let run = c.interp(&in_k, &in_e);
        let tb = c.tables(&run);
        rec.tables = lvm::m3::loop_tables(&c, &tb, &in_k, &in_e);
        let (d, l, r, e) = lvm::m3::shape(&rec.tables);
        println!("loop: {} tables, {} committed words, bus depth {d} leafdec {l} table rounds {r} table evals {e}", rec.tables.len(), lvm::m3::committed_words(&rec.tables));
    }
    // --synth BIG SMALL: a synthetic program of the real Q's size on the zero stream (dev benchmark)
    if let Some(i) = args.iter().position(|a| a == "--synth") {
        use lvm::loopir::*;
        let t = Instant::now();
        let n_in = 17usize << p.rec_rows_log;
        let c = Compiled::new(synthetic(n_in, args[i + 1].parse().unwrap(), args[i + 2].parse().unwrap()));
        let in_k: Vec<lv::primitives::field::F64> = (0..n_in).map(|x| lv::primitives::field::F64((x as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)).collect();
        let run = c.interp(&in_k, &[]);
        let tb = c.tables(&run);
        rec.tables = lvm::m3::loop_tables(&c, &tb, &in_k, &[]);
        let (d, l, r, e) = lvm::m3::shape(&rec.tables);
        println!(
            "synth: {} pieces, {} rows, {} tables, {} committed words, bus depth {d} leafdec {l} table rounds {r} table evals {e}; witness {:.3} s",
            c.pieces.len(), c.pieces.iter().map(|p| 1usize << c.height(p)).sum::<usize>(), rec.tables.len(),
            lvm::m3::committed_words(&rec.tables), t.elapsed().as_secs_f64()
        );
    }
    // P-FIX dev: `--build-emu` (with `--synth`): the stream's order, where `prove` builds the recursion tables
    // beside the chain walk (lever 3) once `h` is known. The build is emulated by the shipped node program's
    // table build on zero inputs (its cost), whose tables are dropped; the synthetic tables are the result.
    let emu = args.iter().any(|a| a == "--build-emu") && !rec.tables.is_empty();
    let (p, synth_tabs) = if emu {
        let mut v = std::mem::take(&mut rec.tables);
        v.retain(lvm::m3::active);
        let (d, l, r, e) = lvm::m3::shape(&v);
        (lvm::params::Params { bus_depth: d, leafdec_reads: l, table_rounds: r, table_evals: e, ..p.clone() }, v)
    } else {
        (p.clone(), Vec::new())
    };
    let q_emu = emu.then(|| {
        let (q, spec) = lvm::loopir::parse_blob(if p.name == "P20" { lvm::stream::Q_P20 } else { lvm::stream::Q_P8 });
        Some((lvm::loopir::Compiled::new(q), spec))
    }).flatten();
    let pl = vec![0u64; lvm::m3::pub_lanes_len(&p)];
    if emu {
        // the stream's zero build before `ready` (untimed), on the same program
        drop(lvm::stream::build_q_tables(&q_emu, &|_, _, n| vec![lv::primitives::field::F64::ZERO; n], &pl));
    }
    let emu_build = |_hd: &lvm::prove::Header, _col: &lvm::prove::Col| -> Vec<lvm::m3::TableW> {
        let t = Instant::now();
        let z = lvm::stream::build_q_tables(&q_emu, &|_, _, n| vec![lv::primitives::field::F64::ZERO; n], &pl);
        if std::env::var_os("LVM_LOG").is_some() {
            eprintln!("lvm: build-emu {} tables in {:.3} s", z.len(), t.elapsed().as_secs_f64());
        }
        drop(z);
        synth_tabs.clone()
    };
    oracle::reset_stats();
    let t0 = Instant::now();
    let sp = lvm::prove::prove(&p, hd, rec, if emu { Some(&emu_build as &lvm::prove::Build) } else { None });
    let prove_s = t0.elapsed().as_secs_f64();
    println!(
        "sprove {} n={n} prove_s={prove_s:.3} peak_rss_mib={:.0} proof_bytes={} qS={} h={}",
        p.name,
        peak_rss_mb(),
        sp.proof.len(),
        sp.trace.len(),
        hex(&sp.h)
    );
    for (name, s) in &sp.stages {
        println!("  stage {name:<14} {s:>9.3} s");
    }
    if p.grind > 0 {
        let g = oracle::stat(oracle::Class::Grind);
        println!(
            "  grind g={} attempts per level (rec; main) {:?} total {} queried {} wall_ms {:.1}",
            p.grind,
            sp.grind_attempts,
            sp.grind_attempts.iter().sum::<u64>(),
            g.queries,
            oracle::grind_wall_s() * 1e3
        );
    }
    print!("{}", lv::tracing::report());
    print!("{}", oracle::report());
    if let Some(out) = arg(args, "--out") {
        std::fs::write(&out, &sp.proof).unwrap_or_else(|e| service::fatal(&format!("{out}: {e}")));
    }
    if let Some(out) = arg(args, "--trace") {
        let mut v = Vec::new();
        for (q, a) in &sp.trace {
            v.extend_from_slice(&(q.len() as u64).to_le_bytes());
            v.extend_from_slice(q);
            v.extend_from_slice(a);
        }
        std::fs::write(&out, &v).unwrap_or_else(|e| service::fatal(&format!("{out}: {e}")));
    }
    if let Some(out) = arg(args, "--sign") {
        let svc = svc.unwrap_or_else(|| service::fatal("--sign needs the service"));
        let t = Instant::now();
        let qs: Vec<&[u8]> = sp.trace.iter().map(|(q, _)| q.as_slice()).collect();
        let (answers, sig) = svc.sign(&qs);
        let ok_answers = answers.iter().zip(&sp.trace).all(|(a, (_, b))| a == b);
        let ok_sig = format::sig_ok(&vk, &format::trace_digest(&sp.trace), &sig);
        println!("  sign: answers {} SigOk {ok_sig} {:.3} s (idx {})", if ok_answers { "match" } else { "DIFFER" }, t.elapsed().as_secs_f64(), sig.idx);
        assert!(ok_answers && ok_sig);
        let file = format::to_file(&format::Signed { pi: sp.proof.clone(), tr: sp.trace.clone(), sig });
        std::fs::write(&out, &file).unwrap_or_else(|e| service::fatal(&format!("{out}: {e}")));
        let back = format::from_file(&file).expect("the file parses");
        assert_eq!(back.pi, sp.proof);
    }
    if let Some(s) = svc {
        println!("  service: {}", s.report());
    }
    println!("  total_s={:.3}", t_start.elapsed().as_secs_f64());
}

/// `selftest` (a child of `setup`, one variant forced by `LVM_CPU`): the KATs, then a Keccak batch proof (2^9)
/// and an `S` proof at `P8` on the in-process keyed oracle; prints `selftest <variant> <digest>`, the Keccak-256 of
/// both proofs, which every correct variant gives (the proofs are byte-identical across variants).
fn cmd_selftest() {
    kat::keccak();
    kat::field();
    kat::oracle();
    oracle::install(Box::new(oracle::Local::keyed(&[0x5A; 32])));
    lv::parallel::init();
    let b = batch::prove(9, 7, &[0u8; 32]);
    let p = lvm::params::p8();
    let mut s = [0u8; 32];
    s[0] = 7;
    let hd = lvm::prove::Header { b: 0, vk: [0; 32], c_l: [0; 32], s, n: 300, h: [0; 32], sig_leaf: None, acc_in: lvm::acc::Acc::zero(p.acc_d(), lv::primitives::field::F192::ZERO) };
    let sp = lvm::prove::prove(&p, hd, lvm::prove::RecWitness::zero(&p), None);
    let mut h = keccak::Keccak256::new();
    h.update(&b.proof).update(&sp.proof);
    for (q, a) in &sp.trace {
        h.update(q).update(a);
    }
    println!("selftest {VARIANT} {}", hex(&h.finalize()));
}

/// `setup DIR` (PROVER.md §3, untimed, `setup_s` = 240 s): the CPU self-test. Each variant runs `selftest` in a
/// child process (`LVM_CPU` forced, 4 threads, a deadline): v2 first, the reference; then v4, then v4p. The
/// fastest variant whose child exits 0 with v2's digest is kept: when it is not v4, `DIR/lvm-cpu` names the cap
/// (`v4p` or `v2`), which `dispatch.s` reads at every start (`$RF_SETUP/lvm-cpu`). A variant the CPU lacks
/// raises SIGILL in its child only, which counts as a failure; `dispatch.s` never picks it anyway.
/// `LVM_SELFTEST_FAIL=v4[,v4p]` makes those children fail (a test of the fallback).
fn cmd_setup(dir: &str) -> i32 {
    let t0 = Instant::now();
    // P-FIX2: no worker count from an earlier setup survives this one (written below; absent: 8)
    let _ = std::fs::remove_file(format!("{dir}/lvm-threads"));
    let exe = std::env::current_exe().map(|p| p.to_string_lossy().into_owned()).unwrap_or_else(|_| "/prover/prover".into());
    let inject = std::env::var("LVM_SELFTEST_FAIL").unwrap_or_default();
    let budget = |v: &str| -> u64 {
        std::env::var(format!("LVM_SELFTEST_S_{v}")).ok().and_then(|x| x.parse().ok()).unwrap_or(match v {
            "v2" => 100,
            _ => 60,
        })
    };
    let run = |v: &str| -> Result<String, String> {
        if inject.split(',').any(|x| x == v) {
            return Err("failure injected (LVM_SELFTEST_FAIL)".into());
        }
        use std::os::unix::process::CommandExt;
        unsafe extern "C" {
            fn setrlimit(resource: i32, rlim: *const [u64; 2]) -> i32;
        }
        let mut cmd = std::process::Command::new(&exe);
        // SAFETY: async-signal-safe: one setrlimit (RLIMIT_CORE = 4) in the child before exec, so that a
        // crashing variant leaves no core file in the setup directory.
        unsafe {
            cmd.pre_exec(|| {
                setrlimit(4, &[0u64, 0u64]);
                Ok(())
            });
        }
        let mut child = cmd
            .arg("selftest")
            .env("LVM_CPU", v)
            .env("LEANVM_NUM_THREADS", "4")
            .env_remove("RF_SETUP")
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .map_err(|e| format!("spawn: {e}"))?;
        let deadline = Instant::now() + std::time::Duration::from_secs(budget(v));
        let status = loop {
            match child.try_wait() {
                Ok(Some(st)) => break st,
                Ok(None) if Instant::now() > deadline => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err("timeout".into());
                }
                Ok(None) => std::thread::sleep(std::time::Duration::from_millis(20)),
                Err(e) => return Err(format!("wait: {e}")),
            }
        };
        let mut out = String::new();
        use std::io::Read;
        if let Some(mut o) = child.stdout.take() {
            let _ = o.read_to_string(&mut out);
        }
        if !status.success() {
            return Err(format!("{status}"));
        }
        out.lines()
            .find_map(|l| l.strip_prefix("selftest ").map(|r| r.to_string()))
            .ok_or_else(|| "no selftest line".into())
    };
    let mut log = String::new();
    let reference = match run("v2") {
        Ok(r) => r,
        Err(e) => {
            // nothing to compare with: the portable variant is the only safe choice
            log += &format!("v2: FAIL ({e}); cap v2\n");
            let _ = std::fs::write(format!("{dir}/lvm-cpu"), "v2\n");
            let _ = std::fs::write(format!("{dir}/lvm-selftest.txt"), &log);
            eprintln!("{log}");
            return 0;
        }
    };
    let digest = |r: &str| r.split_whitespace().nth(1).unwrap_or("").to_string();
    log += &format!("v2: ok {}\n", digest(&reference));
    let mut chosen = "v2";
    for v in ["v4", "v4p"] {
        match run(v) {
            Ok(r) if digest(&r) == digest(&reference) => {
                log += &format!("{v}: ok ({r})\n");
                chosen = v;
                break;
            }
            Ok(r) => log += &format!("{v}: FAIL (digest differs: {r})\n"),
            Err(e) => log += &format!("{v}: FAIL ({e})\n"),
        }
    }
    let cap = format!("{dir}/lvm-cpu");
    if chosen == "v4" {
        let _ = std::fs::remove_file(&cap);
    } else if let Err(e) = std::fs::write(&cap, format!("{chosen}\n")) {
        eprintln!("setup: {cap}: {e}");
        return 1;
    }
    log += &format!("cap: {chosen} ({:.1} s)\n", t0.elapsed().as_secs_f64());
    // P-FIX2: the worker count of the steps, timed on the chosen variant (`DIR/lvm-threads`)
    let (k, msg) = if t0.elapsed().as_secs() < 180 {
        select_threads(&exe, chosen, t0 + std::time::Duration::from_secs(225))
    } else {
        (8, "threads 8 (no setup time left)".to_string())
    };
    if let Err(e) = std::fs::write(format!("{dir}/lvm-threads"), format!("{k}\n")) {
        eprintln!("setup: {dir}/lvm-threads: {e}");
    }
    log += &format!("{msg}\n");
    let _ = std::fs::write(format!("{dir}/lvm-selftest.txt"), &log);
    eprint!("{log}");
    0
}

/// P-FIX dev: `tbench P8|P20 REPS`: time the recursion-table build of the shipped node program on zero inputs
/// (the pre-`ready` zero build; `LVM_PROF=1` for its spans).
fn cmd_tbench(args: &[String]) {
    let p = lvm::params::Params::by_name(args.get(2).map_or("P20", |s| s.as_str())).expect("P8|P20");
    let reps: usize = args.get(3).map_or(3, |v| v.parse().expect("REPS"));
    lv::parallel::init();
    let t = Instant::now();
    let (q, spec) = lvm::loopir::parse_blob(if p.name == "P20" { lvm::stream::Q_P20 } else { lvm::stream::Q_P8 });
    let q = Some((lvm::loopir::Compiled::new(q), spec));
    println!("tbench parse+compile {:.3} s", t.elapsed().as_secs_f64());
    let pl = vec![0u64; lvm::m3::pub_lanes_len(&p)];
    if std::env::var_os("TB_ARRS").is_some() {
        if let Some((_, Some(spec))) = &q {
            for a in spec.arrs.iter().filter(|a| a.kind == lvm::loopir::ArrKind::Aliased) {
                for &(r, o) in &a.val {
                    println!("aliased {} {o} {}", if r { "rec" } else { "main" }, 1usize << a.tau);
                }
            }
        }
    }
    let mut last = 0;
    for r in 0..reps {
        let t = Instant::now();
        let tabs = lvm::stream::build_q_tables(&q, &|_, _, n| vec![lv::primitives::field::F64::ZERO; n], &pl);
        let el = t.elapsed().as_secs_f64();
        let mut hsh = 0xcbf2_9ce4_8422_2325u64;
        for tw in &tabs {
            for c in &tw.cols {
                for w in c {
                    hsh = (hsh ^ w.0).wrapping_mul(0x100_0000_01b3);
                }
                hsh = (hsh ^ c.len() as u64).wrapping_mul(0x100_0000_01b3);
            }
        }
        println!("tbench rep {r} build {el:.3} s ({} tables, digest {hsh:016x})", tabs.len());
        last = tabs.len();
    }
    let _ = last;
    print!("{}", lv::tracing::report());
}

/// P-FIX dev: `gbench N REPS`: the tape's output claim and depth-24 GKR alone at `n` (P20 shape, local oracle),
/// then the KS GKR (2^15 rows); `LVM_PROF=1` for the spans.
fn cmd_gbench(args: &[String]) {
    use lv::primitives::field::F64;
    let n: usize = args.get(2).map_or(1, |v| v.parse().expect("N"));
    let reps: usize = args.get(3).map_or(3, |v| v.parse().expect("REPS"));
    oracle::install(Box::new(oracle::Local::keyed(&[0x5A; 32])));
    lv::parallel::init();
    let p = lvm::params::Params::by_name("P20").unwrap();
    let chain = lvm::tables::Chain::run_gated(p.log_n, &[7u8; 32], n, false);
    let tape_reps = if std::env::var_os("GB_NOTAPE").is_some() { 0 } else { reps };
    for r in 0..tape_reps {
        let t = Instant::now();
        let w = lv::keccak_gkr::Witness::generate_uncommitted(chain.shape, &chain.inputs);
        let tw = t.elapsed().as_secs_f64();
        let mut ps = lv::fiat_shamir::transcript::ProverState::seeded(b"gbench-tape-0123");
        let t = Instant::now();
        let rr = ps.sample_vec(p.log_n);
        let out = lv::keccak_gkr::OutputClaim::of_inputs_padded(chain.shape, &chain.inputs, rr);
        let to = t.elapsed().as_secs_f64();
        ps.add_scalars(&out.lanes);
        let t = Instant::now();
        let _ = w.prove_tape(&mut ps, &out);
        let tg = t.elapsed().as_secs_f64();
        println!("gbench n={n} rep {r}: witness {tw:.3} out {to:.3} tape gkr {tg:.3} s");
    }
    if std::env::var_os("GB_NOKS").is_some() {
        print!("{}", lv::tracing::report());
        return;
    }
    // KS14-G: `GB_KSLOG=L` runs KS at 2^L rows (`rec_rows_log = L − 1`), the rest of P20 unchanged
    let kl: usize = std::env::var("GB_KSLOG").ok().and_then(|v| v.parse().ok()).unwrap_or(p.ks_log);
    let p = lvm::params::Params { ks_log: kl, rec_rows_log: kl - 1, ..p };
    let lay = lvm::tables::Layout::new(&p);
    let cont = lvm::tables::cont_column(p.ks_log, p.rec_rows_log, lvm::prove::sponge_blocks(&p).min(1 << p.rec_rows_log));
    let ks = lvm::tables::Sponge::run(p.ks_log, cont, vec![[0u64; lvm::params::REC_STREAM_COLS]; 1 << p.ks_log]);
    let mut cmain = vec![F64::ZERO; 1 << p.nu_main];
    let mut crec = vec![F64::ZERO; 1 << p.nu_rec()];
    for r in 0..reps {
        let ks_w = lvm::tables::write_ks(&lay, &ks, &mut cmain, &mut crec);
        let mut ps = lv::fiat_shamir::transcript::ProverState::seeded(b"gbench-ks-01234");
        let t = Instant::now();
        let rk = ps.sample_vec(p.ks_log);
        let kout = lv::keccak_gkr::OutputClaim::of_inputs(ks.shape, &ks.inputs, rk);
        let to = t.elapsed().as_secs_f64();
        ps.add_scalars(&kout.lanes);
        let t = Instant::now();
        let _ = ks_w.prove(&mut ps, &cmain[lay.ks_off..lay.ks_off + (1 << lay.ks_vars())], &kout);
        let tg = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let _ = lvm::link::prove_ks(&mut ps, &lay, &ks);
        println!("gbench KS 2^{kl} rep {r}: out {to:.3} gkr {tg:.3} link {:.3} s", t.elapsed().as_secs_f64());
    }
    print!("{}", lv::tracing::report());
}

/// P-FIX2: `tsel` (a child of the stream's start-up): the tape's depth-24 GKR at n = 2^14 rows on a local oracle,
/// the worker count from `LEANVM_NUM_THREADS`; prints `tsel <best of 3, s>`. The kernel phases' stand-in.
fn cmd_tsel() {
    oracle::install(Box::new(oracle::Local::keyed(&[0x5A; 32])));
    lv::parallel::init();
    let p = lvm::params::Params::by_name("P20").unwrap();
    let chain = lvm::tables::Chain::run_gated_notify_ref(p.log_n, &[7u8; 32], 1 << 14, false, |_| {});
    let w = lv::keccak_gkr::Witness::generate_uncommitted(chain.shape, &chain.inputs);
    let mut best = f64::MAX;
    let mut dig = String::new();
    for _ in 0..3 {
        let mut ps = lv::fiat_shamir::transcript::ProverState::seeded(b"tsel-tape-0123456");
        let t = Instant::now();
        let rr = ps.sample_vec(p.log_n);
        let out = lv::keccak_gkr::OutputClaim::of_inputs_padded(chain.shape, &chain.inputs, rr);
        ps.add_scalars(&out.lanes);
        let fin = w.prove_tape(&mut ps, &out);
        best = best.min(t.elapsed().as_secs_f64());
        dig = format!("{:?}", fin.value);
    }
    println!("tsel {best:.6} {}", hex(&keccak::keccak256(dig.as_bytes())));
}

/// `prover setup`'s worker count: 8, or 4 if `tsel` runs at least 3 % faster with 4. Each count is timed in its
/// own child process on the chosen CPU variant, alternately, three times each (best of each); fewer than 8 CPUs
/// or a failed child: 8. The proof bytes do not depend on the count (the field sums are exact).
fn select_threads(exe: &str, variant: &str, deadline: Instant) -> (usize, String) {
    let cpus = std::thread::available_parallelism().map_or(1, |n| n.get());
    if cpus < 8 {
        return (8, format!("threads 8 ({cpus} CPUs: not timed)"));
    }
    let t0 = Instant::now();
    let run = |k: usize| -> Option<(f64, String)> {
        let mut ch = std::process::Command::new(exe)
            .arg("tsel")
            .env("LVM_CPU", variant)
            .env("LEANVM_NUM_THREADS", k.to_string())
            .env_remove("RF_SETUP")
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .ok()?;
        let deadline = deadline.min(Instant::now() + std::time::Duration::from_secs(30));
        loop {
            match ch.try_wait() {
                Ok(Some(st)) if st.success() => break,
                Ok(None) if Instant::now() < deadline => std::thread::sleep(std::time::Duration::from_millis(5)),
                _ => {
                    let _ = ch.kill();
                    let _ = ch.wait();
                    return None;
                }
            }
        }
        let mut out = String::new();
        std::io::Read::read_to_string(ch.stdout.as_mut()?, &mut out).ok()?;
        let mut f = out.trim().strip_prefix("tsel ")?.split_whitespace();
        Some((f.next()?.parse().ok()?, f.next()?.to_string()))
    };
    let (mut t8, mut t4) = (f64::MAX, f64::MAX);
    let mut digest: Option<String> = None;
    for k in [8, 4, 4, 8, 8, 4] {
        match run(k) {
            // the claim the GKR ends at must not depend on the count
            Some((_, d)) if digest.as_ref().is_some_and(|x| *x != d) => return (8, format!("threads 8 (tsel's claim differs with {k})")),
            Some((t, d)) => {
                digest = Some(d);
                if k == 8 { t8 = t8.min(t) } else { t4 = t4.min(t) }
            }
            None => return (8, format!("threads 8 (tsel failed or out of time with {k})")),
        }
    }
    let k = if t4 < 0.97 * t8 { 4 } else { 8 };
    (k, format!("threads {k} (tsel: 8 {:.0} ms, 4 {:.0} ms; {:.1} s)", t8 * 1e3, t4 * 1e3, t0.elapsed().as_secs_f64()))
}

/// `first DIR` / `step DIR` (PROVER.md §3): connect, `ready`, wait for `go`, prove, write `proof.bin`, `done`.
/// Parameter set `P20` (`LVM_PARAMS=P8` for local tests), 8 threads unless `LEANVM_NUM_THREADS` says otherwise.
fn cmd_stream(mode: &str, dir: &str) {
    let t_start = Instant::now();
    let tsel = if std::env::var_os("LEANVM_NUM_THREADS").is_none() {
        // P-FIX2 (SYN2 §3.3 item 3): the worker count `prover setup` timed on this machine (`$RF_SETUP/lvm-threads`;
        // `LVM_TSEL=N` overrides), else 8
        let file = std::env::var("RF_SETUP").ok().and_then(|d| std::fs::read_to_string(format!("{d}/lvm-threads")).ok());
        let pick = |v: Option<String>| v.and_then(|x| x.trim().parse::<usize>().ok()).filter(|&k| (1..=64).contains(&k));
        let (k, from) = match (pick(std::env::var("LVM_TSEL").ok()), pick(file)) {
            (Some(k), _) => (k, "LVM_TSEL"),
            (None, Some(k)) => (k, "setup"),
            _ => (8, "default"),
        };
        // SAFETY: single-threaded here (no worker pool, no other thread yet).
        unsafe { std::env::set_var("LEANVM_NUM_THREADS", k.to_string()) };
        format!("threads {k} ({from})")
    } else {
        String::from("threads set by LEANVM_NUM_THREADS")
    };
    let p = lvm::params::Params::by_name(&std::env::var("LVM_PARAMS").unwrap_or_else(|_| "P20".into()))
        .unwrap_or_else(|| service::fatal("LVM_PARAMS: P8 | P20"));
    let _ = std::env::set_current_dir(dir);
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set"));
    let svc = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
    lv::parallel::init();
    svc.warm(lv::parallel::num_threads().min(service::MAX_CONNS));
    let vk = svc.vk();
    let svc: &'static service::Service = Box::leak(Box::new(svc));
    oracle::install(Box::new(Shared(svc)));
    let log = std::env::var_os("LVM_LOG").is_some();
    if let Ok(v) = std::fs::read_to_string(format!("{dir}/vk.hex")) {
        if unhex(&v) != vk {
            service::fatal("vk.hex differs from the service's VK");
        }
    }
    // FR's heap set-up before `ready` (untimed): the arena settings and pre-touch, and the large-block cache
    // pre-faulted to about the request's peak (`LVM_PREFAULT_MIB` overrides)
    let pf = std::env::var("LVM_PREFAULT_MIB").ok().and_then(|x| x.parse().ok()).unwrap_or(if p.log_n >= 20 { 6500 } else { 200 });
    proc::heap_setup(pf);
    // P-QUICK lever 1: the node program (blob parse, compile, zero table build, Φ's columns) depends on no
    // input, so it is built before `ready` (untimed) instead of after `go`
    crate::chainwalk::select(); // PORT-12 / P-FIX2: the chain walk's kernel, timed before `ready`
    let ctx = lvm::stream::Ctx { p, svc, vk, log, q: None, phi0: lv::primitives::field::F192::ZERO }.with_loop();
    if log {
        eprintln!("lvm: {mode} {} {} start-up {:.3} s; {tsel}", ctx.p.name, kat::info(), t_start.elapsed().as_secs_f64());
    }
    say("ready");
    wait_go();
    let t = Instant::now();
    let file = lvm::stream::run(&ctx, mode, dir);
    proc::tsu_release();
    std::fs::write(format!("{dir}/proof.bin"), &file).unwrap_or_else(|e| service::fatal(&format!("proof.bin: {e}")));
    if log {
        eprintln!("lvm: {mode} done in {:.3} s, file {} B, peak RSS {:.0} MiB", t.elapsed().as_secs_f64(), file.len(), peak_rss_mb());
    }
    say("done");
    proc::tsu_exit();
}

fn run(args: Vec<String>) -> i32 {
    match args.get(1).map(String::as_str) {
        Some("info") => println!("{}", kat::info()),
        Some("kat") => {
            let which = args.get(2).map_or("all", String::as_str);
            println!("{}", kat::info());
            if matches!(which, "keccak" | "all") {
                kat::keccak();
            }
            if matches!(which, "field" | "all") {
                kat::field();
            }
            if matches!(which, "oracle" | "all") {
                kat::oracle();
            }
        }
        Some("batch") => cmd_batch(&args),
        Some("sprove") => cmd_sprove(&args),
        Some("tbench") => cmd_tbench(&args),
        Some("gbench") => cmd_gbench(&args),
        Some("tsel") => cmd_tsel(),
        Some("pgbench") => cmd_pgbench(&args),
        Some("s2check") => {
            lvm::wire::check::closed_forms_match_brute_force();
            println!("s2check wire closed forms: ok");
            lvm::params::print_numbers();
        }
        Some("setup") => {
            let dir = args.get(2).cloned().or_else(|| std::env::var("RF_SETUP").ok()).unwrap_or_else(|| "/setup".into());
            return cmd_setup(&dir);
        }
        Some("selftest") => cmd_selftest(),
        Some("rqtest") => cmd_rqtest(&args),
        Some(m @ ("first" | "step")) => cmd_stream(m, args.get(2).map_or("/work", String::as_str)),
        _ => {
            eprintln!("usage: lvm-prover info | kat [keccak|field|oracle|all] | batch --log-n N [--local] [--sign] | setup DIR | first DIR | step DIR");
            return 2;
        }
    }
    0
}

/// The entry point: `main` of a plain build, `lvm_main_<variant>` behind `dispatch.s` (the symbol is renamed by
/// `build-asm.sh`). `argv` is read here, so no variant depends on std's own argument capture.
#[unsafe(no_mangle)]
pub extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    // SAFETY: the C runtime passes `argc` valid NUL-terminated strings.
    let args: Vec<String> = (0..argc as usize)
        .map(|i| unsafe { CStr::from_ptr(*argv.add(i)) }.to_string_lossy().into_owned())
        .collect();
    let code = run(args);
    let _ = std::io::stdout().flush();
    code
}
