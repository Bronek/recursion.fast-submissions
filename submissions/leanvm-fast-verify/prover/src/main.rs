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
mod format;
mod kat;
mod keccak;
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
    oracle::reset_stats();
    let t0 = Instant::now();
    let sp = lvm::prove::prove(&p, hd, rec, None);
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
    let _ = std::fs::write(format!("{dir}/lvm-selftest.txt"), &log);
    eprint!("{log}");
    0
}

/// `first DIR` / `step DIR` (PROVER.md §3): connect, `ready`, wait for `go`, prove, write `proof.bin`, `done`.
/// Parameter set `P20` (`LVM_PARAMS=P8` for local tests), 8 threads unless `LEANVM_NUM_THREADS` says otherwise.
fn cmd_stream(mode: &str, dir: &str) {
    let t_start = Instant::now();
    if std::env::var_os("LEANVM_NUM_THREADS").is_none() {
        // SAFETY: single-threaded here (no worker pool, no other thread yet).
        unsafe { std::env::set_var("LEANVM_NUM_THREADS", "8") };
    }
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
    if log {
        eprintln!("lvm: {mode} {} {} start-up {:.3} s", p.name, kat::info(), t_start.elapsed().as_secs_f64());
    }
    say("ready");
    wait_go();
    let t = Instant::now();
    let ctx = lvm::stream::Ctx { p, svc, vk, log, q: None, phi0: lv::primitives::field::F192::ZERO }.with_loop();
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
