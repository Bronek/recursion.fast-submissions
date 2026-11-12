//! Process plumbing of a request (PROVER.md §3: what runs before `ready` and around `done`), adapted from
//! `rf-k/submissions/flock-recursive/prover/main.rs@8bff272b` (`heap_setup`, `heap_arena`, `heap_pretouch`,
//! `tsu_release`, `sign_checked`) and `stream.rs` (`read_chain`): verbatim but for the environment names
//! (`FLOCK_` → `LVM_`), the pool (`par` → `lv::parallel`) and FR's profiler hooks (dropped).
#![allow(unsafe_op_in_unsafe_fn, clippy::missing_safety_doc)]

use crate::{alloc, service};

/// A raw pointer the pool's tasks may share (FR `par::SyncPtr`).
pub struct SyncPtr<T>(pub *mut T);
unsafe impl<T> Sync for SyncPtr<T> {}
unsafe impl<T> Send for SyncPtr<T> {}

unsafe extern "C" {
    /// glibc's `mallopt` (the prover is linked with glibc, `-static`).
    fn mallopt(param: i32, value: i32) -> i32;
}

/// Keep small freed memory in one arena (glibc) and pre-fault `mib` MiB for the large-block cache
/// (`alloc.rs`), before the request's clock.
///
/// H4: setting `M_TRIM_THRESHOLD` also freezes glibc's mmap threshold at 128 KiB, so every
/// allocation of 128 KiB … 8 MiB (below `alloc.rs`'s cache) was a fresh `mmap`, faulted page by
/// page inside the request and unmapped at its `free` (≈ 27,000 faults in an N2 node's shift
/// phase alone). The threshold is now the cache's 8 MiB: those allocations come from the arena,
/// which is never trimmed, and `HEAP_PRETOUCH_MIB` of it is faulted here, before `ready`
/// (`LVM_HEAP_MIB` overrides, in whole 4 MiB pieces: 1 … 3 raise the threshold and pre-touch
/// nothing; 0 keeps the old behaviour: no threshold change, no pre-touch).
pub fn heap_setup(mib: usize) {
    heap_arena();
    alloc::prefault(mib << 20);
}

/// `heap_setup`'s glibc part (the settings and the arena's pre-touch), once per process. TSU: the
/// stream calls it first thing, so that the start-up's own mid-size allocations (the node data,
/// the plans) come from the pre-touched huge-page arena instead of small-page `mmap`s and arena
/// growth, which the dying process frees ≈ 9× slower (`LVM_ARENA_EARLY=0`: as before).
pub fn heap_arena() {
    static DONE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
    if DONE.swap(true, std::sync::atomic::Ordering::Relaxed) {
        return;
    }
    let heap: usize = std::env::var("LVM_HEAP_MIB").ok().and_then(|x| x.parse().ok()).unwrap_or(HEAP_PRETOUCH_MIB);
    // SAFETY: plain glibc calls (M_ARENA_MAX = -8, M_TRIM_THRESHOLD = -1, M_MMAP_THRESHOLD = -3);
    // a refused setting is only slower.
    unsafe {
        mallopt(-8, 1);
        mallopt(-1, i32::MAX);
        if heap > 0 {
            mallopt(-3, alloc::BIG as i32);
        }
    }
    if heap > 0 {
        heap_pretouch(heap << 20);
    }
}

/// TSU: the arena's advised but untouched address space beyond the pre-touch (MiB).
const ARENA_SPAN_MIB: usize = 1024;

/// The arena pre-touched by `heap_setup` (MiB).
const HEAP_PRETOUCH_MIB: usize = 256;

/// Fault `bytes` of glibc's arena now: allocate it in 4 MiB pieces (below the mmap threshold, so
/// from the arena), touch every page from the pool's threads, free it all. Untrimmed, the pages stay
/// in the process for the request's mid-size allocations. No effect on any result.
fn heap_pretouch(bytes: usize) {
    const PIECE: usize = 4 << 20;
    let l = std::alloc::Layout::from_size_align(PIECE, 8).unwrap();
    // SAFETY: each piece is allocated, written within its bounds and freed with its layout
    unsafe {
        // TSU: the arena as transparent huge pages, so that the dying process frees it ≈ 9× faster
        // (TSU-RESULT §3.1; the runner's clock runs until it is dead). The heap is first grown by the
        // whole pre-touch at once (`M_TOP_PAD` for the first piece's `sbrk`), then the grown span is
        // advised `MADV_HUGEPAGE` before anything else in it is written (glibc's chunk headers
        // included: a 2 MiB range with one small page already faulted stays small). A refusal only
        // costs speed. `LVM_ARENA_THP=0` keeps small pages.
        let thp = std::env::var("LVM_ARENA_THP").map_or(true, |v| v != "0") && bytes >= PIECE;
        if thp {
            // M_TOP_PAD = -2 (glibc's default 128 KiB is restored below). The heap grows by the
            // pre-touch plus `ARENA_SPAN_MIB` of address space that is advised but not touched: the
            // start-up's and the request's arena growth beyond the pre-touch (≈ 250 MB, TSU-RESULT
            // §4) then faults huge pages too. Untouched, it costs no memory.
            mallopt(-2, (bytes + (ARENA_SPAN_MIB << 20)) as i32);
        }
        let mut ps: Vec<crate::proc::SyncPtr<u8>> = Vec::with_capacity(bytes / PIECE);
        ps.push(crate::proc::SyncPtr(std::alloc::alloc(l)));
        if thp {
            mallopt(-2, 128 << 10);
            let top = sbrk(0) as usize;
            let lo = (ps[0].0 as usize + PIECE).next_multiple_of(2 << 20);
            let hi = top & !((2 << 20) - 1);
            if !ps[0].0.is_null() && hi > lo {
                arena_madvise(lo as *mut u8, hi - lo, 14);
            }
        }
        ps.extend((1..bytes / PIECE).map(|_| crate::proc::SyncPtr(std::alloc::alloc(l))));
        if ps.iter().any(|p| p.0.is_null()) {
            service::fatal("heap pre-touch: out of memory");
        }
        crate::lv::parallel::for_each(ps.len(), |i| {
            for o in (0..PIECE).step_by(4096) {
                std::ptr::write_volatile(ps[i].0.add(o), 0);
            }
        });
        for p in ps.iter().rev() {
            std::alloc::dealloc(p.0, l);
        }
    }
}

unsafe extern "C" {
    #[link_name = "madvise"]
    fn arena_madvise(addr: *mut u8, len: usize, advice: i32) -> i32;
    /// glibc's `sbrk` (`sbrk(0)`: the heap's top, read only)
    fn sbrk(incr: isize) -> *mut u8;
    /// glibc's `_exit` (TSU's measurement switch `LVM_TSU_EXIT`)
    fn _exit(code: i32) -> !;
}

/// TSU: just before `done`, once the request's large buffers are dead, hand the cache's free blocks
/// back to the kernel from 4 threads (`alloc::release_free`; `LVM_REL=0` turns it off).
pub fn tsu_release() {
    if std::env::var("LVM_REL").map_or(true, |v| v != "0") {
        let t = std::time::Instant::now();
        let (b, hs) = alloc::release_free(4);
        // measurements (`LVM_TSU=1`, `LVM_TSU_JOIN=1`): wait for the release and time it, so
        // that `kill_s` is the teardown of what is left; otherwise the threads run on, detached
        if std::env::var_os("LVM_TSU_JOIN").is_some() {
            for h in hs {
                let _ = h.join();
            }
            eprintln!("TSU release {} MiB joined in {:.4} s", b >> 20, t.elapsed().as_secs_f64());
        } else if std::env::var_os("LVM_LOG").is_some() {
            eprintln!("TSU release {} MiB", b >> 20);
        }
    }
}


/// `SIGN` the trace; its answers must be the ones recorded while proving (FR `sign_checked`).
pub fn sign_checked(svc: &service::Service, tr: &crate::oracle::Trace) -> crate::format::Sig {
    let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
    let (answers, sig) = svc.sign(&qs);
    if answers.len() != tr.len() || answers.iter().zip(tr.iter()).any(|(a, (_, b))| a != b) {
        service::fatal("SIGN answers differ from the QUERY answers");
    }
    sig
}

fn unhex(s: &str) -> Vec<u8> {
    let s = s.trim();
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex")).collect()
}

/// A chain file `{"n": N, "start": "HEX"}` (FR `stream::read_chain`).
pub fn read_chain(p: &std::path::Path) -> (u64, crate::keccak::Digest) {
    let t = std::fs::read_to_string(p).unwrap_or_else(|e| service::fatal(&format!("{}: {e}", p.display())));
    let after = |k: &str| -> &str { &t[t.find(k).unwrap_or_else(|| service::fatal(&format!("{}: no {k}", p.display()))) + k.len()..] };
    let n: u64 = after("\"n\"").trim_start_matches([' ', ':']).split(|c: char| !c.is_ascii_digit()).next().unwrap().parse().expect("n");
    let s = after("\"start\"");
    let q = s.find('"').expect("start") + 1;
    let start: crate::keccak::Digest = unhex(&s[q..q + 64]).try_into().expect("start: 32 bytes");
    (n, start)
}

/// FR's measurement switch: `LVM_TSU_EXIT=1` ends the process with `_exit(0)` right after `done`.
pub fn tsu_exit() {
    if std::env::var_os("LVM_TSU_EXIT").is_some() {
        unsafe { _exit(0) }
    }
}
