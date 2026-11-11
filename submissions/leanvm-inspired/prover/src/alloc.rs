#![allow(unsafe_op_in_unsafe_fn)]
//! The global allocator: small allocations go to glibc; allocations of at least 8 MiB come from a
//! cache of page-aligned blocks that are never returned to the kernel, so a request's large
//! buffers reuse pages that are already faulted in (K §3's pre-faulted arena, as an allocator).
//! `prefault(bytes)` maps and touches one block before the timed part of a request; later large
//! allocations are carved from it (best fit, split), and freed blocks go back to the cache.
//! No effect on any result. (From `flock-recursive/prover/alloc.rs`; WP-4: `LVM_ALLOC=system` passes every
//! allocation to glibc, for the memory measurements, and the prefault uses scoped threads.)

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::Mutex;

pub const BIG: usize = 8 << 20;
// `main.rs` passes `BIG` to glibc as `M_MMAP_THRESHOLD`, whose cap is 32 MiB on x86-64
const _: () = assert!(BIG <= 32 << 20);
const PAGE: usize = 4096;
/// Large blocks are 2 MiB-aligned and advised as transparent huge pages (`MADV_HUGEPAGE`; the
/// runners' THP mode is `madvise`): fewer faults in `prefault`, fewer TLB misses on the tables.
/// `LVM_NO_THP` turns it off (measurements).
const HUGE: usize = 2 << 20;

unsafe extern "C" {
    /// glibc's `madvise` (the prover is linked with glibc, `-static`).
    fn madvise(addr: *mut u8, len: usize, advice: i32) -> i32;
}

pub struct Cache;

struct State {
    /// free blocks `(address, bytes)`
    free: Vec<(usize, usize)>,
    /// live blocks handed out `(address, bytes)`
    live: Vec<(usize, usize)>,
    mapped: usize,
    /// bytes in `live` now, and their high-water mark (TSU's measurements)
    live_bytes: usize,
    live_peak: usize,
}

static STATE: Mutex<State> = Mutex::new(State { free: Vec::new(), live: Vec::new(), mapped: 0, live_bytes: 0, live_peak: 0 });

impl State {
    fn hand_out(&mut self, a: usize, sz: usize) {
        self.live.push((a, sz));
        self.live_bytes += sz;
        self.live_peak = self.live_peak.max(self.live_bytes);
    }
}

fn round(n: usize) -> usize {
    n.div_ceil(PAGE) * PAGE
}

unsafe fn map(bytes: usize) -> *mut u8 {
    let p = System.alloc(Layout::from_size_align_unchecked(bytes, HUGE));
    if !p.is_null() && std::env::var_os("LVM_NO_THP").is_none() {
        // MADV_HUGEPAGE = 14; a refusal only costs speed
        madvise(p, bytes, 14);
    }
    p
}

/// `LVM_ALLOC=system`: no cache, every allocation is glibc's (read once).
fn system_only() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static S: AtomicU8 = AtomicU8::new(2);
    match S.load(Ordering::Relaxed) {
        2 => {
            // no allocation here: `var_os` would allocate inside the allocator
            let on = env_is("LVM_ALLOC", b"system");
            S.store(on as u8, Ordering::Relaxed);
            on
        }
        v => v == 1,
    }
}

/// Whether the environment variable `name` is `val`, read from `/proc`-free libc `getenv` (no allocation).
fn env_is(name: &str, val: &[u8]) -> bool {
    unsafe extern "C" {
        fn getenv(name: *const u8) -> *const u8;
    }
    let mut n = [0u8; 64];
    n[..name.len()].copy_from_slice(name.as_bytes());
    // SAFETY: a NUL-terminated name; getenv returns NULL or a NUL-terminated string
    unsafe {
        let p = getenv(n.as_ptr());
        if p.is_null() {
            return false;
        }
        let mut i = 0;
        while *p.add(i) != 0 {
            i += 1;
        }
        std::slice::from_raw_parts(p, i) == val
    }
}

unsafe impl GlobalAlloc for Cache {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if l.size() < BIG || l.align() > PAGE || system_only() {
            return System.alloc(l);
        }
        let need = round(l.size());
        let mut st = STATE.lock().unwrap();
        // best fit
        let mut best: Option<usize> = None;
        for (i, &(_, sz)) in st.free.iter().enumerate() {
            if sz >= need && best.map_or(true, |b| sz < st.free[b].1) {
                best = Some(i);
            }
        }
        if let Some(i) = best {
            let (a, sz) = st.free.swap_remove(i);
            if sz - need >= BIG {
                st.free.push((a + need, sz - need));
                st.hand_out(a, need);
            } else {
                st.hand_out(a, sz);
            }
            return a as *mut u8;
        }
        drop(st);
        let p = map(need);
        if p.is_null() {
            return p;
        }
        let mut st = STATE.lock().unwrap();
        st.mapped += need;
        st.hand_out(p as usize, need);
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        if l.size() < BIG || l.align() > PAGE || system_only() {
            return System.dealloc(p, l);
        }
        let mut st = STATE.lock().unwrap();
        let a = p as usize;
        let i = st.live.iter().position(|e| e.0 == a).expect("unknown large block");
        let (_, sz) = st.live.swap_remove(i);
        st.live_bytes -= sz;
        // merge with a free neighbour that follows or precedes it
        let mut blk = (a, sz);
        loop {
            if let Some(j) = st.free.iter().position(|e| e.0 == blk.0 + blk.1) {
                let (_, s2) = st.free.swap_remove(j);
                blk.1 += s2;
            } else if let Some(j) = st.free.iter().position(|e| e.0 + e.1 == blk.0) {
                let (a2, s2) = st.free.swap_remove(j);
                blk = (a2, s2 + blk.1);
            } else {
                break;
            }
        }
        st.free.push(blk);
    }
}

/// Map and touch `bytes` now (before a request's clock), as one cached free block.
pub fn prefault(bytes: usize) {
    let need = round(bytes);
    unsafe {
        let p = map(need);
        if p.is_null() {
            return;
        }
        let base = p as usize;
        let pages = need / PAGE;
        std::thread::scope(|sc| {
            for c in 0..8 {
                sc.spawn(move || {
                    for i in (c * pages / 8)..((c + 1) * pages / 8) {
                        std::ptr::write_volatile((base + i * PAGE) as *mut u8, 0);
                    }
                });
            }
        });
        let mut st = STATE.lock().unwrap();
        st.mapped += need;
        st.free.push((p as usize, need));
    }
}

/// Bytes mapped by the cache.
pub fn mapped() -> usize {
    STATE.lock().unwrap().mapped
}

/// `(mapped, live now, live high-water)` bytes of the cache (TSU's measurements).
pub fn stats() -> (usize, usize, usize) {
    let st = STATE.lock().unwrap();
    (st.mapped, st.live_bytes, st.live_peak)
}

/// K1-MEM: `LVM_MEMLOG` prints, at each phase mark, the cache's mapped bytes, its live bytes and
/// their high-water mark since the previous mark (which this resets), and the process's `VmRSS`
/// and `VmHWM`. Diagnostics only; no effect on any result.
pub fn memlog(name: &str) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ON.get_or_init(|| std::env::var_os("LVM_MEMLOG").is_some()) {
        return;
    }
    let (mp, lv, pk) = {
        let mut st = STATE.lock().unwrap();
        let r = (st.mapped, st.live_bytes, st.live_peak);
        st.live_peak = st.live_bytes;
        r
    };
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let kb = |k: &str| s.lines().find(|l| l.starts_with(k)).and_then(|l| l[k.len()..].trim().trim_end_matches("kB").trim().parse::<u64>().ok()).unwrap_or(0);
    eprintln!("MEMLOG {name} mapped_mib={} live_mib={} phase_peak_mib={} rss_mib={} hwm_mib={}", mp >> 20, lv >> 20, pk >> 20, kb("VmRSS:") >> 10, kb("VmHWM:") >> 10);
}

/// TSU: return the pages of every free cached block to the kernel (`MADV_DONTNEED`) from `k`
/// detached threads, and drop those blocks from the cache (a later large allocation maps anew).
/// Called once a request's large buffers are dead, just before `done`: the runner stops the clock
/// when the last process is dead (PROVER.md §3), and the kernel frees a dying process's pages on
/// one CPU (`exit_mmap`); freed here, they are freed on `k` CPUs, overlapped with writing
/// `proof.bin`. The threads are not joined; at `done` the runner's kill waits for them (on the
/// clock either way), and they write nothing. No effect on any result. Returns the bytes released
/// and the threads (dropping the handles detaches them).
pub fn release_free(k: usize) -> (usize, Vec<std::thread::JoinHandle<()>>) {
    let blocks = std::mem::take(&mut STATE.lock().unwrap().free);
    let total: usize = blocks.iter().map(|b| b.1).sum();
    if total == 0 || k == 0 {
        return (0, Vec::new());
    }
    // cut the free bytes into `k` shares at 2 MiB boundaries (whole huge pages per thread)
    let share = total.div_ceil(k).div_ceil(HUGE) * HUGE;
    let mut parts: Vec<Vec<(usize, usize)>> = vec![Vec::new(); k];
    let (mut t, mut room) = (0, share);
    for (mut a, mut sz) in blocks {
        while sz > 0 {
            let take = sz.min(room);
            parts[t].push((a, take));
            a += take;
            sz -= take;
            room -= take;
            if room == 0 && t + 1 < k {
                t += 1;
                room = share;
            } else if room == 0 {
                room = usize::MAX;
            }
        }
    }
    let hs = parts
        .into_iter()
        .filter(|p| !p.is_empty())
        .filter_map(|part| {
            std::thread::Builder::new()
                .stack_size(64 << 10)
                .spawn(move || {
                    for (a, sz) in part {
                        // MADV_DONTNEED = 4; the block is out of the cache, nobody else holds it
                        unsafe { madvise(a as *mut u8, sz, 4) };
                    }
                })
                .ok()
        })
        .collect();
    (total, hs)
}
