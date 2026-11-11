// Vendored from leanVM 0b850750 + the pr/all crate diff (04fba039b..edd857be9) `crates/pcs/src/ntt/scratch.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The thread-local scratch every pass transforms in.

use crate::lv::primitives::field::F64;
use std::cell::RefCell;

/// One cache line of words.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub(super) struct Line([F64; 8]);

// SAFETY: one field, an array of plain words.
unsafe impl crate::lv::primitives::Plain for Line {}

/// Lend this thread's scratch buffer, grown to the requested length.
///
/// - It is cache-line aligned, so a full-width load never splits a line.
/// - It lives as long as the thread, so no pass allocates in its hot loop.
pub(super) fn with_scratch<R>(len: usize, f: impl FnOnce(&mut [F64]) -> R) -> R {
    thread_local! {
        static SCRATCH: RefCell<Vec<Line>> = const { RefCell::new(Vec::new()) };
    }
    SCRATCH.with_borrow_mut(|lines| {
        // Grow only; a later, smaller request reuses the same lines.
        if lines.len() * 8 < len {
            lines.resize(len.div_ceil(8), Line([F64::ZERO; 8]));
        }
        f(&mut crate::lv::primitives::cast_slice_mut::<Line, F64>(lines)[..len])
    })
}
