//! leanVM's prover crates (leanVM 0b850750), vendored as modules by `tools/vendor.py`; every edit
//! after vendoring is listed in `PATCHES.md`.
#![allow(dead_code, unused_imports, unused_variables, clippy::all)]

pub mod fiat_shamir;
// PORT-13: the v4 tier (AVX-512 + GFNI + VBMI + VPCLMULQDQ, the evaluation machine) runs leanvm-gkr-fast's (#13)
// re-vendor of gattaca-com/leanVM `pr/all`'s GKR (`keccak_gkr_v4/`), storing every round as in #15; v2 and v4p keep
// leanVM 0b850750's (`keccak_gkr/`), which is faster without GFNI/VBMI. Same proofs, byte for byte (lv/PATCHES.md).
#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni",
    target_feature = "vpclmulqdq"
)))]
pub mod keccak_gkr;
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni",
    target_feature = "vpclmulqdq"
))]
#[path = "keccak_gkr_v4/mod.rs"]
pub mod keccak_gkr;
pub mod leanvm_core;
pub mod parallel;
pub mod pcs;
pub mod primitives;
pub mod tracing;
