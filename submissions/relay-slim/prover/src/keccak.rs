//! Keccak-f[1600] and Ethereum's Keccak-256 (the contract's one hash at core 7ecd179,
//! `RecursionFast/Contract/Hash/Keccak.lean`): the FIPS 202 sponge with rate 136 bytes, capacity 512
//! bits, a 32-byte output and Keccak's original padding `0x01 … 0x80` (a single padding byte is
//! `0x81`; not SHA-3's `0x06`). Lane `x + 5y` holds `A[x, y]`, a lane is the little-endian 64-bit word
//! of 8 state bytes. Written from the contract and FIPS 202; the known answers are those of
//! `RecursionFast/Controls/Keccak.lean`, `harness/rfh/keccak.py` and `service/src/keccak.rs`.
//!
//! * `keccak_f`: the scalar permutation (the reference of every other path);
//! * `keccak_f_x8`: eight independent states at once, AVX-512F (`vprolq`, `vpternlogq`) under
//!   `cpuid` dispatch, else the scalar loop (`FLOCK_KECCAK=scalar` forces the fallback);
//! * `Keccak256`: the streaming sponge; `Keyed`: the service's `PRF_k(q) = Keccak-256(k ‖ q)`
//!   (`service/PROTOCOL.md` §2.1), `⌊(32 + |q|)/136⌋ + 1` permutations;
//! * the relation hashes (`Contract/Relation.lean`): `chain_step` = Keccak(0x43 ‖ d) (one
//!   permutation), `chain_end`, `leaf_stmt` = Keccak(0x4C ‖ h ‖ enc64 n), `node_stmt` =
//!   Keccak(0x4E ‖ c₁ ‖ c₂).

pub type Digest = [u8; 32];

/// The rate in bytes (`Keccak.rate`).
pub const RATE: usize = 136;
/// Rate lanes.
pub const RATE_LANES: usize = RATE / 8;

/// ι's round constants (`Keccak.rc`, FIPS 202 Algorithm 5).
pub const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// ρ's offsets of lane `x + 5y` (`Keccak.rhoOffsets`, FIPS 202 Table 2).
pub const RHO: [u32; 25] = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14];

/// π as a gather: lane `i = x + 5y` of `π(a)` is lane `PI_SRC[i] = (x + 3y) mod 5 + 5x` of `a`.
pub const PI_SRC: [usize; 25] = {
    let mut t = [0usize; 25];
    let mut i = 0;
    while i < 25 {
        let (x, y) = (i % 5, i / 5);
        t[i] = (x + 3 * y) % 5 + 5 * x;
        i += 1;
    }
    t
};

/// Repeat `$b` with the constant `$v` = 0 … 4 (forces the unrolling, so every lane index and rotation
/// is a constant and the state stays in registers; tiny-keccak's device).
macro_rules! unroll5 {
    ($v:ident, $b:block) => {{
        { const $v: usize = 0; $b }
        { const $v: usize = 1; $b }
        { const $v: usize = 2; $b }
        { const $v: usize = 3; $b }
        { const $v: usize = 4; $b }
    }};
}
/// `$b` for the constant `$v` = 0 … 24.
macro_rules! unroll25 {
    ($v:ident, $b:block) => {
        unroll5!(UNROLL_HI, {
            unroll5!(UNROLL_LO, {
                const $v: usize = 5 * UNROLL_HI + UNROLL_LO;
                $b
            })
        })
    };
}

/// θ, ρ and π of one round: `b = π(ρ(θ(a)))` (the input of χ).
#[inline(always)]
pub fn theta_rho_pi(a: &[u64; 25], b: &mut [u64; 25]) {
    let mut c = [0u64; 5];
    unroll5!(X, {
        c[X] = a[X] ^ a[X + 5] ^ a[X + 10] ^ a[X + 15] ^ a[X + 20];
    });
    let mut d = [0u64; 5];
    unroll5!(X, {
        d[X] = c[(X + 4) % 5] ^ c[(X + 1) % 5].rotate_left(1);
    });
    unroll25!(I, {
        const S: usize = PI_SRC[I];
        b[I] = (a[S] ^ d[S % 5]).rotate_left(RHO[S]);
    });
}

/// χ and ι of round `r`: `a = χ(b)`, then `a[0] ^= RC[r]`.
#[inline(always)]
pub fn chi_iota(b: &[u64; 25], a: &mut [u64; 25], r: usize) {
    unroll25!(I, {
        const X: usize = I % 5;
        const Y5: usize = I - X;
        a[I] = b[I] ^ (!b[Y5 + (X + 1) % 5] & b[Y5 + (X + 2) % 5]);
    });
    a[0] ^= RC[r];
}

/// **Keccak-f[1600]** (`Keccak.keccakF`): the 24 rounds in place.
#[inline]
pub fn keccak_f(a: &mut [u64; 25]) {
    let mut b = [0u64; 25];
    for r in 0..24 {
        // two rounds per iteration would save the copies; LLVM keeps `a`, `b` in registers either way
        theta_rho_pi(a, &mut b);
        chi_iota(&b, a, r);
    }
}

// ---------------------------------------------------------------- eight states at once

/// `FLOCK_KECCAK=scalar` forces the scalar loop of `keccak_f_x8`.
pub fn x8_tier() -> &'static str {
    static T: std::sync::OnceLock<&'static str> = std::sync::OnceLock::new();
    T.get_or_init(|| {
        if std::env::var("FLOCK_KECCAK").is_ok_and(|v| v == "scalar") {
            return "scalar";
        }
        #[cfg(target_arch = "x86_64")]
        if std::arch::is_x86_feature_detected!("avx512f") {
            // the agreement guard: the vector path must equal the scalar one on a fixed input
            let mut s: [[u64; 25]; 8] = std::array::from_fn(|t| std::array::from_fn(|i| (i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ t as u64));
            let mut want = s;
            for w in want.iter_mut() {
                keccak_f(w);
            }
            unsafe { keccak_f_x8_avx512(&mut s) };
            if s == want {
                return "avx512";
            }
        }
        "scalar"
    })
}

/// Keccak-f[1600] of eight independent states.
pub fn keccak_f_x8(s: &mut [[u64; 25]; 8]) {
    #[cfg(target_arch = "x86_64")]
    if x8_tier() == "avx512" {
        unsafe { keccak_f_x8_avx512(s) };
        return;
    }
    for a in s.iter_mut() {
        keccak_f(a);
    }
}

/// The AVX-512F path: lane `i` of the eight states in one zmm register (a gather/scatter by an
/// 8 × 25 transpose through memory), θ's parities and χ by `vpternlogq`, ρ by `vprolvq`.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx512f")]
unsafe fn keccak_f_x8_avx512(s: &mut [[u64; 25]; 8]) {
    use std::arch::x86_64::*;
    // lane i of state t is at s[t][i]: index 25 t + i (u64 words)
    let base = s.as_mut_ptr() as *mut u64;
    let idx = _mm512_setr_epi64(0, 25, 50, 75, 100, 125, 150, 175);
    let mut a: [__m512i; 25] = [_mm512_setzero_si512(); 25];
    for i in 0..25 {
        a[i] = _mm512_i64gather_epi64::<8>(idx, base.add(i) as *const i64);
    }
    let rho: [__m512i; 25] = std::array::from_fn(|i| _mm512_set1_epi64(RHO[i] as i64));
    let one = _mm512_set1_epi64(1);
    for r in 0..24 {
        let mut c = [_mm512_setzero_si512(); 5];
        for x in 0..5 {
            let t = _mm512_ternarylogic_epi64::<0x96>(a[x], a[x + 5], a[x + 10]);
            c[x] = _mm512_ternarylogic_epi64::<0x96>(t, a[x + 15], a[x + 20]);
        }
        let mut d = [_mm512_setzero_si512(); 5];
        for x in 0..5 {
            d[x] = _mm512_xor_si512(c[(x + 4) % 5], _mm512_rolv_epi64(c[(x + 1) % 5], one));
        }
        let mut b = [_mm512_setzero_si512(); 25];
        for i in 0..25 {
            let src = PI_SRC[i];
            b[i] = _mm512_rolv_epi64(_mm512_xor_si512(a[src], d[src % 5]), rho[src]);
        }
        for y in 0..5 {
            for x in 0..5 {
                // a ^ (~b & c): truth table 0xD2
                a[x + 5 * y] = _mm512_ternarylogic_epi64::<0xD2>(b[x + 5 * y], b[(x + 1) % 5 + 5 * y], b[(x + 2) % 5 + 5 * y]);
            }
        }
        a[0] = _mm512_xor_si512(a[0], _mm512_set1_epi64(RC[r] as i64));
    }
    for i in 0..25 {
        _mm512_i64scatter_epi64::<8>(base.add(i) as *mut i64, idx, a[i]);
    }
}

// ---------------------------------------------------------------- the sponge

/// Lane `i` of a block of bytes, little-endian (`Keccak.blockLane`), `0` past its end.
#[inline(always)]
pub fn lane_of(b: &[u8], i: usize) -> u64 {
    let mut w = [0u8; 8];
    let lo = (8 * i).min(b.len());
    let hi = (8 * i + 8).min(b.len());
    w[..hi - lo].copy_from_slice(&b[lo..hi]);
    u64::from_le_bytes(w)
}

/// The first 32 bytes of the state (the digest).
#[inline(always)]
pub fn digest_of(a: &[u64; 25]) -> Digest {
    let mut d = [0u8; 32];
    for i in 0..4 {
        d[8 * i..8 * i + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    d
}

/// The streaming Keccak-256 sponge.
#[derive(Clone)]
pub struct Keccak256 {
    a: [u64; 25],
    buf: [u8; RATE],
    len: usize,
}

impl Default for Keccak256 {
    fn default() -> Self {
        Self::new()
    }
}

impl Keccak256 {
    pub fn new() -> Keccak256 {
        Keccak256 { a: [0; 25], buf: [0; RATE], len: 0 }
    }
    #[inline(always)]
    fn absorb_block(a: &mut [u64; 25], blk: &[u8]) {
        for i in 0..RATE_LANES {
            a[i] ^= u64::from_le_bytes(blk[8 * i..8 * i + 8].try_into().unwrap());
        }
        keccak_f(a);
    }
    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        if self.len > 0 {
            let k = (RATE - self.len).min(data.len());
            self.buf[self.len..self.len + k].copy_from_slice(&data[..k]);
            self.len += k;
            data = &data[k..];
            if self.len == RATE {
                Self::absorb_block(&mut self.a, &self.buf);
                self.len = 0;
            }
        }
        while data.len() >= RATE {
            Self::absorb_block(&mut self.a, &data[..RATE]);
            data = &data[RATE..];
        }
        if !data.is_empty() {
            self.buf[..data.len()].copy_from_slice(data);
            self.len = data.len();
        }
        self
    }
    /// The padded last block (`Keccak.pad`), its permutation and the digest.
    pub fn finalize(&self) -> Digest {
        let mut a = self.a;
        let mut blk = [0u8; RATE];
        blk[..self.len].copy_from_slice(&self.buf[..self.len]);
        blk[self.len] ^= 0x01;
        blk[RATE - 1] ^= 0x80;
        Self::absorb_block(&mut a, &blk);
        digest_of(&a)
    }
}

/// **Keccak-256** (`keccak256`).
pub fn keccak256(m: &[u8]) -> Digest {
    Keccak256::new().update(m).finalize()
}

/// Permutations of the sponge over `n` bytes: `⌊n/136⌋ + 1` (the padding always adds a byte).
pub const fn permutations(n: usize) -> u64 {
    (n / RATE) as u64 + 1
}

/// The service's keyed hash `q ↦ Keccak-256(k ‖ q)` (`service/PROTOCOL.md` §2.1): the 32-byte key
/// held in the sponge's buffer; `⌊(32 + |q|)/136⌋ + 1` permutations (`oracle_perms`).
#[derive(Clone)]
pub struct Keyed {
    pre: Keccak256,
}

impl Keyed {
    pub fn new(key: &[u8; 32]) -> Keyed {
        let mut pre = Keccak256::new();
        pre.update(key);
        Keyed { pre }
    }
    pub fn hash(&self, q: &[u8]) -> Digest {
        self.pre.clone().update(q).finalize()
    }
}

/// The service's permutations for one query of `n` bytes.
pub const fn oracle_perms(n: usize) -> u64 {
    permutations(32 + n)
}

// ---------------------------------------------------------------- the relation hashes

pub const TAG_CHAIN: u8 = 0x43;
pub const TAG_LEAF: u8 = 0x4C;
pub const TAG_NODE: u8 = 0x4E;

/// The padded single block of `chainStep d` = Keccak-256(0x43 ‖ d) as the 17 rate lanes of the
/// absorbed state (the capacity is zero): `0x43 ‖ d ‖ 0x01 ‖ 0^101 ‖ 0x80`.
#[inline(always)]
pub fn chain_block(d: &Digest) -> [u64; 25] {
    let mut a = [0u64; 25];
    let w: [u64; 4] = std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap()));
    a[0] = 0x43 | (w[0] << 8);
    a[1] = (w[0] >> 56) | (w[1] << 8);
    a[2] = (w[1] >> 56) | (w[2] << 8);
    a[3] = (w[2] >> 56) | (w[3] << 8);
    a[4] = (w[3] >> 56) | (0x01 << 8);
    a[16] = 0x80u64 << 56;
    a
}

/// `chainStep d = Keccak-256(0x43 ‖ d)`: one permutation.
#[inline]
pub fn chain_step(d: &Digest) -> Digest {
    let mut a = chain_block(d);
    keccak_f(&mut a);
    digest_of(&a)
}

/// `chainEnd s n`: `n` chain steps from `s`.
pub fn chain_end(s: &Digest, n: u64) -> Digest {
    let mut h = *s;
    for _ in 0..n {
        h = chain_step(&h);
    }
    h
}

/// `leafStmt h n = Keccak-256(0x4C ‖ h ‖ enc64 n)` (41 bytes, one permutation).
pub fn leaf_stmt(h: &Digest, n: u64) -> Digest {
    Keccak256::new().update(&[TAG_LEAF]).update(h).update(&n.to_le_bytes()).finalize()
}

/// `nodeStmt c₁ c₂ = Keccak-256(0x4E ‖ c₁ ‖ c₂)` (65 bytes, one permutation).
pub fn node_stmt(c1: &Digest, c2: &Digest) -> Digest {
    Keccak256::new().update(&[TAG_NODE]).update(c1).update(c2).finalize()
}

#[cfg(test)]
mod tests {
    use super::*;

    pub fn hex(d: &[u8]) -> String {
        d.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// leanVM's test pattern (`Controls/Keccak.lean` `pattern`, `kblock.py`).
    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((7 * i + 3) % 256) as u8).collect()
    }

    /// `keccakF_zero_kat` (`Controls/Keccak.lean`, the Keccak team's intermediate values).
    #[test]
    fn keccak_f_zero_kat() {
        let mut a = [0u64; 25];
        keccak_f(&mut a);
        let want: [u64; 25] = [
            0xF1258F7940E1DDE7, 0x84D5CCF933C0478A, 0xD598261EA65AA9EE, 0xBD1547306F80494D, 0x8B284E056253D057,
            0xFF97A42D7F8E6FD4, 0x90FEE5A0A44647C4, 0x8C5BDA0CD6192E76, 0xAD30A6F71B19059C, 0x30935AB7D08FFC64,
            0xEB5AA93F2317D635, 0xA9A6E6260D712103, 0x81A57C16DBCF555F, 0x43B831CD0347C826, 0x01F22F1A11A5569F,
            0x05E5635A21D9AE61, 0x64BEFEF28CC970F2, 0x613670957BC46611, 0xB87C5A554FD00ECB, 0x8C3EE88A1CCF32C8,
            0x940C7922AE3A2614, 0x1841F924A2C509E4, 0x16F53526E70465C2, 0x75F644E97F30A13B, 0xEAF1FF7B5CECA249,
        ];
        assert_eq!(a, want);
    }

    /// The round constants re-derived from FIPS 202's LFSR (Algorithm 5), as `Controls/Keccak.lean`.
    #[test]
    fn rc_from_lfsr() {
        let rc = |t: usize| -> u64 {
            let mut r: u32 = 1;
            for _ in 0..t % 255 {
                r <<= 1;
                if r & 0x100 != 0 {
                    r ^= 0x171;
                }
            }
            (r & 1) as u64
        };
        for i in 0..24 {
            let mut v = 0u64;
            for j in 0..7 {
                v |= rc(j + 7 * i) << ((1 << j) - 1);
            }
            assert_eq!(v, RC[i], "RC[{i}]");
        }
    }

    /// The known answers of `Controls/Keccak.lean`, `harness/rfh/keccak.py` and the service (with
    /// the padding edges 135/136/137, 271/272) and the SHA3 negative.
    #[test]
    fn keccak256_kats() {
        assert_eq!(hex(&keccak256(b"")), "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
        assert_ne!(hex(&keccak256(b"")), "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a");
        assert_eq!(hex(&keccak256(b"abc")), "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45");
        for (n, d) in [
            (135, "00ef96af9cf4b24c7f269d922294444a197d0a33638c2e56634c57e892103a8f"),
            (136, "742061bcad767ed4c4f5883b1dcb1aad11afdcc140dc469d953759b127b9f9ed"),
            (137, "e3371f61e770abf254c34239c3b0099ad90594507415bc81dd0a10b9692bbf2a"),
            (271, "4401c4afbe16ff911bdbf2d38e556e5b861f3fdf0f9d4306b1c46f6ae4f73584"),
            (272, "ac141fd7b0a0ffcd2e967254d508da3ec616596493c36fa304425647d90e6de5"),
        ] {
            assert_eq!(hex(&keccak256(&pattern(n))), d, "pattern({n})");
        }
        // the service's chain-step vector: "C" ‖ 00 01 … 1f
        let d: Digest = std::array::from_fn(|i| i as u8);
        assert_eq!(hex(&chain_step(&d)), "db8c51208716e57c91fc944cfa0df7336f9e784f9d3c0c04347f5fa833588e97");
        // kblock.py §3: three links from 0^32
        assert_eq!(hex(&chain_end(&[0u8; 32], 3)), "fb8b17f228b7c051624718dc288e76c1d1ce84f246ed2ac7e4d7396710dcbc08");
    }

    #[test]
    fn streaming_equals_one_shot() {
        let m = pattern(1000);
        for split in [0, 1, 35, 103, 104, 135, 136, 137, 271, 272, 999, 1000] {
            let mut h = Keccak256::new();
            h.update(&m[..split]).update(&m[split..]);
            assert_eq!(h.finalize(), keccak256(&m), "split at {split}");
        }
        let mut h = Keccak256::new();
        for b in &m[..300] {
            h.update(&[*b]);
        }
        assert_eq!(h.finalize(), keccak256(&m[..300]));
    }

    /// The service's keyed vectors (`service/src/keccak.rs` `keyed`, key 00 … 1f).
    #[test]
    fn keyed_kats() {
        let key: [u8; 32] = std::array::from_fn(|i| i as u8);
        let k = Keyed::new(&key);
        for (n, d) in [
            (0, "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"),
            (1, "c0a2a2460b6a12938ebd31825058add79257242e4479430c68dc2dea4f77e539"),
            (103, "ee17fa0bccfc9ef064b3c29cfaafeef311386ca16ac0f5ab7e63e1fa4bcb8b1e"),
            (104, "06d11ea2d8a362576c366116e23a193e62fa8cdb58dc5660a3033f780af83e4d"),
            (105, "baabd99912af774e0b5c4c4f46033cc00e68b4cf911409b481bd846ef93822d0"),
            (1000, "b3ebd3729073604285f9fe8b9ff8266ff49d5315c56aef81824e15b8942e4702"),
        ] {
            assert_eq!(hex(&k.hash(&pattern(n))), d, "keyed pattern({n})");
        }
        for n in [0usize, 1, 103, 104, 105, 239, 240, 241, 1000] {
            let mut kq = key.to_vec();
            kq.extend_from_slice(&pattern(n));
            assert_eq!(k.hash(&pattern(n)), keccak256(&kq));
        }
        assert_eq!((oracle_perms(103), oracle_perms(104), oracle_perms(239), oracle_perms(240)), (1, 2, 2, 3));
    }

    #[test]
    fn relation_hashes_are_the_sponge() {
        let d: Digest = std::array::from_fn(|i| (i as u8).wrapping_mul(91) ^ 0x5A);
        let mut m = vec![TAG_CHAIN];
        m.extend_from_slice(&d);
        assert_eq!(chain_step(&d), keccak256(&m));
        let mut m = vec![TAG_LEAF];
        m.extend_from_slice(&d);
        m.extend_from_slice(&123456789u64.to_le_bytes());
        assert_eq!(leaf_stmt(&d, 123456789), keccak256(&m));
        let e = chain_step(&d);
        let mut m = vec![TAG_NODE];
        m.extend_from_slice(&d);
        m.extend_from_slice(&e);
        assert_eq!(node_stmt(&d, &e), keccak256(&m));
    }

    #[test]
    fn x8_equals_scalar() {
        let mut s: [[u64; 25]; 8] = std::array::from_fn(|t| std::array::from_fn(|i| ((t * 25 + i) as u64).wrapping_mul(0xD6E8_FEB8_6659_FD93).rotate_left(t as u32)));
        let mut want = s;
        for w in want.iter_mut() {
            keccak_f(w);
            keccak_f(w);
        }
        keccak_f_x8(&mut s);
        keccak_f_x8(&mut s);
        assert_eq!(s, want, "tier {}", x8_tier());
        // the vector path must be the one tested where the CPU has it (the guard falls back silently)
        #[cfg(target_arch = "x86_64")]
        if std::arch::is_x86_feature_detected!("avx512f") && std::env::var_os("FLOCK_KECCAK").is_none() {
            assert_eq!(x8_tier(), "avx512");
        }
        eprintln!("keccak_f_x8 tier: {}", x8_tier());
    }
}
