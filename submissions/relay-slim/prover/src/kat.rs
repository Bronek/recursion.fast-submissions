//! Known-answer tests run by the binary itself (`lvm-prover kat [keccak|field|oracle|all]`), so that each
//! CPU variant (`prover-v2.s`, `prover-v4.s`, …) is tested as built: every kernel against an independent
//! reference, on fixed vectors, random operands and corners. A failure panics (exit 101 / abort).

use crate::keccak::{Keccak256, Keyed, keccak256};
use crate::lv::primitives::field::gf2_64::{R64, mul_wide, reduce, software};
use crate::lv::primitives::field::{F64, F192, mul2, mul4, mul_unreduced4};
use crate::lv::primitives::hash;

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// leanVM's test pattern bytes.
fn pattern(n: usize) -> Vec<u8> {
    (0..n).map(|i| (i.wrapping_mul(31) ^ (i >> 3)) as u8).collect()
}

pub fn keccak() {
    // Ethereum's Keccak-256 (service/PROTOCOL.md §2.0)
    let empty = "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470";
    let abc = "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45";
    assert_eq!(hex(&keccak256(b"")), empty);
    assert_eq!(hex(&keccak256(b"abc")), abc);
    assert_eq!(hex(&hash::hash(b"")), empty);
    assert_eq!(hex(&hash::hash(b"abc")), abc);
    // leanVM's sponge against FR's, every length through three blocks and some past
    for n in (0..=420).chain([543, 544, 545, 1000, 4096]) {
        let m = pattern(n);
        assert_eq!(hash::hash(&m), keccak256(&m), "length {n}");
        let mut st = Keccak256::new();
        st.update(&m[..n / 3]).update(&m[n / 3..]);
        assert_eq!(st.finalize(), keccak256(&m));
    }
    // the batched permutation (leanVM's backend: AVX-512 x8, AVX2 x4 or scalar) against the scalar one
    let mut r = Rng(0x0123_4567_89AB_CDEF);
    let mut states: Vec<[u64; 25]> = (0..37).map(|_| std::array::from_fn(|_| r.next())).collect();
    let mut want = states.clone();
    for s in want.iter_mut() {
        crate::keccak::keccak_f(s);
        crate::keccak::keccak_f(s);
    }
    hash::keccak_f_many(&mut states);
    hash::keccak_f_many(&mut states);
    assert_eq!(states, want, "keccak_f_many");
    let mut one = want[0];
    let mut two = want[0];
    hash::keccak_f(&mut one);
    crate::keccak::keccak_f(&mut two);
    assert_eq!(one, two, "keccak_f");
    // hash_many over equal-length items
    for len in [32usize, 64, 135, 136, 137, 512] {
        let data = pattern(len * 19);
        let mut out = vec![0u8; 32 * 19];
        hash::hash_many(&data, len, &mut out);
        for i in 0..19 {
            assert_eq!(out[32 * i..32 * i + 32], keccak256(&data[i * len..(i + 1) * len]), "hash_many {len}");
        }
    }
    // FR's x8 Keccak (AVX-512F under cpuid) against its scalar loop
    let mut s8: [[u64; 25]; 8] = std::array::from_fn(|t| std::array::from_fn(|i| (t * 25 + i) as u64 * 0x9E37));
    let mut w8 = s8;
    for w in w8.iter_mut() {
        crate::keccak::keccak_f(w);
    }
    crate::keccak::keccak_f_x8(&mut s8);
    assert_eq!(s8, w8, "keccak_f_x8 ({})", crate::keccak::x8_tier());
    // PORT-12: both chain-walk kernels (and relay-echo's two-chain call) against `keccak::chain_step`, on
    // chains of 0 … 40 and 5000 steps from random starts, the walk's blocks and inputs included
    use crate::chainwalk::{Kernel, block_of_lanes, walk, walk_y};
    let lanes = |d: &[u8; 32]| -> [u64; 4] { std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap())) };
    let mut rng = Rng(0x5EED_0012);
    for (t, n) in (0..=40usize).chain([1023, 1024, 1025, 5000]).enumerate() {
        let s: [u8; 32] = std::array::from_fn(|_| rng.next() as u8);
        let s2: [u8; 32] = std::array::from_fn(|_| rng.next() as u8);
        let mut want = Vec::with_capacity(n);
        let mut want2 = Vec::with_capacity(n);
        let (mut d, mut d2) = (s, s2);
        for _ in 0..n {
            d = crate::keccak::chain_step(&d);
            d2 = crate::keccak::chain_step(&d2);
            want.push(lanes(&d));
            want2.push(lanes(&d2));
        }
        for k in [Kernel::Lv, Kernel::Vl] {
            let mut y = vec![[0u64; 4]; n];
            let e = walk_y(k, lanes(&s), &mut y);
            assert!(y == want && e == if n > 0 { want[n - 1] } else { lanes(&s) }, "chain walk {k:?}, n = {n}");
            // the cut: none (production's `Chain::run`), mid-walk, the end, or past it (never called)
            let cut = [0, (7 * t) % (n + 1), n, n + 1][t % 4];
            let mut got_end = None;
            let (inp, y) = walk(k, lanes(&s), n, cut, |h| got_end = Some(h));
            assert!(y == want && inp.len() == n, "walk {k:?}, n = {n}");
            for i in 0..n {
                let prev = if i == 0 { lanes(&s) } else { want[i - 1] };
                assert_eq!(inp[i], block_of_lanes(&prev), "walk inputs {k:?}, n = {n}, row {i}");
                assert_eq!(inp[i], crate::keccak::chain_block(&crate::lvm::tables::lanes_digest(&prev)), "chain_block");
            }
            assert_eq!(got_end, if cut > 0 && cut <= n { Some(want[cut - 1]) } else { None }, "walk at_end {k:?}, n = {n}, cut {cut}");
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vl", target_feature = "avx512dq"))]
        {
            let mut ya = vec![[0u64; 4]; n];
            let mut yb = vec![[0u64; 4]; n];
            crate::keccak_vl::walk2(lanes(&s), lanes(&s2), &mut ya, &mut yb);
            assert!(ya == want && yb == want2, "keccak_vl::walk2, n = {n}");
        }
    }
    println!("kat keccak: ok (leanVM batch width {}, x8 tier {}, vl chain kernel {})", hash::LANES, crate::keccak::x8_tier(),
        if crate::keccak_vl::AVAILABLE { "tested" } else { "not in this build" });
}

/// The reference product: the bit loop, then long division by `x^64 + x^4 + x^3 + x + 1`.
fn ref_mul(a: u64, b: u64) -> u64 {
    let mut p = software::clmul(a, b);
    for bit in (64..128).rev() {
        if (p >> bit) & 1 != 0 {
            p ^= ((1u128 << 64) | R64 as u128) << (bit - 64);
        }
    }
    p as u64
}

/// The reference `E` product: schoolbook over `ref_mul`, `y^3 = y + 1`.
fn ref_mul_e(a: F192, b: F192) -> F192 {
    let (a, b) = (a.to_limbs(), b.to_limbs());
    let mut e = [0u64; 5];
    for i in 0..3 {
        for j in 0..3 {
            e[i + j] ^= ref_mul(a[i], b[j]);
        }
    }
    // y^3 = y + 1, y^4 = y^2 + y
    F192::new(e[0] ^ e[3], e[1] ^ e[3] ^ e[4], e[2] ^ e[4])
}

pub fn field() {
    // leanVM's independent Python vectors (`gf2_64.rs`, `gf2_64x3.rs` tests)
    const K: [(u64, u64, u64); 3] = [
        (0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
        (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
        (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb),
    ];
    type V = ([u64; 3], [u64; 3], [u64; 3], [u64; 3]);
    const E: [V; 2] = [
        (
            [0x950e87d7f5606615, 0x2c61275c9e6b6cf8, 0x1f00bca0042db923],
            [0x6dbca290a9eab706, 0x4c10a4fe30cffdda, 0xf26fff4cc4fd394d],
            [0x888a0fc35abaf5f6, 0x68a84cbc132b0649, 0x9fdeaf613003cabe],
            [0x8fba131ad5d46b8c, 0x1c170457f537a805, 0x3632cc098ca15135],
        ),
        (
            [0x6814a2bc786a6d2d, 0xa26b351e6c8042c5, 0x54760e7fbc051c6c],
            [0xd4c08880a5a4666d, 0x29610ae0eed8f1e7, 0xc34bd8e2fe5213e5],
            [0x2ad322ebf2f9043b, 0x8ac800aa67154c80, 0x6d0f76651d3c4d0c],
            [0xcf800ef2b83bb43a, 0xefe1c6cd064dd44c, 0x57dc5c7a60e2981b],
        ),
    ];
    for (a, b, c) in K {
        assert_eq!(ref_mul(a, b), c);
        assert_eq!(F64(a) * F64(b), F64(c), "F64 vector");
    }
    for (a, b, c, sq) in E {
        let (a, b) = (F192::from_limbs(a), F192::from_limbs(b));
        assert_eq!(ref_mul_e(a, b), F192::from_limbs(c));
        assert_eq!(a * b, F192::from_limbs(c), "F192 vector");
        assert_eq!(a.square(), F192::from_limbs(sq), "F192 square vector");
    }
    let corners: [u64; 7] = [0, 1, u64::MAX, 1 << 63, 0xF000_0000_0000_0000, R64, 0x8000_0000_0000_0001];
    let mut r = Rng(0x2545_F491_4F6C_DD1D);
    let pairs: Vec<(u64, u64)> = (0..20_000)
        .map(|_| (r.next(), r.next()))
        .chain(corners.iter().flat_map(|&a| corners.iter().map(move |&b| (a, b))))
        .collect();
    // every tier of the portable product (whatever this build dispatches to)
    let tiers = clmul_tiers();
    for &(a, b) in &pairs {
        let want = software::clmul(a, b);
        assert_eq!(mul_wide(a, b), want, "mul_wide");
        for (name, f) in &tiers {
            assert_eq!(f(a, b), want, "clmul tier {name}");
        }
        assert_eq!((F64(a) * F64(b)).0, ref_mul(a, b), "F64 mul");
        assert_eq!(reduce(want), ref_mul(a, b), "reduce");
        assert_eq!(F64(a).square(), F64(ref_mul(a, a)), "F64 square");
    }
    for &(a, _) in pairs.iter().take(300) {
        if a != 0 {
            assert_eq!(F64(a) * F64(a).inv(), F64::ONE, "F64 inv");
        }
    }
    // E: scalar, mixed, batched
    let es: Vec<F192> = (0..2_000).map(|_| F192::new(r.next(), r.next(), r.next())).collect();
    for w in es.windows(4) {
        let (a, b) = (w[0], w[1]);
        let want = ref_mul_e(a, b);
        assert_eq!(a * b, want, "F192 mul");
        assert_eq!(a.mul_unreduced(b).reduce(), want, "F192 mul_unreduced");
        assert_eq!(a.square(), ref_mul_e(a, a), "F192 square");
        assert_eq!(a.mul_base(F64(b.c0)), ref_mul_e(a, F192::new(b.c0, 0, 0)), "F192 mul_base");
        assert_eq!(a.mul_base_unreduced(F64(b.c1)).reduce(), ref_mul_e(a, F192::new(b.c1, 0, 0)), "mul_base_unreduced");
        let x: [F192; 4] = [w[0], w[1], w[2], w[3]];
        let y: [F192; 4] = [w[3], w[2], w[1], w[0]];
        let m4 = mul4(x, y);
        let u4 = mul_unreduced4(x, y);
        for i in 0..4 {
            assert_eq!(m4[i], ref_mul_e(x[i], y[i]), "mul4");
            assert_eq!(u4[i].reduce(), ref_mul_e(x[i], y[i]), "mul_unreduced4");
        }
        let m2 = mul2([w[0], w[1]], [w[2], w[3]]);
        assert_eq!(m2, [ref_mul_e(w[0], w[2]), ref_mul_e(w[1], w[3])], "mul2");
    }
    for a in es.iter().take(200) {
        if !a.is_zero() {
            assert_eq!(*a * a.inv(), F192::ONE, "F192 inv");
        }
    }
    println!(
        "kat field: ok ({} random pairs + corners; clmul tiers {:?}; dispatch {:?})",
        pairs.len(),
        tiers.iter().map(|t| t.0).collect::<Vec<_>>(),
        current_tier()
    );
}

type Tier = (&'static str, Box<dyn Fn(u64, u64) -> u128>);

fn clmul_tiers() -> Vec<Tier> {
    let mut t: Vec<Tier> = vec![("holes", Box::new(software::clmul_holes))];
    #[cfg(target_arch = "x86_64")]
    {
        if std::arch::is_x86_feature_detected!("avx512f") {
            t.push(("avx512", Box::new(|a, b| unsafe { software::clmul_avx512(a, b) })));
        }
        if std::arch::is_x86_feature_detected!("pclmulqdq") || std::env::var("LVM_PCLMUL").is_ok_and(|v| v == "1") {
            t.push((
                "pclmul",
                Box::new(|a, b| unsafe { crate::lv::primitives::field::gf2_64::x86_64::clmul(a, b) }),
            ));
        }
    }
    t
}

fn current_tier() -> &'static str {
    if cfg!(target_feature = "pclmulqdq") {
        return "compile-time pclmulqdq";
    }
    match software::tier() {
        software::Tier::Pclmul => "run-time pclmul",
        software::Tier::Avx512 => "run-time avx512",
        software::Tier::Holes => "run-time holes",
    }
}

pub fn oracle() {
    let key = [0x5Au8; 32];
    let k = Keyed::new(&key);
    for n in [0usize, 7, 32, 64, 103, 104, 239, 240, 384, 512, 4952] {
        let q = pattern(n);
        let mut kq = key.to_vec();
        kq.extend_from_slice(&q);
        assert_eq!(k.hash(&q), keccak256(&kq), "keyed {n}");
    }
    println!("kat oracle: ok (Keyed = Keccak-256(k ‖ q))");
}

/// What this build is: the variant's compile-time features and its run-time choices.
pub fn info() -> String {
    let f = |b: bool, s: &str| if b { s.to_string() } else { String::new() };
    let feats = [
        f(cfg!(target_feature = "avx2"), "avx2"),
        f(cfg!(target_feature = "bmi2"), "bmi2"),
        f(cfg!(target_feature = "avx512f"), "avx512f"),
        f(cfg!(target_feature = "avx512bw"), "avx512bw"),
        f(cfg!(target_feature = "avx512vbmi"), "avx512vbmi"),
        f(cfg!(target_feature = "pclmulqdq"), "pclmulqdq"),
        f(cfg!(target_feature = "vpclmulqdq"), "vpclmulqdq"),
        f(cfg!(target_feature = "gfni"), "gfni"),
    ]
    .into_iter()
    .filter(|s| !s.is_empty())
    .collect::<Vec<_>>()
    .join(",");
    format!(
        "variant {} (compile-time: {feats}); K product: {}; Keccak batch width {}; threads {}; {}",
        crate::VARIANT,
        current_tier(),
        hash::LANES,
        crate::lv::parallel::num_threads(),
        crate::chainwalk::info()
    )
}
