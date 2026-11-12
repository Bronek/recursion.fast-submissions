-- From relay-echo (#12), `lean/FastDefs.lean` (Apache-2.0), unchanged except the module names of
-- its imports.
/-
  The compiled verifier of the relay-echo entry. `check'` decides what the library's
  `WitnessSending.check` decides; `V'` is the verifier built on it. The statements that tie them
  to the library are in `FastSpec.lean`.

  **The chain in lanes.** A leaf's hash chain runs on `H4`, a digest as four little-endian
  64-bit words; the digest is converted to lanes and back once per leaf (`toH4`, `ofH4`). One
  step (`stepH4`) builds the padded block of `tagChain ‖ d` directly in the 25 lanes
  (`blockH4`), applies `Keccak-f[1600]` (`permF`: the first and last rounds written out, rounds
  1 to 22 as a loop, all on complemented lanes) and keeps lanes 0 to 3. `stepH4` and `permF`
  are what the statements name. `check'` runs the chain as `chainEndH4`: the same rounds, with
  the steps and the rounds in one loop over unboxed words (`chainLoop`), so that no state is
  built between steps.

  **The format on byte arrays.** `check'` reads one level of the proof in place (`parseB`):
  every field at its byte index, the children's proofs as slices, and no list of bytes or words.
  It then builds the encoding of what it read in a byte array (`encodeB`) and compares it with
  the proof, which rejects trailing bytes and non-zero padding as the library's re-encoding
  does. The conjuncts on the witness are the library's `check`, recursing into `check'`.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.FastCheck
open RecursionFast Keccak

/-! ## The chain in lanes -/

/-- A digest as four little-endian 64-bit words: bytes `8i … 8i + 7` are word `hi`. -/
structure H4 where
  (h0 h1 h2 h3 : UInt64)

/-- The four little-endian words of a digest. -/
def toH4 (d : Digest) : H4 :=
  ⟨d[0].toUInt64 ||| d[1].toUInt64 <<< 8 ||| d[2].toUInt64 <<< 16 ||| d[3].toUInt64 <<< 24 |||
      d[4].toUInt64 <<< 32 ||| d[5].toUInt64 <<< 40 ||| d[6].toUInt64 <<< 48 |||
      d[7].toUInt64 <<< 56,
    d[8].toUInt64 ||| d[9].toUInt64 <<< 8 ||| d[10].toUInt64 <<< 16 ||| d[11].toUInt64 <<< 24 |||
      d[12].toUInt64 <<< 32 ||| d[13].toUInt64 <<< 40 ||| d[14].toUInt64 <<< 48 |||
      d[15].toUInt64 <<< 56,
    d[16].toUInt64 ||| d[17].toUInt64 <<< 8 ||| d[18].toUInt64 <<< 16 |||
      d[19].toUInt64 <<< 24 ||| d[20].toUInt64 <<< 32 ||| d[21].toUInt64 <<< 40 |||
      d[22].toUInt64 <<< 48 ||| d[23].toUInt64 <<< 56,
    d[24].toUInt64 ||| d[25].toUInt64 <<< 8 ||| d[26].toUInt64 <<< 16 |||
      d[27].toUInt64 <<< 24 ||| d[28].toUInt64 <<< 32 ||| d[29].toUInt64 <<< 40 |||
      d[30].toUInt64 <<< 48 ||| d[31].toUInt64 <<< 56⟩

/-- The 32 bytes of four words, each little-endian (the byte formulas of `Keccak.outBytes`). -/
def ofH4 (h : H4) : Digest :=
  #v[(h.h0 >>> 0).toUInt8, (h.h0 >>> 8).toUInt8, (h.h0 >>> 16).toUInt8, (h.h0 >>> 24).toUInt8,
    (h.h0 >>> 32).toUInt8, (h.h0 >>> 40).toUInt8, (h.h0 >>> 48).toUInt8, (h.h0 >>> 56).toUInt8,
    (h.h1 >>> 0).toUInt8, (h.h1 >>> 8).toUInt8, (h.h1 >>> 16).toUInt8, (h.h1 >>> 24).toUInt8,
    (h.h1 >>> 32).toUInt8, (h.h1 >>> 40).toUInt8, (h.h1 >>> 48).toUInt8, (h.h1 >>> 56).toUInt8,
    (h.h2 >>> 0).toUInt8, (h.h2 >>> 8).toUInt8, (h.h2 >>> 16).toUInt8, (h.h2 >>> 24).toUInt8,
    (h.h2 >>> 32).toUInt8, (h.h2 >>> 40).toUInt8, (h.h2 >>> 48).toUInt8, (h.h2 >>> 56).toUInt8,
    (h.h3 >>> 0).toUInt8, (h.h3 >>> 8).toUInt8, (h.h3 >>> 16).toUInt8, (h.h3 >>> 24).toUInt8,
    (h.h3 >>> 32).toUInt8, (h.h3 >>> 40).toUInt8, (h.h3 >>> 48).toUInt8, (h.h3 >>> 56).toUInt8]

/-- The padded block of `tagChain ‖ d` (33 bytes, then `0x01`, zeros and `0x80` at byte 135) in
the 25 lanes, from the words of `d`: the tag shifts the digest by one byte. -/
@[inline] def blockH4 (h : H4) : S25 :=
  ⟨(0x43 : UInt64) ||| h.h0 <<< 8, h.h0 >>> 56 ||| h.h1 <<< 8, h.h1 >>> 56 ||| h.h2 <<< 8,
    h.h2 >>> 56 ||| h.h3 <<< 8, h.h3 >>> 56 ||| 0x100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0x8000000000000000, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The lanes `1, 2, 8, 12, 17, 20` complemented: the representation of the state that
`roundC` keeps (lane complementing, as in the Keccak team's code). -/
@[inline] def complL (s : S25) : S25 :=
  ⟨s.a0, ~~~s.a1, ~~~s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, ~~~s.a8, s.a9, s.a10, s.a11, ~~~s.a12,
    s.a13, s.a14, s.a15, s.a16, ~~~s.a17, s.a18, s.a19, ~~~s.a20, s.a21, s.a22, s.a23, s.a24⟩

/-- `roundF` on complemented lanes: `roundC (complL s) c = complL (roundF s c)`. θ, ρ and π are
`roundF`'s; each row of χ follows its five lanes, and with the lanes of `complL` complemented, χ
needs one NOT per row instead of five (the others become `|||` or a NOT shared by two lanes). -/
@[inline] def roundC (s : S25) (c : UInt64) : S25 :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotK c1 1
  let d1 := c0 ^^^ rotK c2 1
  let d2 := c1 ^^^ rotK c3 1
  let d3 := c2 ^^^ rotK c4 1
  let d4 := c3 ^^^ rotK c0 1
  let b0 := rotK (s.a0 ^^^ d0) 0
  let b1 := rotK (s.a6 ^^^ d1) 44
  let b2 := rotK (s.a12 ^^^ d2) 43
  let b3 := rotK (s.a18 ^^^ d3) 21
  let b4 := rotK (s.a24 ^^^ d4) 14
  let n2 := ~~~b2
  let e0 := b0 ^^^ (b1 ||| b2) ^^^ c
  let e1 := b1 ^^^ (n2 ||| b3)
  let e2 := b2 ^^^ (b3 &&& b4)
  let e3 := b3 ^^^ (b4 ||| b0)
  let e4 := b4 ^^^ (b0 &&& b1)
  let b5 := rotK (s.a3 ^^^ d3) 28
  let b6 := rotK (s.a9 ^^^ d4) 20
  let b7 := rotK (s.a10 ^^^ d0) 3
  let b8 := rotK (s.a16 ^^^ d1) 45
  let b9 := rotK (s.a22 ^^^ d2) 61
  let n9 := ~~~b9
  let e5 := b5 ^^^ (b6 ||| b7)
  let e6 := b6 ^^^ (b7 &&& b8)
  let e7 := b7 ^^^ (b8 ||| n9)
  let e8 := b8 ^^^ (b9 ||| b5)
  let e9 := b9 ^^^ (b5 &&& b6)
  let b10 := rotK (s.a1 ^^^ d1) 1
  let b11 := rotK (s.a7 ^^^ d2) 6
  let b12 := rotK (s.a13 ^^^ d3) 25
  let b13 := rotK (s.a19 ^^^ d4) 8
  let b14 := rotK (s.a20 ^^^ d0) 18
  let n13 := ~~~b13
  let e10 := b10 ^^^ (b11 ||| b12)
  let e11 := b11 ^^^ (b12 &&& b13)
  let e12 := b12 ^^^ (n13 &&& b14)
  let e13 := n13 ^^^ (b14 ||| b10)
  let e14 := b14 ^^^ (b10 &&& b11)
  let b15 := rotK (s.a4 ^^^ d4) 27
  let b16 := rotK (s.a5 ^^^ d0) 36
  let b17 := rotK (s.a11 ^^^ d1) 10
  let b18 := rotK (s.a17 ^^^ d2) 15
  let b19 := rotK (s.a23 ^^^ d3) 56
  let n18 := ~~~b18
  let e15 := b15 ^^^ (b16 &&& b17)
  let e16 := b16 ^^^ (b17 ||| b18)
  let e17 := b17 ^^^ (n18 ||| b19)
  let e18 := n18 ^^^ (b19 &&& b15)
  let e19 := b19 ^^^ (b15 ||| b16)
  let b20 := rotK (s.a2 ^^^ d2) 62
  let b21 := rotK (s.a8 ^^^ d3) 55
  let b22 := rotK (s.a14 ^^^ d4) 39
  let b23 := rotK (s.a15 ^^^ d0) 41
  let b24 := rotK (s.a21 ^^^ d1) 2
  let n21 := ~~~b21
  let e20 := b20 ^^^ (n21 &&& b22)
  let e21 := n21 ^^^ (b22 ||| b23)
  let e22 := b22 ^^^ (b23 &&& b24)
  let e23 := b23 ^^^ (b24 ||| b20)
  let e24 := b24 ^^^ (b20 &&& b21)
  ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
    e20, e21, e22, e23, e24⟩

/-- The round constants of rounds 1 to 22 (`Keccak.rc` without its first and last). -/
def rcInner : List UInt64 := [0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001]

/-- `roundC` for each constant of `cs`, two per iteration, the 25 lanes passed as words: rounds 1
to 22 of `permF`. `check'` does not run it; `chainLoop` runs the rounds of every step. -/
def roundsC (cs : List UInt64) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
    a19 a20 a21 a22 a23 a24 : UInt64) : S25 :=
  match cs with
  | [] => ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
      a19, a20, a21, a22, a23, a24⟩
  | [c0] => roundC ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
      a17, a18, a19, a20, a21, a22, a23, a24⟩ c0
  | c0 :: c1 :: cs =>
    let s := roundC (roundC ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24⟩ c0) c1
    roundsC cs s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12 s.a13 s.a14
      s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24

/-- `Keccak-f[1600]` on the 25 lanes, equal to `Keccak.keccakFF` (`permF_eq`): the first and last
rounds written out and rounds 1 to 22 as one loop (`roundsC`), all on complemented lanes
(`complL`). `chainLoop` runs the same rounds in the same order for every step. -/
@[inline] def permF (s : S25) : S25 :=
  let s := roundC (complL s) 0x0000000000000001
  let s := roundsC rcInner s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12
    s.a13 s.a14 s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24
  complL (roundC s 0x8000000080008008)

/-- **One chain step in lanes**: the permutation of the padded block, lanes 0 to 3. This is the
step that L2 and L3 name (`toH4_chainStepF`, `chainEndH4_succ`); `chainEndH4` runs `n` of them. -/
def stepH4 (h : H4) : H4 :=
  let s := permF (blockH4 h)
  ⟨s.a0, s.a1, s.a2, s.a3⟩

/-- **The chain loop**: the rounds `cs` of the current step on its 25 lanes, passed as words (four
per iteration while four remain, then two, then one), then the step's last round, then `n` more
steps, each a block of the four output lanes, its first round and `rcInner`. Steps and rounds
are one tail recursion, so that the compiled loop keeps the lanes unboxed, hands no state from
one step to the next and allocates only the final digest. -/
def chainLoop (n : ℕ) (cs : List UInt64) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
    a17 a18 a19 a20 a21 a22 a23 a24 : UInt64) : H4 :=
  match cs with
  | [] =>
    let s := complL (roundC ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24⟩ 0x8000000080008008)
    match n with
    | 0 => ⟨s.a0, s.a1, s.a2, s.a3⟩
    | n + 1 =>
      let s := roundC (complL (blockH4 ⟨s.a0, s.a1, s.a2, s.a3⟩)) 0x0000000000000001
      chainLoop n rcInner s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12 s.a13
        s.a14 s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24
  | c0 :: c1 :: c2 :: c3 :: cs =>
    let s := roundC (roundC (roundC (roundC ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24⟩ c0) c1) c2) c3
    chainLoop n cs s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12 s.a13 s.a14
      s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24
  | c0 :: c1 :: cs =>
    let s := roundC (roundC ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24⟩ c0) c1
    chainLoop n cs s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12 s.a13 s.a14
      s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24
  | c0 :: cs =>
    let s := roundC ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
      a18, a19, a20, a21, a22, a23, a24⟩ c0
    chainLoop n cs s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12 s.a13 s.a14
      s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24
termination_by (n, cs.length)

/-- `n` chain steps in lanes: the first step's block and first round, then `chainLoop`
(`chainEndH4_succ`: `stepH4`, then the remaining steps). -/
def chainEndH4 (h : H4) : ℕ → H4
  | 0 => h
  | n + 1 =>
    let s := roundC (complL (blockH4 h)) 0x0000000000000001
    chainLoop n rcInner s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12 s.a13
      s.a14 s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24

/-! ## The proof format on byte arrays

The proof of a witness is the bytes of its words (`WitnessSending.encode`, from `witWords` and
`wordsBytes`, `Library/Words.lean`). Every field starts on an 8-byte boundary: a number is one
little-endian word, a digest is its 32 bytes, and a byte string is its length word, its bytes and
zero bytes up to the next boundary. -/

/-- Push `k` zero bytes. -/
def pushZeros (b : ByteArray) : ℕ → ByteArray
  | 0 => b
  | k + 1 => pushZeros (b.push 0) k

/-- Push a byte string as `bytesWords` writes it: its length, its bytes, then zero bytes up to
the next multiple of 8. -/
def pushString (b x : ByteArray) : ByteArray :=
  pushZeros (pushU64 b x.size ++ x) ((8 - x.size % 8) % 8)

/-- Push a trace as `logWords` writes it: the number of entries, then each entry's query and
answer. -/
def pushTrace (b : ByteArray) (tr : Trace) : ByteArray :=
  tr.foldl (fun b e => pushDigest (pushString b e.1) e.2) (pushU64 b tr.length)

/-- Push a signature as `sigWords` writes it: the index, the chain values, the path. -/
def pushSig (b : ByteArray) (σ : Sig) : ByteArray :=
  σ.path.foldl pushDigest (σ.ots.foldl pushDigest (pushU64 b σ.idx))

/-- Push a signed proof as `signedWords` writes it: the proof, the trace, the signature. -/
def pushSigned (b : ByteArray) (p : Signed) : ByteArray :=
  pushSig (pushTrace (pushString b p.π) p.tr) p.σ

/-- **The proof that sends a witness**, built in a byte array (`WitnessSending.encode`). The
capacity covers a node whose children have empty traces. -/
def encodeB : Wit → ByteArray
  | .leaf s n => pushU64 (pushDigest (pushU64 (ByteArray.emptyWithCapacity 48) 0) s) n
  | .node c₁ c₂ p₁ p₂ =>
    pushSigned (pushSigned (pushDigest (pushDigest (pushU64
      (ByteArray.emptyWithCapacity (p₁.π.size + p₂.π.size + 9672)) 1) c₁) c₂) p₁) p₂

/-- The little-endian word of the 8 bytes from byte `i`. -/
def u64At (b : ByteArray) (i : ℕ) (h : i + 8 ≤ b.size) : UInt64 :=
  b[i].toUInt64 ||| b[i + 1].toUInt64 <<< 8 ||| b[i + 2].toUInt64 <<< 16 |||
    b[i + 3].toUInt64 <<< 24 ||| b[i + 4].toUInt64 <<< 32 ||| b[i + 5].toUInt64 <<< 40 |||
    b[i + 6].toUInt64 <<< 48 ||| b[i + 7].toUInt64 <<< 56

/-- A number from byte `i`, as `readNat` reads it: the value of its word, and the index after
it. -/
def rdNat (b : ByteArray) (i : ℕ) : Option (ℕ × ℕ) :=
  if h : i + 8 ≤ b.size then some ((u64At b i h).toNat, i + 8) else none

/-- The digest of the 32 bytes from byte `i`. -/
def digestAt (b : ByteArray) (i : ℕ) (h : i + 32 ≤ b.size) : Digest :=
  Vector.ofFn fun j => b[i + j.val]'(by have := j.isLt; omega)

/-- The `k` digests of the `32 · k` bytes from byte `i`. -/
def digestsAt (b : ByteArray) : (i k : ℕ) → i + 32 * k ≤ b.size → List Digest
  | _, 0, _ => []
  | i, k + 1, h => digestAt b i (by omega) :: digestsAt b (i + 32) k (by omega)

/-- A digest from byte `i`, as `readDigest` reads it. -/
def rdDigest (b : ByteArray) (i : ℕ) : Option (Digest × ℕ) :=
  if h : i + 32 ≤ b.size then some (digestAt b i h, i + 32) else none

/-- `k` digests from byte `i`, as `readList readDigest k` reads them. -/
def rdDigests (b : ByteArray) (i k : ℕ) : Option (List Digest × ℕ) :=
  if h : i + 32 * k ≤ b.size then some (digestsAt b i k h, i + 32 * k) else none

/-- A byte string from byte `i`, as `readString` reads it: its length word, then its bytes (a
slice of `b`), then its padding up to the next word, which is skipped and not read. -/
def rdString (b : ByteArray) (i : ℕ) : Option (ByteArray × ℕ) := do
  let (n, j) ← rdNat b i
  let e := j + 8 * ((n + 7) / 8)
  if e ≤ b.size then some (b.extract j (j + n), e) else none

/-- A trace entry from byte `i`, as `readEntry` reads it: the query, then the answer. -/
def rdEntry (b : ByteArray) (i : ℕ) : Option ((ByteArray × Digest) × ℕ) := do
  let (q, i) ← rdString b i
  let (a, i) ← rdDigest b i
  return ((q, a), i)

/-- `k` trace entries from byte `i`, after the entries `acc` (the last one read first). -/
def rdEntries (b : ByteArray) : ℕ → ℕ → Trace → Option (Trace × ℕ)
  | 0, i, acc => some (acc.reverse, i)
  | k + 1, i, acc =>
    match rdEntry b i with
    | some (e, j) => rdEntries b k j (e :: acc)
    | none => none

/-- A signature from byte `i`, as `readSig` reads it. -/
def rdSig (b : ByteArray) (i : ℕ) : Option (Sig × ℕ) := do
  let (idx, i) ← rdNat b i
  let (ots, i) ← rdDigests b i wotsLen
  let (path, i) ← rdDigests b i sigHeight
  return (⟨idx, ots, path⟩, i)

/-- A signed proof from byte `i`, as `readSigned` reads it. -/
def rdSigned (b : ByteArray) (i : ℕ) : Option (Signed × ℕ) := do
  let (π, i) ← rdString b i
  let (m, i) ← rdNat b i
  let (tr, i) ← rdEntries b m i []
  let (σ, i) ← rdSig b i
  return (⟨π, tr, σ⟩, i)

/-- **The witness a proof sends, read in place**: one level, the children's proofs as slices.
Like `decodeWit`, it reads fields strictly and ignores the padding bytes and whatever follows the
last field; `check'` re-encodes the witness, which rejects both. -/
def parseB (b : ByteArray) : Option Wit := do
  let (tag, i) ← rdNat b 0
  match tag with
  | 0 =>
    let (s, i) ← rdDigest b i
    let (n, _) ← rdNat b i
    return .leaf s n
  | 1 =>
    let (c₁, i) ← rdDigest b i
    let (c₂, i) ← rdDigest b i
    let (p₁, i) ← rdSigned b i
    let (p₂, _) ← rdSigned b i
    return .node c₁ c₂ p₁ p₂
  | _ => none

/-! ## The decision -/

/-- **The decision**: the library's `WitnessSending.check`, with the proof read by `parseB`
and compared with `encodeB` of what was read, the leaf's chain computed in lanes, and the
children decided by `check'`. Each child's proof must be shorter than `π`, the termination
measure; the children of every encoding are (`WitnessSending.size_child_lt`). -/
def check' (vk c : Digest) (π : Proof) : Bool :=
  match parseB π with
  | some (.leaf s n) =>
    decide (encodeB (.leaf s n) = π) && decide (n ≤ chainCap) &&
      decide (c = leafStmtF (ofH4 (chainEndH4 (toH4 s) n)) n)
  | some (.node c₁ c₂ p₁ p₂) =>
    if _h : p₁.π.size < π.size ∧ p₂.π.size < π.size then
      if encodeB (.node c₁ c₂ p₁ p₂) = π then
        decide (c = nodeStmtF c₁ c₂) &&
          (decide (p₁.π.size < 2 ^ 64) && decide (p₁.tr.length ≤ 0) &&
            decide (∀ e ∈ p₁.tr, e.1.size ≤ queryCap) &&
            SigOkF vk (traceDigestF p₁.tr) p₁.σ &&
            (p₁.tr.isEmpty && check' vk c₁ p₁.π)) &&
          (decide (p₂.π.size < 2 ^ 64) && decide (p₂.tr.length ≤ 0) &&
            decide (∀ e ∈ p₂.tr, e.1.size ≤ queryCap) &&
            SigOkF vk (traceDigestF p₂.tr) p₂.σ &&
            (p₂.tr.isEmpty && check' vk c₂ p₂.π))
      else false
    else false
  | none => false
termination_by π.size
decreasing_by
  · exact _h.1
  · exact _h.2

/-- The verifier: `check'`, with no oracle query. -/
def V' (vk c : Digest) (π : Proof) : OProg Bool := .ret (check' vk c π)

end RecursionFast.FastCheck
