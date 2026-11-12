import LvmSchedule
import RecursionFast.Library.Fast

/-!
# `V_S`'s parse and query driver (BLUEPRINT §2.1, §2.2, §5 steps 1–2; §11 A1, A3)

**Parse** (`parseOk`, before any query). The `S` proof is

```
'S' pad[7] | b u64 | vk[32] | c_L[32] | s[32] | n u64 | h[32] | σ_leaf (idx u64 ‖ 133×32 ‖ 16×32)
| body: the prover messages in schedule order
```
(header 5,624 B, `headerBytes`). `V_S` rejects unless `|π| = piSize`, `π[0] = 'S'` and the pad is
zero (bytes 0–7 are in no query, so `reassemble` needs them constant), `b ∈ {0, 1}` (A3), the
copy of `vk` is the argument, `1 ≤ n ≤ 2^20` (A1) and `n ≤ 2^logN` (the chain table's height:
the same bound at `P20`, the test set's smaller table at `P8`), and

* `b = 0`: `c_L` and `σ_leaf` are zero bytes and `c = leafStmt h n`;
* `b = 1`: `c = nodeStmt c_L (leafStmt h n)` and `SigOk vk (traceDigest []) σ_leaf`.

The hashes are the Library's fast twins (`Library/Fast.lean`: `leafStmtF`, `nodeStmtF`,
`SigOkF`, `traceDigestF`, each proved equal to the contract's function).

**Drive** (`drive`). `q₀ = "lvm/1\0\0"`; the seed `a₀ ‖ header[8..]`; then the schedule
(`LvmSchedule.schedule`): a `read`/`cap` item moves the body cursor, a `sample` asks `st ‖
pending` (the pending bytes are the body bytes since the last FS query: one slice of π), a
`positions` item asks `⌈t/8⌉` such queries (8 positions of `height` bits per answer, low
first), an `opening` item asks per position the leaf query (the row) and the node queries
`left ‖ right` (the current node is the left child iff the position's bit at that level is 0),
then compares the top with the cap node `pos >> path` (a comparison, not a query). A cap mismatch
rejects at once. A level whose leaf row exceeds the contract's `queryCap` is rejected (WP-11b, A15). Opened rows and siblings are never absorbed by an FS query (the next one starts
after them). On every accepting path the driver asks exactly `qS p` queries
(`LvmSchedule.qS`; the compiled test checks it).

**The stream** (`streamOf`). The driver records its trace and hands the decision `F` the bytes
`Σ = tagTrace ‖ traceBytes tr` (`Library/Fast.lean`'s `traceBytesB`, equal to
`tagTrace :: traceBytes tr`): BLUEPRINT §2.2's stream, a whole number of lanes. `F` reads every
message, challenge, position and row out of `Σ` at the offsets the schedule fixes (`LvmDecide*`).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-! ## Bytes -/

/-- The number with the 8 little-endian bytes of `b` at `o` (`get!`: a byte beyond the end reads
as 0; the callers check sizes first). -/
def u64At (b : ByteArray) (o : Nat) : Nat :=
  let g (i : Nat) : UInt64 := (b.get! (o + i)).toUInt64 <<< (8 * i).toUInt64
  (g 0 ||| g 1 ||| g 2 ||| g 3 ||| g 4 ||| g 5 ||| g 6 ||| g 7).toNat

/-- The 32 bytes of `b` at `o` as a digest (`get!`, as `u64At`). -/
def digestAt (b : ByteArray) (o : Nat) : Digest := Vector.ofFn fun i => b.get! (o + i.val)

/-- A digest's bytes as a byte array. -/
def digestBytes (d : Digest) : ByteArray := ⟨d.toArray⟩

/-- Every byte of `b` in `[o, o + n)` is zero. -/
def zeroBytes (b : ByteArray) (o : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => b.get! o == 0 && zeroBytes b (o + 1) n

/-- The all-zero digest. -/
def zeroDigest : Digest := Vector.replicate 32 0

/-! ## The header (BLUEPRINT §2.1) -/

/-- Byte offsets of the header fields in π. -/
def offB : Nat := 8
/-- Offset of the `vk` copy. -/
def offVk : Nat := 16
/-- Offset of `c_L`. -/
def offCL : Nat := 48
/-- Offset of the chain start `s`. -/
def offS : Nat := 80
/-- Offset of the chain length `n`. -/
def offN : Nat := 112
/-- Offset of the chain end `h`. -/
def offH : Nat := 120
/-- Offset of `σ_leaf`. -/
def offSig : Nat := 152

/-- The fields of an `S` header. -/
structure Header where
  /-- The flag: 0 a leaf statement, 1 a node statement. -/
  b : Nat
  /-- The copy of the public key. -/
  vk : Digest
  /-- The left child's statement (`b = 1`). -/
  cL : Digest
  /-- The chain start. -/
  s : Digest
  /-- The chain length. -/
  n : Nat
  /-- The chain end. -/
  h : Digest
  /-- The leaf signature on `traceDigest []` (`b = 1`). -/
  sig : Sig

/-- The signature at byte `o`: `idx u64 ‖ 133 chain values ‖ 16 siblings`. -/
def sigAt (b : ByteArray) (o : Nat) : Sig :=
  ⟨u64At b o, (List.range wotsLen).map fun k => digestAt b (o + 8 + 32 * k),
    (List.range sigHeight).map fun k => digestAt b (o + 8 + 32 * wotsLen + 32 * k)⟩

/-- The header of a proof (meaningful once `|π| ≥ headerBytes`). -/
def Header.ofProof (π : ByteArray) : Header :=
  ⟨u64At π offB, digestAt π offVk, digestAt π offCL, digestAt π offS, u64At π offN,
    digestAt π offH, sigAt π offSig⟩

/-- The chain's statement `leafStmt h n`. -/
def Header.leaf (hd : Header) : Digest := leafStmtF hd.h hd.n

/-- **The statement an `S` header proves**: `leafStmt h n` (`b = 0`) or
`nodeStmt c_L (leafStmt h n)` (`b = 1`). -/
def Header.stmt (hd : Header) : Digest :=
  if hd.b = 0 then hd.leaf else nodeStmtF hd.cL hd.leaf

/-- **The native checks of step 1** (BLUEPRINT §5, §11 A1, A3), in order of cost. -/
def parseOk (p : Params) (vk c : Digest) (π : ByteArray) : Bool :=
  π.size == piSize p && π.get! 0 == 0x53 && zeroBytes π 1 7 &&
    let hd := Header.ofProof π
    (hd.b == 0 || hd.b == 1) && hd.vk == vk && 1 ≤ hd.n && hd.n ≤ chainCap && hd.n ≤ 2 ^ p.logN &&
    (if hd.b = 0 then hd.cL == zeroDigest && zeroBytes π offSig sigBytes && c == hd.stmt
     else c == hd.stmt && SigOkF vk (traceDigestF []) hd.sig)

/-! ## The driver -/

/-- The driver's state. -/
structure DSt where
  /-- The next unread body byte of π. -/
  off : Nat
  /-- The first body byte not yet absorbed by an FS query. -/
  pend : Nat
  /-- The Fiat–Shamir state: the last FS answer. -/
  st : Digest
  /-- The trace so far, newest entry first. -/
  log : List (ByteArray × Digest)
  /-- The π offset of each cap read so far. -/
  caps : List (Ref × Nat)
  /-- The current oracle's positions. -/
  pos : List Nat

/-- The challenge bits of an answer: lanes 0–2 as one 192-bit number, lane 0 lowest. -/
def answerBits (a : Digest) : Nat :=
  let b := digestBytes a
  u64At b 0 + 2 ^ 64 * u64At b 8 + 2 ^ 128 * u64At b 16

/-- Ask `q`, logging the entry. -/
@[inline] def ask (q : ByteArray) (s : DSt) (k : DSt → Digest → OProg Bool) : OProg Bool :=
  .query q fun a => k { s with log := (q, a) :: s.log } a

/-- One FS query `st ‖ pending`; its answer is the new state. -/
@[inline] def fsQuery (π : ByteArray) (s : DSt) (k : DSt → Digest → OProg Bool) : OProg Bool :=
  ask (digestBytes s.st ++ π.extract s.pend s.off) s fun s a => k { s with st := a, pend := s.off } a

/-- The positions of `t` queries of `h` bits: `n` FS queries, `rem` positions still to draw,
8 per answer (BLUEPRINT §2.2). -/
def posLoop (π : ByteArray) (h : Nat) : (n rem : Nat) → DSt → (DSt → OProg Bool) → OProg Bool
  | 0, _, s, k => k s
  | n + 1, rem, s, k => fsQuery π s fun s a =>
      let cnt := min positionsPerAnswer rem
      let bits := answerBits a
      let ps := (List.range cnt).map fun j => (bits >>> (j * h)) % 2 ^ h
      posLoop π h n (rem - cnt) { s with pos := s.pos ++ ps } k

/-- Walk a Merkle path from the node `cur` of position `q` at level `lvl`: `j` more levels, each
sibling the next 32 body bytes, each step one node query `left ‖ right`. -/
def climb (π : ByteArray) (q : Nat) :
    (j lvl : Nat) → Digest → DSt → (DSt → Digest → OProg Bool) → OProg Bool
  | 0, _, cur, s, k => k s cur
  | j + 1, lvl, cur, s, k =>
    let sib := π.extract s.off (s.off + 32)
    let nodeQ := if (q >>> lvl) % 2 = 0 then digestBytes cur ++ sib else sib ++ digestBytes cur
    ask nodeQ { s with off := s.off + 32 } fun s a => climb π q j (lvl + 1) a s k

/-- Open the oracle of level `L` at each position: the leaf query, the path, the cap check
(the cap read at `capOff`); reject at the first mismatch. -/
def openLoop (π : ByteArray) (L : Level) (capOff : Nat) :
    List Nat → DSt → (DSt → OProg Bool) → OProg Bool
  | [], s, k => k s
  | q :: qs, s, k =>
    ask (π.extract s.off (s.off + L.row)) { s with off := s.off + L.row } fun s leaf =>
      climb π q L.path 0 leaf s fun s top =>
        if top == digestAt π (capOff + nodeBytes * (q >>> L.path)) then openLoop π L capOff qs s k
        else .ret false

/-- The π offset of the cap of `r` (read before its opening; `none` never happens on the
schedule, and the driver rejects if it does). -/
def capOffset (s : DSt) (r : Ref) : Option Nat := (s.caps.find? (·.1 == r)).map (·.2)

/-- **Run the items** of the schedule from the state `s`, then `k`. -/
def driveItems (p : Params) (π : ByteArray) :
    List Item → DSt → (DSt → OProg Bool) → OProg Bool
  | [], s, k => k s
  | .read m :: rest, s, k => driveItems p π rest { s with off := s.off + eBytes * m } k
  | .cap c r :: rest, s, k =>
    driveItems p π rest { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c } k
  | .sample :: rest, s, k => fsQuery π s fun s _ => driveItems p π rest s k
  | .positions r :: rest, s, k =>
    let L := p.level r
    posLoop π L.height L.nPosQ L.t { s with pos := [] } fun s => driveItems p π rest s k
  | .opening r :: rest, s, k =>
    match capOffset s r with
    | none => .ret false
    | some capOff =>
      -- WP-11b-QL (A15): every leaf query of the level is a row of `(p.level r).row` bytes; check it
      -- against the contract's `queryCap` (a static bound, so the check costs nothing).
      if (p.level r).row ≤ queryCap then
        openLoop π (p.level r) capOff s.pos s fun s =>
          driveItems p π rest { s with pend := s.off } k
      else .ret false

/-- **The stream** `Σ = tagTrace ‖ traceBytes tr` of the trace logged newest first. -/
def streamOf (log : List (ByteArray × Digest)) : ByteArray := traceBytesB log.reverse

/-- The first query, `q₀`. -/
def q0Query : ByteArray := ⟨q0Bytes.toArray⟩

/-- The seed query: the salt `a₀` and the header from byte 8. -/
def seedQuery (π : ByteArray) (a₀ : Digest) : ByteArray := digestBytes a₀ ++ π.extract 8 headerBytes

/-- **The driver** (BLUEPRINT §5 step 2): `q₀`, the seed, the schedule; at the end, with the body
used up, the decision `F` on the stream. -/
def drive (p : Params) (π : ByteArray) (F : ByteArray → Bool) : OProg Bool :=
  .query q0Query fun a₀ =>
    let sq := seedQuery π a₀
    .query sq fun st₀ =>
      driveItems p π (schedule p)
        ⟨headerBytes, headerBytes, st₀, [(sq, st₀), (q0Query, a₀)], [], []⟩
        fun s => .ret (s.off == π.size && F (streamOf s.log))

end Lvm
