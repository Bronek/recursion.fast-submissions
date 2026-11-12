import LvmQSigParts
import LvmWotsMsg
import LvmKSpongeDigests

/-!
# `Q_sig`'s soundness: the hypotheses and conclusions (BLUEPRINT §4.6, §11 A2, A3)

New for lvm (WP-12). The theorem WP-14 consumes:

**`qsig_sound`**: in every memory `M` where `Q_sig`'s rows and assertions hold with the node flag
`1`, given
* `SigKS` — the `KS` rows of the signature schedule: each hash's message lanes are `Q_sig`'s cells
  `xcell o r l` (row `r`, lane `l`; the sponge's byte `q` is byte `q mod 8` of lane `q / 8`), its
  block is a `BlockPerm` from the zero state (the key leaf: 32 linked blocks), and its digest
  cells (`ys`, `yc`, `yls`, `yns`) are the output's first 32 bytes. This is the per-row form of
  WP-8's sponge table (`LvmKSponge`, K2-LS); WP-8's `LvmSpongeTable` turns the KS table relation
  into it;
* `SigBits` — the `BITS` outputs: each output cell is its `BOut` word function of the cell the row
  reads (`LvmBits.row_sound` gives this from a `BITS` row's constraints, the bus gives the read);
* powers of `x` injective below `2^10` (from `GInj`, which `loopir_sound` assumes anyway),

the child's signature `σ'` (`sigAt' M.k I.sg`) on the message digest `m` (`digAt M.k I.md`, which is
`traceDigest tr'` by the KS trace rows) passes the contract's `SigOk` under `vk`, and the child's
header (stream lanes from `I.hd`) passes the native checks of `V_S`'s parse step (`ChildOk`):
`b' ∈ {0,1}`, `vk' = vk`, `1 ≤ n' ≤ 2^20`, `b' = 0 ⇒ c_L' = 0 ∧ σ_leaf' = 0`,
`b' = 1 ⇒ σ_leaf' = σ_leaf` (A2), and `c_L = leafStmt h' n'` (`b' = 0`) or
`nodeStmt c_L' (leafStmt h' n')` (`b' = 1`).
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.KSponge Lvm.Wots

/-! ## Reading digests, signatures and cells -/

/-- The digest whose four lanes are the `K` cells `a … a + 3`. -/
def digAt (v : Nat → FK) (a : Nat) : Digest := digOfW fun l => (v (a + l)).val

/-- The signature whose lanes are the `K` cells from `a`: `idx`, 133 chain values, 16 siblings
(BLUEPRINT §2.1's `σ` layout). -/
def sigAt' (v : Nat → FK) (a : Nat) : Sig :=
  ⟨(v a).val.toNat, (List.range wotsLen).map fun i => digAt v (a + 1 + 4 * i),
    (List.range sigHeight).map fun t => digAt v (a + 533 + 4 * t)⟩

/-- Chain `i`'s template row `t` (message chains `i < 128`, checksum chains `128 … 132`). -/
def chainCell (o : SigOut) (i t : Nat) : Nat :=
  if i < 128 then (o.cm.cell t i).n else ((o.cc.getD (i - 128) dLoop).cell t 0).n

/-- The input of chain `i`'s step `s + 1`, lane `l`: the signed value, then the muxed cells. -/
def xin (I : SigIn) (o : SigOut) (i s l : Nat) : Nat :=
  if s = 0 then I.sg + 1 + 4 * i + l else chainCell o i (8 * s + l)

/-- Chain `i`'s end, lane `l`. -/
def endc (o : SigOut) (i l : Nat) : Nat := chainCell o i (24 + l)

/-- Lane `m < 544` of the key leaf's message. -/
def leafLane (o : SigOut) (m : Nat) : Nat :=
  if m < 2 then (o.msg.la.cell m 0).n
  else if m < 514 then (o.msg.lb.cell 0 (m - 2)).n else (o.msg.lc.cell (m - 514) 0).n

/-- **Lane `l` of `KS` row `r`'s message** (`r < 449`: 399 chain steps, 32 leaf blocks, 16 path
nodes, `leafStmt`, `nodeStmt`). -/
def xcell (o : SigOut) (r l : Nat) : Nat :=
  if r < 384 then (o.msg.xm.cell (17 * (r % 3) + l) (r / 3)).n
  else if r < 399 then ((o.msg.xc.getD ((r - 384) / 3) dLoop).cell (17 * ((r - 384) % 3) + l) 0).n
  else if r < 431 then leafLane o (17 * (r - 399) + l)
  else if r < 447 then (o.msg.xp.cell l (r - 431)).n
  else if r = 447 then (o.msg.xls.cell l 0).n else (o.msg.xns.cell l 0).n

/-- The words of the cells `f l`. -/
def lanesW (v : Nat → FK) (f : Nat → Nat) : Nat → UInt64 := fun l => (v (f l)).val

/-! ## The hypotheses -/

/-- A one-block hash row: its message lanes `x`, its digest cells `y`. -/
def OneHash (v : Nat → FK) (x : Nat → Nat) (y : Nat) : Prop :=
  ∃ s, BlockPerm (xorMsg zeroSt (laneByte (lanesW v x))) s ∧ digAt v y = stDigest s

/-- **The `KS` rows of the signature schedule** (WP-8's sponge table, per row). -/
structure SigKS (I : SigIn) (o : SigOut) (v : Nat → FK) : Prop where
  step : ∀ r < 399, OneHash v (xcell o r) (I.ys + 4 * r)
  leaf : ∃ sIn sOut : Nat → State, sIn 0 = zeroSt ∧
    (∀ u < 32, BlockPerm (xorMsg (sIn u) (laneByte (lanesW v (xcell o (399 + u))))) (sOut u)) ∧
    (∀ u, u + 1 < 32 → sIn (u + 1) = sOut u) ∧ digAt v I.yc = stDigest (sOut 31)
  path : ∀ t < 16, OneHash v (xcell o (431 + t)) (I.yc + 4 * (t + 1))
  ls : OneHash v (xcell o 447) I.yls
  ns : OneHash v (xcell o 448) I.yns

/-- A `BITS` output: cell `c` is the word function `b` of cell `w`. -/
def Out1 (v : Nat → FK) (w : Nat) (b : BOut) (c : Nat) : Prop := v c = w64 (b.word (v w).val)

/-- **The `BITS` outputs `Q_sig` reads** (rows: `σ'.idx`; the message digest's 256 bits; the ten
checksum bits of a free word; every chain step input (`shl 24`/`shr 40`); every chain end, path
node half, `h'`, `c_L'`, `leafStmt` lane (`shl 8`/`shr 56`); `n'`'s parts, bits and range fields). -/
structure SigBits (I : SigIn) (o : SigOut) (v : Nat → FK) : Prop where
  idx_lo : Out1 v I.sg (.shl 8) I.bi
  idx_bit : ∀ z < 16, Out1 v I.sg (.bit z) (I.bi + 1 + z)
  idx_hi : Out1 v I.sg (.shr 16) (I.bi + 17)
  md : ∀ q < 256, Out1 v (I.md + q / 64) (.bit (q % 64)) (I.bd + q)
  cs : ∃ w : UInt64, ∀ k < 10, v (I.bc + k) = w64 ((BOut.bit k).word w)
  x : ∀ i < 133, ∀ s < 3, ∀ l < 4,
    Out1 v (xin I o i s l) (.shl 24) (I.bx + 2 * (4 * (3 * i + s) + l)) ∧
      Out1 v (xin I o i s l) (.shr 40) (I.bx + 2 * (4 * (3 * i + s) + l) + 1)
  e : ∀ i < 133, ∀ l < 4, Out1 v (endc o i l) (.shl 8) (I.be + 2 * (4 * i + l)) ∧
    Out1 v (endc o i l) (.shr 56) (I.be + 2 * (4 * i + l) + 1)
  p : ∀ t < 16, ∀ u < 2, ∀ l < 4,
    Out1 v (o.pa.cell (4 + 4 * u + l) t).n (.shl 8) (I.bp + 2 * (8 * t + 4 * u + l)) ∧
      Out1 v (o.pa.cell (4 + 4 * u + l) t).n (.shr 56) (I.bp + 2 * (8 * t + 4 * u + l) + 1)
  h : ∀ l < 4, Out1 v (I.hd + 14 + l) (.shl 8) (I.bh + 2 * l) ∧
    Out1 v (I.hd + 14 + l) (.shr 56) (I.bh + 2 * l + 1)
  n_lo : Out1 v (I.hd + 13) (.shl 8) I.bn
  n_hi : Out1 v (I.hd + 13) (.shr 56) (I.bn + 1)
  n_bit : ∀ z ≤ I.ln, Out1 v (I.hd + 13) (.bit z) (I.bn + 2 + z)
  n_top : Out1 v (I.hd + 13) (.shr (I.ln + 1)) (I.bn + 2 + I.ln + 1)
  n_low : Out1 v (I.hd + 13) (.shl (64 - I.ln)) (I.bn + 2 + I.ln + 2)
  cl : ∀ l < 4, Out1 v (I.hd + 5 + l) (.shl 8) (I.bcl + 2 * l) ∧
    Out1 v (I.hd + 5 + l) (.shr 56) (I.bcl + 2 * l + 1)
  ls : ∀ l < 4, Out1 v (I.yls + l) (.shl 8) (I.bls + 2 * l) ∧
    Out1 v (I.yls + l) (.shr 56) (I.bls + 2 * l + 1)

/-- The all-zero digest. -/
def zeroDig : Digest := Vector.replicate 32 0

/-- **The child's header passes `V_S`'s native checks** (BLUEPRINT §11 A2, A3; WP-11a `parseOk`):
the stream lanes from `I.hd` are `b'`, `vk'` (4), `c_L'` (4), `s'` (4), `n'`, `h'` (4), `σ_leaf'`
(597); `I.vk`, `I.cL`, `I.sl` are the current proof's `vk`, `c_L`, `σ_leaf`. -/
def ChildOk (I : SigIn) (v : Nat → FK) : Prop :=
  let b := (v I.hd).val.toNat
  let n := (v (I.hd + 13)).val.toNat
  (b = 0 ∨ b = 1) ∧ digAt v (I.hd + 1) = digAt v I.vk ∧ 1 ≤ n ∧ n ≤ 2 ^ I.ln ∧
    (b = 0 → digAt v (I.hd + 5) = zeroDig ∧ ∀ k < 597, v (I.hd + 18 + k) = 0) ∧
    (b = 1 → ∀ k < 597, v (I.hd + 18 + k) = v (I.sl + k)) ∧
    digAt v I.cL = (if b = 0 then leafStmt (digAt v (I.hd + 14)) n
      else nodeStmt (digAt v (I.hd + 5)) (leafStmt (digAt v (I.hd + 14)) n))

end Lvm.QSig
