import LvmQSigLoop
import LvmBits

/-!
# `Q_sig`: the child's signature and header checks as a LoopIR gadget (BLUEPRINT §4.6, §11 A2–A3)

New for lvm (WP-12), written with QL's builder (`LvmQBuild`). FR's WOTS circuit rows
(`FRNodeRows4Wots*`) are BLAKE2s-era `GF(2^128)` rows over FR's own circuit IR; their logic is
followed here (three steps per chain selected by `[d < s]`, the selectors `(1 − b₀)(1 − b₁)`,
`1 − b₁`, `1 − b₀b₁`, the multiplicative checksum `Π g^{3 − dᵢ} = Π g^{2^k c_k}`, the path mux), the
rows are new.

**Inputs** (`SigIn`, `K` cells; WP-14 places them): the node flag `flag` (the gate of every
assertion), `vk`, `c_L`, `σ_leaf` (597 lanes) of the current proof; the child's header in the stream
(`hd` = the lane of `b'`, then `vk'`, `c_L'`, `s'`, `n'`, `h'`, `σ_leaf'`, BLUEPRINT §2.1); the
child's signature `σ'` (`sg`: `idx`, 133 × 4 chain lanes, 16 × 4 path lanes); the message digest
`md` (= `traceDigest tr'`); the `KS` digests (`ys` chain steps `4(3i + s) + l`, `yc` the key leaf
then the 16 path nodes `yc + 4(t + 1)`, `yls`, `yns` the statement hashes); and the `BITS`
outputs (`bi`, `bd`, `bc`, `bx`, `be`, `bp`, `bn`, `bh`, `bcl`, `bls`, laid out in `SigBits`); the
`KS` message input array `xs` (7,633 lanes, A19).

**Rows** (all `K`): constants `Z = 0`, `O = 1`; the table `T[i] = i << 8` (`i < 128`, seven
doubling loops); the 128 message chains (one loop of 28 rows) and the 5 checksum chains; the
checksum factors `x^{3 − dᵢ}`, their product tree, the ten factors `x^{2^k c_k}` and the equality;
the path mux (one loop of 12 rows over 16 levels); the header checks; `σ_leaf' = b'·σ_leaf`
(597 lanes in five loops); then **all message lanes, consecutively** (KS row `r`'s lane `l` is the
`(17 r + l)`-th of them): 399 chain steps, the key leaf (544 lanes), 16 path nodes, `leafStmt`,
`nodeStmt`; finally (A19) the gated equalities of the message lanes with the `KS` message input
array `xs` (`gXeq`).
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-- The input cells of `Q_sig`. -/
structure SigIn where
  flag : Nat
  vk : Nat
  cL : Nat
  sl : Nat
  hd : Nat
  sg : Nat
  md : Nat
  ys : Nat
  yc : Nat
  yls : Nat
  yns : Nat
  bi : Nat
  bd : Nat
  bc : Nat
  bx : Nat
  be : Nat
  bp : Nat
  bn : Nat
  bh : Nat
  bcl : Nat
  bls : Nat
  /-- The `KS` message input array: row `r`'s lane `l` at `xs + 17 r + l` (A19). -/
  xs : Nat
  /-- The child's chain-length bound `n' ≤ 2^ln` (A3; `V_S`'s `parseOk` asks `n ≤ 2^logN`, so
  `ln = logN`: 20 at `P20`, 9 at `P8`; `1 ≤ ln ≤ 62`). WP-11b-QL: a parameter, was `LN = 20`. -/
  ln : Nat

/-- A word as a `K` constant. -/
abbrev w64 (u : UInt64) : FK := ⟨u⟩

/-! ## Templates -/

/-- **One WOTS chain** (28 rows): `b₀ + 1`, `b₁ + 1` (= `[d < 2]`), `[d < 1]`, `[d < 3]`; per lane the
step-2 input `[d < 1]·(out₁ + ots) + ots`, the step-3 input `[d < 2]·(out₂ + ots) + ots`, the end
`[d < 3]·(out₃ + ots) + ots`. -/
def chainTpl (d0 d1 Z O : Opd) (ots o1 o2 o3 : Nat → Opd) : List LRow :=
  [lr 0 1 d0 d0, lr 0 1 d1 d1, mr (.cur 0) (.cur 1) Z, mr d0 d1 O] ++
  (List.range 4).map (fun l => lr 1 0 (o1 l) (ots l)) ++
  (List.range 4).map (fun l => mr (.cur 2) (.cur (4 + l)) (ots l)) ++
  (List.range 4).map (fun l => lr 1 0 (o2 l) (ots l)) ++
  (List.range 4).map (fun l => mr (.cur 1) (.cur (12 + l)) (ots l)) ++
  (List.range 4).map (fun l => lr 1 0 (o3 l) (ots l)) ++
  (List.range 4).map (fun l => mr (.cur 3) (.cur (20 + l)) (ots l))

/-- The 128 message chains' operands (loop over `i`). -/
def chainM (I : SigIn) (Zn On : Nat) : List LRow :=
  chainTpl (oS I.bd 2) (oS (I.bd + 1) 2) (oA Zn) (oA On) (fun l => oS (I.sg + 1 + l) 4)
    (fun l => oS (I.ys + l) 12) (fun l => oS (I.ys + 4 + l) 12) (fun l => oS (I.ys + 8 + l) 12)

/-- Checksum chain `u < 5` (chain `128 + u`; digit bits `c_{2u}`, `c_{2u+1}`). -/
def chainC (I : SigIn) (Zn On u : Nat) : List LRow :=
  chainTpl (oA (I.bc + 2 * u)) (oA (I.bc + 2 * u + 1)) (oA Zn) (oA On)
    (fun l => oA (I.sg + 1 + 4 * (128 + u) + l))
    (fun l => oA (I.ys + 4 * (3 * (128 + u)) + l)) (fun l => oA (I.ys + 4 * (3 * (128 + u) + 1) + l))
    (fun l => oA (I.ys + 4 * (3 * (128 + u) + 2) + l))

/-- The checksum factor of a message chain: `x^{1 − b₀}`, `x^{2(1 − b₁)}`, their product. -/
def csfTpl (I : SigIn) (Zn : Nat) : List LRow :=
  [lr (FK.x + 1) FK.x (oA Zn) (oS I.bd 2), lr (FK.x ^ 2 + 1) (FK.x ^ 2) (oA Zn) (oS (I.bd + 1) 2),
    mr (.cur 0) (.cur 1) (oA Zn)]

/-- One level of a product tree: `y ↦ a[2y]·a[2y+1]`, `a[i]` at `src + st·i`. -/
def ptTpl (src st Zn : Nat) : List LRow := [mr (oS src (2 * st)) (oS (src + st) (2 * st)) (oA Zn)]

/-- One doubling level of the table `T`: `T'[2y + t] = T[y] + t·x^{14 − d}`. -/
def tTpl (d : Nat) (src : Opd) (Zn : Nat) : List LRow :=
  [lr 0 0 src (oA Zn), lr 0 (w64 ((1 : UInt64) <<< (14 - d : Nat).toUInt64)) src (oA Zn)]

/-- The path mux of level `t` (12 rows): `δ = cur + sib`, `l = b·δ + cur`, `r = b·δ + sib`. -/
def pathTpl (I : SigIn) : List LRow :=
  (List.range 4).map (fun l => lr 1 0 (oS (I.yc + l) 4) (oS (I.sg + 533 + l) 4)) ++
  (List.range 4).map (fun l => mr (oS (I.bi + 1) 1) (.cur l) (oS (I.yc + l) 4)) ++
  (List.range 4).map (fun l => mr (oS (I.bi + 1) 1) (.cur l) (oS (I.sg + 533 + l) 4))

/-- `σ_leaf'` lanes `[off, off + 2^d)`: `e = b'·σ_leaf + σ_leaf'`, gated `e = 0`. -/
def slTpl (I : SigIn) (off : Nat) : List LRow :=
  [mr (oA I.hd) (oS (I.sl + off) 1) (oS (I.hd + 18 + off) 1), ar (.cur 0) (oA I.flag)]

/-- Constant lanes `6 … 15` (or from `a`) and the final pad lane `0x80 ‖ …` at byte 135. -/
def zeroLanes (Zn n : Nat) : List LRow := (List.range n).map fun _ => lr 0 0 (oA Zn) (oA Zn)

/-- The last lane of a one-block message: the pad bit `0x80` of byte 135. -/
def padLane (Zn : Nat) : LRow := lr 0 (w64 0x8000000000000000) (oA Zn) (oA Zn)

/-- **A chain step's 17 lanes** (`tagWots ‖ enc64 j ‖ i ‖ s ‖ x`): lane 0 `j << 8 + 0x57`, lane 1
`T + x₀ << 24 + c₁`, lanes 2–4 `x_{k−1} >> 40 + x_k << 24`, lane 5 `x₃ >> 40 + 0x01 << 24`, zeros,
the pad lane. `x`'s parts are `BITS` outputs at `xb + 2k` (`shl 24`) and `+ 1` (`shr 40`). -/
def stepLanes (I : SigIn) (Zn : Nat) (T : Opd) (c1 : UInt64) (xb st : Nat) : List LRow :=
  [lr 0 (w64 0x57) (oA I.bi) (oA I.bi), lr 1 (w64 c1) T (oS xb st),
    lr 1 0 (oS (xb + 1) st) (oS (xb + 2) st), lr 1 0 (oS (xb + 3) st) (oS (xb + 4) st),
    lr 1 0 (oS (xb + 5) st) (oS (xb + 6) st), lr 0 (w64 0x1000000) (oS (xb + 7) st) (oS (xb + 7) st)] ++
  zeroLanes Zn 10 ++ [padLane Zn]

/-- The three steps of a chain (51 lanes). -/
def stepsTpl (I : SigIn) (Zn : Nat) (T : Opd) (c1 : Nat → UInt64) (xb st : Nat) : List LRow :=
  stepLanes I Zn T (c1 0) xb st ++ stepLanes I Zn T (c1 1) (xb + 8) st ++
    stepLanes I Zn T (c1 2) (xb + 16) st

/-- **Two digests after a tag** (65 bytes; `sigNode`, `nodeStmt`): parts of `a` at `aB + 2k`, of `b`
at `bB + 2k` (`shl 8`, then `shr 56`). -/
def twoLanes (Zn : Nat) (tag : UInt64) (aB bB st : Nat) : List LRow :=
  [lr 0 (w64 tag) (oS aB st) (oS aB st)] ++
  (List.range 3).map (fun k => lr 1 0 (oS (aB + 2 * k + 1) st) (oS (aB + 2 * k + 2) st)) ++
  [lr 1 0 (oS (aB + 7) st) (oS bB st)] ++
  (List.range 3).map (fun k => lr 1 0 (oS (bB + 2 * k + 1) st) (oS (bB + 2 * k + 2) st)) ++
  [lr 0 (w64 0x100) (oS (bB + 7) st) (oS (bB + 7) st)] ++ zeroLanes Zn 7 ++ [padLane Zn]

/-- **`leafStmt`'s 17 lanes** (`tagLeaf ‖ h' ‖ enc64 n'`). -/
def leafStmtLanes (I : SigIn) (Zn : Nat) : List LRow :=
  [lr 0 (w64 0x4C) (oA I.bh) (oA I.bh)] ++
  (List.range 3).map (fun k => lr 1 0 (oA (I.bh + 2 * k + 1)) (oA (I.bh + 2 * k + 2))) ++
  [lr 1 0 (oA (I.bh + 7)) (oA I.bn), lr 0 (w64 0x100) (oA (I.bn + 1)) (oA (I.bn + 1))] ++
  zeroLanes Zn 10 ++ [padLane Zn]

/-- The key leaf's lanes 0, 1. -/
def leafA (I : SigIn) : List LRow :=
  [lr 0 (w64 0x4B) (oA I.bi) (oA I.bi), lr 0 0 (oA I.be) (oA I.be)]

/-- The key leaf's lanes `2 + m` (`m < 512`): `E_m >> 56 + E_{m+1} << 8`. -/
def leafB (I : SigIn) : List LRow := [lr 1 0 (oS (I.be + 1) 2) (oS (I.be + 2) 2)]

/-- The key leaf's lanes 514 … 543. -/
def leafC (I : SigIn) (Zn : Nat) : List LRow :=
  (List.range 19).map (fun k => lr 1 0 (oA (I.be + 2 * (512 + k) + 1)) (oA (I.be + 2 * (513 + k)))) ++
  [lr 0 (w64 0x100) (oA (I.be + 2 * 531 + 1)) (oA (I.be + 2 * 531 + 1))] ++
  zeroLanes Zn 9 ++ [padLane Zn]

/-- Message lanes `[off, off + 2^d)`: `e = x[x0 + j] + xs[j]`, gated `e = 0` (A19). -/
def xeqTpl (I : SigIn) (x0 off : Nat) : List LRow :=
  [lr 1 0 (oS (x0 + off) 1) (oS (I.xs + off) 1), ar (.cur 0) (oA I.flag)]

/-! ## The gadget -/

/-- A product chain `acc · q₁ · q₂ ⋯` (`mad` with the zero cell). -/
def prodChain (Z : Cell) : Cell → List Cell → BM Cell
  | acc, [] => pure acc
  | acc, q :: qs => do
    let a ← mad acc q Z
    prodChain Z a qs

/-- The checksum side: `acc · Π_{j < n} x^{2^{k+j} c_{k+j}}` (factors `(x^{2^k} + 1)·c_k + 1`). -/
def cbitsGo (I : SigIn) (Z : Cell) : Nat → Nat → Cell → BM Cell
  | _, 0, acc => pure acc
  | k, n + 1, acc => do
    let g ← lin .K (FK.x ^ (2 ^ k) + 1) 1 Z (kc (I.bc + k))
    let a ← mad acc g Z
    cbitsGo I Z (k + 1) n a

/-- The ten checksum bit factors' product, from the one cell. -/
def cbits (I : SigIn) (Z O : Cell) : BM Cell := cbitsGo I Z 0 10 O

/-- The header checks (A3): `vk' = vk`, the root is `vk`, `b' ∈ {0,1}`, `b' = 0 ⇒ c_L' = 0`,
`1 ≤ n' ≤ 2^ln`, and the statement: `c_L = b' ? nodeStmt : leafStmt`. -/
def header (I : SigIn) (Z : Cell) (O : Cell) : BM Unit := do
  let g := kc I.flag
  let _ ← forN 4 fun l => assertEq (kc (I.hd + 1 + l)) (kc (I.vk + l)) g
  let _ ← forN 4 fun l => assertEq (kc (I.yc + 64 + l)) (kc (I.vk + l)) g
  let bb ← mad (kc I.hd) (kc I.hd) (kc I.hd)
  assert0 bb g
  let nb ← addK (kc I.hd) 1
  let g0 ← mad nb g Z
  let _ ← forN 4 fun l => assert0 (kc (I.hd + 5 + l)) g0
  assert0 (kc (I.bn + 2 + I.ln + 1)) g
  let p ← mad (kc (I.bn + 2 + I.ln)) (kc (I.bn + 2 + I.ln + 2)) Z
  assert0 p g
  let qs ← forN (I.ln + 1) fun z => addK (kc (I.bn + 2 + z)) 1
  let acc ← match qs with
    | [] => pure O
    | q :: rest => prodChain Z q rest
  assert0 acc g
  let _ ← forN 4 fun l => do
    let dl ← add (kc (I.yns + l)) (kc (I.yls + l))
    let sel ← mad (kc I.hd) dl (kc (I.yls + l))
    assertEq sel (kc (I.cL + l)) g
  pure ()

/-- Constants and the table `T[i] = i << 8` (`i < 128`). -/
def gPre (I : SigIn) : BM (Cell × Cell × List LoopOut) := do
  let Z ← const .K 0 (kc I.flag)
  let O ← const .K 1 (kc I.flag)
  let t0 ← loop [0] (tTpl 0 (oA Z.n) Z.n)
  let t1 ← loop [1] (tTpl 1 (oS t0.p.k 1) Z.n)
  let t2 ← loop [2] (tTpl 2 (oS t1.p.k 1) Z.n)
  let t3 ← loop [3] (tTpl 3 (oS t2.p.k 1) Z.n)
  let t4 ← loop [4] (tTpl 4 (oS t3.p.k 1) Z.n)
  let t5 ← loop [5] (tTpl 5 (oS t4.p.k 1) Z.n)
  let t6 ← loop [6] (tTpl 6 (oS t5.p.k 1) Z.n)
  pure (Z, O, [t0, t1, t2, t3, t4, t5, t6])

/-- The checksum: factors, product tree, the ten bit factors, the equality. -/
def gCheck (I : SigIn) (Z O : Cell) : BM (LoopOut × List LoopOut × Cell) := do
  let cs ← loop [7] (csfTpl I Z.n)
  let p6 ← loop [6] (ptTpl (cs.p.k + 2) 3 Z.n)
  let p5 ← loop [5] (ptTpl p6.p.k 1 Z.n)
  let p4 ← loop [4] (ptTpl p5.p.k 1 Z.n)
  let p3 ← loop [3] (ptTpl p4.p.k 1 Z.n)
  let p2 ← loop [2] (ptTpl p3.p.k 1 Z.n)
  let p1 ← loop [1] (ptTpl p2.p.k 1 Z.n)
  let p0 ← loop [0] (ptTpl p1.p.k 1 Z.n)
  let cq ← cbits I Z O
  assertEq (p0.cell 0 0) cq (kc I.flag)
  pure (cs, [p6, p5, p4, p3, p2, p1, p0], cq)

/-- `σ_leaf' = b'·σ_leaf`, gated (597 lanes). -/
def gSl (I : SigIn) : BM Unit := do
  let _ ← loop [9] (slTpl I 0)
  let _ ← loop [6] (slTpl I 512)
  let _ ← loop [4] (slTpl I 576)
  let _ ← loop [2] (slTpl I 592)
  let _ ← loop [0] (slTpl I 596)
  pure ()

/-- **The message lanes are the `KS` inputs** (A19): `x[x0 + j] = xs[j]`, gated, for `j < 7633`
(`7633 = 4096 + 2048 + 1024 + 256 + 128 + 64 + 16 + 1`). -/
def gXeq (I : SigIn) (x0 : Nat) : BM Unit := do
  let _ ← loop [12] (xeqTpl I x0 0)
  let _ ← loop [11] (xeqTpl I x0 4096)
  let _ ← loop [10] (xeqTpl I x0 6144)
  let _ ← loop [8] (xeqTpl I x0 7168)
  let _ ← loop [7] (xeqTpl I x0 7424)
  let _ ← loop [6] (xeqTpl I x0 7552)
  let _ ← loop [4] (xeqTpl I x0 7616)
  let _ ← loop [0] (xeqTpl I x0 7632)
  pure ()

/-- The messages' loops, in KS row order. -/
structure MsgOut where
  xm : LoopOut
  xc : List LoopOut
  la : LoopOut
  lb : LoopOut
  lc : LoopOut
  xp : LoopOut
  xls : LoopOut
  xns : LoopOut

/-- All message lanes, consecutively. -/
def gMsg (I : SigIn) (Zn Tb : Nat) : BM MsgOut := do
  let xm ← loop [7] (stepsTpl I Zn (oS Tb 1) (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24)
  let xc ← forN 5 fun u => loop [] (stepsTpl I Zn (oA Zn)
    (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
    (I.bx + 24 * (128 + u)) 0)
  let la ← loop [] (leafA I)
  let lb ← loop [9] (leafB I)
  let lc ← loop [] (leafC I Zn)
  let xp ← loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16)
  let xls ← loop [] (leafStmtLanes I Zn)
  let xns ← loop [] (twoLanes Zn 0x4E I.bcl I.bls 0)
  pure ⟨xm, xc, la, lb, lc, xp, xls, xns⟩

/-- What `Q_sig` returns. -/
structure SigOut where
  pre : Cell × Cell × List LoopOut
  cm : LoopOut
  cc : List LoopOut
  ck : LoopOut × List LoopOut × Cell
  pa : LoopOut
  msg : MsgOut
  /-- The first message lane (KS row `r`'s lane `l` is the cell `x0 + 17 r + l`). -/
  x0 : Nat

/-- The cell of `T[0]` (the last doubling level). -/
def Tbase (pre : Cell × Cell × List LoopOut) : Nat := (pre.2.2.getD 6 ⟨⟨0, 0⟩, [], []⟩).p.k

/-- **`Q_sig`.** -/
def qsig (I : SigIn) : BM SigOut := do
  let pre ← gPre I
  let cm ← loop [7] (chainM I pre.1.n pre.2.1.n)
  let cc ← forN 5 fun u => loop [] (chainC I pre.1.n pre.2.1.n u)
  let ck ← gCheck I pre.1 pre.2.1
  let pa ← loop [4] (pathTpl I)
  header I pre.1 pre.2.1
  assert0 (kc (I.bi + 17)) (kc I.flag)
  gSl I
  let px ← getPtr
  let msg ← gMsg I pre.1.n (Tbase pre)
  gXeq I px.k
  pure ⟨pre, cm, cc, ck, pa, msg, px.k⟩

end Lvm.QSig
