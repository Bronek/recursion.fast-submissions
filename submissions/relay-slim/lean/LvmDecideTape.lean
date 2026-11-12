-- New for lvm2 (WP T-V, stage S2): V_S's tape (T1–T2) and wire (T3–T5) phases on the reader `DM`
-- (lvm2 BLUEPRINT2 §1.2, §2.2; FRZ-0's schedule; T-P1's "Conventions").
import LvmDecideV0

/-!
# The decision `F`: the tape and the wire (lvm2 stage S2)

The chain digest-only tape replaces v1's `CH` and `CH` link phases (BLUEPRINT2 §2.2).

* **Tape** (`dTape`; T1, T2): the instance point `r ∈ E^logN`, the 25 output scalars `a_l`
  (`a_0 … a_3` are `D̃_l(r)`, the rest free, BLUEPRINT2 §1.5), then leanVM's `verify_keccak` with
  `Shape { logN, 24 }` (one segment): five lane challenges, the first claim (`tapeFirstClaimF`, no
  segment factor, no committed output) and 24 layers (`verifyKeccakLayerG`, v1's layer with the
  depth and the segment count as parameters). No opening. The result is the input claim
  `C_in = Σ_i ι(i)·⟨ω, in(i)⟩` (T-G's `claimTrue_tapeStates`). This is T-G's `tapeGkr` in its flat
  form `tapeGkr_eq`, over `FE`.
* **Wire** (`dWire`; T3, T4): T-W's `wireChProg` over `FE`, read for read: the wiring sumcheck from
  `wireTargetF` (`C_in + ι(0)·⟨ω, Pad43(s)⟩ + ⟨ω, c43⟩·Σ_{i ≤ m} ι(i) + ⟨ω, c43⟩·ι(0)`) over the
  `logN` row variables, `g_D`, the check `final = K̃_ch(σ)·g_D` (`msEvalF`), then `D`'s slot
  reduction (two rounds over the lane bits), the 64 slices, the slot check, and the ring switch at
  `σ ‖ τ ‖ sel(dsel)` on `C_main`.
* **Claims** (`tapeClaims`; T1, T4, T5, T-P1's C.7 order): the four word claims `D̃_l(r) = a_l`, the
  ring-switched slices, the four boundary claims `D̃_l(bits(m)) = h_l`.

The `FE` twins of T-K's evaluators (`eqAtF`, `iotaF`, `msEvalF`, `thrEvalF`) and of T-W's dot
products (`padDotF`, `c43DotF`, `slotWF`) are transcriptions; `LvmVEqWire` proves them equal to
the originals through `FE.toExt3`.
-/

set_option autoImplicit false

namespace Lvm

open DM

/-! ## The generic Keccak layer (T-G's `verifyKeccakLayerS` over `FE`) -/

/-- `verify_layer` for `segs` segments of `depth` rounds: v1's `verifyKeccakLayer` with
`gkrSegments`, `gkrDepth` as parameters (T-G's `verifyKeccakLayerS ⟨depth, segs⟩`). -/
def verifyKeccakLayerG (depth segs logSteps step : Nat) (claim : KeccakClaim) : DM KeccakClaim := do
  let packLog := logSteps - 4
  let product ← readEs productBits
  let projected := sumE ((List.range productBits).map fun c =>
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) =>
      if mask.testBit c then some m else none) * product.getD c 0)
  let segments := eqKernel (claim.point.drop packLog)
  let iota := sumE ((List.range segs).map fun segment =>
    let constant := keccakRC.getD (depth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((List.range 64).filterMap fun z =>
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))
  require (projected + iota * sumE claim.mu == claim.value)
  let s ← sampleE
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  let (value, scale, point) ← keccakPackRounds claim.point (polyEval product s) 1
  let (localPoint, value) ← sumcheck value 4 (List.replicate localBits none)
  let t ← readEs 3
  let eqZ := eqKernelA (localPoint.take 6)
  let eqL := eqKernelA (localPoint.drop 6)
  let w := claim.weights.toArray
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  let weighted := sumE ((List.range 25).map fun l => eqL.getD l 0 *
    sumE ((List.range 64).map fun z => eqZ.getD z 0 * w.getD (64 * l + z) 0))
  require (scale * weighted * (kappa * t0 + (kappa + t1) * t2) == value)
  let beta ← sampleE
  let laneW := ((List.range 25).map fun l => eqL.getD l 0 + beta *
    (eqL.getD (keccakAlong (64 * l) 4 / 64) 0 + beta * eqL.getD (keccakAlong (64 * l) 3 / 64) 0)).toArray
  let weights := (List.range keccakBits).map fun j => eqZ.getD (j % 64) 0 * laneW.getD (j / 64) 0
  pure ⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose weights⟩

/-- The layers, `step` over the given list. -/
def keccakLayersG (depth segs logSteps : Nat) : List Nat → KeccakClaim → DM KeccakClaim
  | [], claim => pure claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayerG depth segs logSteps step claim
    keccakLayersG depth segs logSteps steps claim

/-- v1's layer is the generic layer at `12 × 2`. -/
theorem verifyKeccakLayer_eq_G (logSteps step : Nat) (claim : KeccakClaim) :
    verifyKeccakLayer logSteps step claim =
      verifyKeccakLayerG gkrDepth gkrSegments logSteps step claim := rfl

/-! ## T1 and T2: the tape -/

/-- **The tape's first claim** (T-G's `tapeFirstClaim` over `FE`): one segment, no committed
output: value `Σ_{l<25} eq(lanes, l)·a_l`, the instance weights of `r_{0..3}`, the point `r_{4..}`,
the weight of bit `j` `eq(lanes, j / 64)·x^(j mod 64)`. -/
def tapeFirstClaimF (inst lanePoint output : List FE) : KeccakClaim :=
  let lanes := eqKernel lanePoint
  ⟨dot (lanes.take 25) output, eqKernel (inst.take 4), inst.drop 4,
    (List.range keccakBits).map fun j => lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))⟩

/-- What the tape phase leaves: `r`, the 25 scalars, the lane point, the input claim. -/
structure TapeRes where
  /-- The instance point `r` (`logN` challenges). -/
  r : List FE
  /-- The 25 output scalars `a_l`. -/
  v : List FE
  /-- The five lane challenges. -/
  lanePt : List FE
  /-- The input claim `(C_in, μ, ρ, ω)`. -/
  claim : KeccakClaim

/-- **T2** on a tape of `2^logSteps` rows (T-G's `tapeGkr_eq` over `FE`): five lane challenges,
then the 24 layers from the first claim. -/
def tapeGkrF (logSteps : Nat) (inst output : List FE) : DM (List FE × KeccakClaim) := do
  let lanePt ← samples laneBits
  let claim ← keccakLayersG tapeDepth 1 logSteps (List.range tapeDepth)
    (tapeFirstClaimF inst lanePt output)
  pure (lanePt, claim)

/-- **The tape phase** (T1, T2; schedule phase `tape`): `r ← logN` challenges, the 25 scalars, the
GKR. -/
def dTape (logN : Nat) : DM TapeRes := do
  let r ← samples logN
  let v ← readEs lanes
  let (lanePt, claim) ← tapeGkrF logN r v
  pure ⟨r, v, lanePt, claim⟩

/-! ## The `FE` twins of T-K's kernels (`LvmWireKernel`) -/

/-- `eqAt` over `FE`: the equality weight of index `w` at `pt`, the first coordinate lowest. -/
def eqAtF : List FE → Nat → FE
  | [], _ => 1
  | r :: rs, w => (if w % 2 = 1 then r else 1 + r) * eqAtF rs (w / 2)

/-- `ι(i) = eq(ρ, i ≫ 4)·μ[i & 15]` (T-K's `iota`). -/
def iotaF (rho mu : List FE) (i : Nat) : FE := eqAtF rho (i / 16) * mu.getD (i % 16) 0

/-- `eqBit` over `FE`. -/
def eqBitF (a : FE) (b : Bool) : FE := if b then a else 1 + a

/-- T-K's `MS4` over `FE`. -/
structure MS4F where
  v00 : FE
  v01 : FE
  v10 : FE
  v11 : FE

/-- Entry `(c, s)`. -/
def MS4F.get (q : MS4F) : Bool → Bool → FE
  | false, false => q.v00
  | false, true => q.v01
  | true, false => q.v10
  | true, true => q.v11

/-- The strict flag after a bit (T-K's `nextS`). -/
def nextSF (y0 s tb : Bool) : Bool := if tb then y0 && s else y0 || s

/-- T-K's `msStep` over `FE`. -/
def msStepF (a r : FE) (tb : Bool) (q : MS4F) : MS4F :=
  let f : Bool → Bool → FE := fun c s =>
    (1 + a) * eqBitF r c * q.get false (nextSF c s tb) +
      a * eqBitF r (!c) * q.get c (nextSF (!c) s tb)
  ⟨f false false, f false true, f true false, f true true⟩

/-- T-K's `msTail` over `FE`. -/
def msTailF : List FE → List FE → Nat → MS4F
  | a :: σ, r :: ρ, t => msStepF a r (t % 2 == 1) (msTailF σ ρ (t / 2))
  | _, _, t => ⟨1, if 1 ≤ t then 1 else 0, 0, 0⟩

/-- **`MS_w^base(σ; t)`** (T-K's `msEval`) over `FE`: `K̃_ch(σ) = msEvalF ρ μ σ 0 m`. -/
def msEvalF (rho mu sigma : List FE) (base t : Nat) : FE :=
  let q := msTailF (sigma.drop 4) (rho.take (sigma.length - 4)) (t / 16)
  eqAtF (rho.drop (sigma.length - 4)) (base / 2 ^ sigma.length) *
    sumE ((List.range 16).map fun d =>
      eqAtF (sigma.take 4) d * mu.getD ((d + 1) % 16) 0 *
        q.get (d == 15) (decide (t % 16 < (d + 1) % 16)))

/-- T-K's `thrTail` over `FE`. -/
def thrTailF : List FE → Nat → FE × FE
  | r :: ρ, t =>
    let q := thrTailF ρ (t / 2)
    let tb := t % 2 == 1
    let g : Bool → FE := fun s =>
      (1 + r) * (if nextSF false s tb then q.2 else q.1) +
        r * (if nextSF true s tb then q.2 else q.1)
    (g false, g true)
  | [], t => (1, if 1 ≤ t then 1 else 0)

/-- **`Σ_{i ≤ t} ι(i)`** (T-K's `thrEval`) over `FE`. -/
def thrEvalF (rho mu : List FE) (t : Nat) : FE :=
  let q := thrTailF rho (t / 16)
  sumE ((List.range 16).map fun d => mu.getD d 0 * (if t % 16 < d then q.2 else q.1))

/-! ## The `FE` twins of T-W's dot products (`LvmWireSpec`) -/

/-- `⟨ω, c43⟩` (T-W's `c43Dot`): the constant bits of `Pad43`, `0x43` (bits 0, 1, 6), `0x01` at
bit 264, `0x80` at bit 1087. -/
def c43DotF (w : Array FE) : FE :=
  w.getD 0 0 + w.getD 1 0 + w.getD 6 0 + w.getD 264 0 + w.getD 1087 0

/-- `⟨ω, Pad43(d)⟩` (T-W's `padDot`) for the digest's four lanes `d`: the digest's set bits `p`
weigh `ω(8 + p)`, plus `⟨ω, c43⟩`. -/
def padDotF (w : Array FE) (d : List FK) : FE :=
  c43DotF w + sumE ((List.range 256).map fun p =>
    if (d.getD (p / 64) 0).val.toNat.testBit (p % 64) then w.getD (8 + p) 0 else 0)

/-- **The wiring target** (T-W's `wireTarget`): `C_in + ι(0)·⟨ω, Pad43(s)⟩ +
⟨ω, c43⟩·(Σ_{i ≤ m} ι(i) + ι(0))`, `m = n − 1`. -/
def wireTargetF (s : List FK) (n : Nat) (claim : KeccakClaim) : FE :=
  let w := claim.weights.toArray
  let i0 := iotaF claim.point claim.mu 0
  claim.value + i0 * padDotF w s + c43DotF w * (thrEvalF claim.point claim.mu (n - 1) + i0)

/-- **`D`'s slot weights at `τ`** (T-W's `slotWE 2 (dW ω) τ`): for each bit `z < 64`,
`Σ_{l<4} eq(τ, l)·ω(8 + 64 l + z)`. -/
def slotWF (w : Array FE) (tau : List FE) : List FE :=
  let e := eqKernel tau
  (List.range 64).map fun z =>
    sumE ((List.range 4).map fun l => e.getD l 0 * w.getD (8 + 64 * l + z) 0)

/-! ## T3, T4: the wire -/

/-- What the wire phase leaves (T-W's `WireChOut` over `FE`). -/
structure WireOut where
  /-- The wiring point `σ` and the final claim. -/
  sc : List FE × FE
  /-- `[g_D]`. -/
  g : List FE
  /-- The slot point `τ` and its final claim. -/
  sl : List FE × FE
  /-- The 64 slices of `D` at `(σ, τ)`. -/
  sv : List FE
  /-- The ring switch: the target and the weight over `C_main`. -/
  ring : FE × (List FE → FE)

/-- `D`'s block index among the `2^(nuMain − logN − 2)` aligned blocks of its size (T-W's `dsel`). -/
def dSel (p : Params) : Nat := (layout0 p).ch / 2 ^ (p.logN + 2)

/-- The selector bits above `D`'s block (T-W's `sb`): `nuMain − logN − 2`. -/
def dSelBits (p : Params) : Nat := p.nuMain - (p.logN + 2)

/-- **The wire phase** (T3, T4; schedule phase `wire`; T-W's `wireChProg p.logN (dSelBits p)
(dSel p) s n claim` over `FE`, read for read): the wiring sumcheck, `g_D`, the check
`final = K̃_ch(σ)·g_D`, `D`'s slot reduction over the two lane bits, the 64 slices, the slot check,
the ring switch at `σ ‖ τ ‖ sel(dSel)`. -/
def dWire (p : Params) (pub : Pub) (claim : KeccakClaim) : DM WireOut := do
  let sc ← sumcheck (wireTargetF pub.s pub.n claim) 3 (List.replicate p.logN none)
  let g ← readEs 1
  require (sc.2 == msEvalF claim.point claim.mu sc.1 0 (pub.n - 1) * g.getD 0 0)
  let sl ← sumcheck (g.getD 0 0) 3 [none, none]
  let sv ← readEs kBits
  require (sl.2 == dot (slotWF claim.weights.toArray sl.1) sv)
  let ring ← ringSwitch (sc.1 ++ sl.1 ++ selectorPoint (dSel p) (dSelBits p)) sv
  pure ⟨sc, g, sl, sv, ring⟩

/-- **A1's range of `n`** (`1 ≤ n ≤ 2^logN`), checked before the wire: the wiring identity and
`K_ch` need it. `parseOk` checks it too; this copy makes the phase's specification unconditional
(no transcript change). -/
def dRange (p : Params) (pub : Pub) : DM Unit := require (decide (1 ≤ pub.n ∧ pub.n ≤ 2 ^ p.logN))

/-! ## The tape's claims (T1, T4, T5) -/

/-- **The tape's claims on `C_main`** (T-P1's C.7 order): `D̃_l(r) = a_l` for `l < 4` (T1), the
ring-switched slices on `C_main` (T4), `D̃_l(bits(n − 1)) = h_l` for `l < 4` (T5, A1: `n ≥ 1`). -/
def tapeClaims (p : Params) (t : TapeRes) (wo : WireOut) (pub : Pub) : List BlockClaim :=
  let blk := dBlock p
  ((List.range dLanes).map fun l =>
    BlockClaim.point blk (t.r ++ selectorPoint l 2) (t.v.getD l 0)) ++
  [⟨⟨p.nuMain, 0⟩, wo.ring.2, wo.ring.1⟩] ++
  (pub.h.zipIdx.map fun (w, l) =>
    BlockClaim.point blk (selectorPoint (pub.n - 1) p.logN ++ selectorPoint l 2) (FE.ofK w))

end Lvm
