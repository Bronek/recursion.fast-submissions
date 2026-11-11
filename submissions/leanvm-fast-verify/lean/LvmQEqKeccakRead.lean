import LvmQSumcheck
import LvmQKeccakSpec

/-!
# QA1: `F`'s Keccak GKR verifier read from the stream (pure forms of the reader programs)

`F`'s Keccak GKR (`LvmDecideKeccak`: `keccakPackRounds`, `verifyKeccakLayer`, `keccakLayers`,
`keccakOpen`, `verifyKeccak`) reads the stream through the cursor; every read sits at the position
`p = ent + msg` plus a constant. Here each program is a pure function of the view `v` (`feAt Σ`)
and `p` (`packSpec`, `layerSpec`, …), and `*_run` says the reader program is that function, its
state moved to the end position with `ok` conjoined with the program's checks. The layer's
expressions are `F`'s, copied verbatim (so the run lemmas are definitional after the reads).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm DM

theorem require_run (c : Bool) (sig : ByteArray) (s : RS) :
    require c sig s = ((), { s with ok := c && s.ok }) := rfl

/-! ## The pack rounds -/

/-- **`keccakPackRounds` on a view**: value, scale, challenges, end position. -/
def packSpec (v : Nat → FE) : List FE → FE → FE → Nat → FE × FE × List FE × Nat
  | [], value, scale, p => (value, scale, [], p)
  | r :: rs, value, scale, p =>
    let msg := roundPoly v p 3 value (some r)
    let ch := v (p + 88)
    let res := packSpec v rs ((1 + r + ch) * polyEval msg ch) (scale * (1 + r + ch)) (p + 120)
    (res.1, res.2.1, ch :: res.2.2.1, res.2.2.2)

theorem packRounds_cons (r : FE) (rs : List FE) (value scale : FE) :
    keccakPackRounds (r :: rs) value scale =
      (sumcheckRoundPoly 3 value (some r) >>= fun message => sampleE >>= fun challenge =>
        keccakPackRounds rs ((1 + r + challenge) * polyEval message challenge) (scale * (1 + r + challenge)) >>=
          fun res => pure (res.1, res.2.1, challenge :: res.2.2)) := rfl

theorem packRounds_run (sig : ByteArray) : ∀ (pt : List FE) (value scale : FE) (s : RS),
    keccakPackRounds pt value scale sig s =
      (((packSpec (feAt sig) pt value scale (s.ent + s.msg)).1,
        (packSpec (feAt sig) pt value scale (s.ent + s.msg)).2.1,
        (packSpec (feAt sig) pt value scale (s.ent + s.msg)).2.2.1),
        if pt = [] then s else ⟨(packSpec (feAt sig) pt value scale (s.ent + s.msg)).2.2.2, 0, s.ok⟩)
  | [], value, scale, s => rfl
  | r :: rs, value, scale, s => by
    rw [packRounds_cons, bind_run, roundPoly_run sig 3 (by omega), bind_run, sampleE_run, bind_run,
      packRounds_run sig rs, pure_run]
    have h1 : s.ent + 40 + (s.msg + 24 * (3 - 1)) = s.ent + s.msg + 88 := by omega
    have h2 : s.ent + 72 + (s.msg + 24 * (3 - 1)) + 0 = s.ent + s.msg + 120 := by omega
    simp only [h1, h2, packSpec]
    cases rs with
    | nil => simp only [packSpec, if_true, if_neg (List.cons_ne_nil r [])]; congr 2
    | cons r' rs' => simp

theorem scState_replicate (count : Nat) (s : RS) {n : Nat} (hn : 0 < n) (e : Option FE) :
    scState count s (List.replicate n e) = ⟨s.ent + s.msg + n * roundLen count, 0, s.ok⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [scState, List.replicate_succ]

/-! ## A layer -/

/-- `F`'s projected value (`verifyKeccakLayer`, verbatim). -/
def projF (claim : KeccakClaim) (product : List FE) : FE :=
  sumE ((List.range productBits).map fun c =>
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) =>
      if mask.testBit c then some m else none) * product.getD c 0)

/-- `F`'s iota term (verbatim). -/
def iotaLayerF (logSteps step : Nat) (claim : KeccakClaim) : FE :=
  sumE ((List.range gkrSegments).map fun segment =>
    (eqKernel (claim.point.drop (logSteps - 4))).getD segment 0 *
      sumE ((List.range 64).filterMap fun z =>
        if (keccakRC.getD (gkrDepth * (segment + 1) - step - 1) 0).toNat.testBit z then
          some (claim.weights.getD z 0) else none))

/-- `F`'s final-check weight (verbatim, arrays). -/
def weightedLayerF (localPoint : List FE) (claim : KeccakClaim) : FE :=
  sumE ((List.range 25).map fun l => (eqKernelA (localPoint.drop 6)).getD l 0 *
    sumE ((List.range 64).map fun z => (eqKernelA (localPoint.take 6)).getD z 0 *
      claim.weights.toArray.getD (64 * l + z) 0))

/-- `F`'s next lane weights (verbatim). -/
def laneWF (localPoint : List FE) (beta : FE) : Array FE :=
  ((List.range 25).map fun l => (eqKernelA (localPoint.drop 6)).getD l 0 + beta *
    ((eqKernelA (localPoint.drop 6)).getD (keccakAlong (64 * l) 4 / 64) 0 + beta *
      (eqKernelA (localPoint.drop 6)).getD (keccakAlong (64 * l) 3 / 64) 0)).toArray

/-- A layer's result: the next claim, its two checks, the end position. -/
structure LayerOut where
  /-- The claim before the round. -/
  claim : KeccakClaim
  /-- The projection check. -/
  ok1 : Bool
  /-- The final check. -/
  ok2 : Bool
  /-- The position after the layer. -/
  pos : Nat

/-- **`verifyKeccakLayer` on a view** from position `p`. -/
def layerSpec (v : Nat → FE) (logSteps step : Nat) (claim : KeccakClaim) (p : Nat) : LayerOut :=
  let product := scalarsAt v (p + 40) productBits
  let s := v (p + 40 + 24 * productBits)
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  let pk := packSpec v claim.point (polyEval product s) 1 (p + 72 + 24 * productBits)
  let sc := scSpec v 4 pk.2.2.2 pk.1 (List.replicate localBits none)
  let p3 := pk.2.2.2 + localBits * roundLen 4
  let t := scalarsAt v (p3 + 40) 3
  let beta := v (p3 + 40 + 24 * 3)
  let eqZ := eqKernelA (sc.1.take 6)
  let laneW := laneWF sc.1 beta
  ⟨⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), mu, pk.2.2.1,
      keccakLinearTranspose ((List.range keccakBits).map fun j => eqZ.getD (j % 64) 0 * laneW.getD (j / 64) 0)⟩,
    projF claim product + iotaLayerF logSteps step claim * sumE claim.mu == claim.value,
    pk.2.1 * weightedLayerF sc.1 claim * (kappa * t.getD 0 0 + (kappa + t.getD 1 0) * t.getD 2 0) == sc.2,
    p3 + 72 + 24 * 3⟩

/-! The reading equations as proof-producing `simp` rules: as `rfl` lemmas `simp` applies them
definitionally and the kernel re-derives each step by unfolding `>>=`, comparing the remaining
reads first (3–8 s in `verifyKeccakLayer_run`); with a proof that is not `rfl`, `simp` cites them. -/

theorem rd_bind_run {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run m f sig s).trans rfl

theorem rd_pure_run {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run a sig s).trans rfl

theorem rd_sampleE_run (sig : ByteArray) (s : RS) :
    sampleE sig s = (feAt sig (s.ent + 40 + s.msg), { s with ent := s.ent + 72 + s.msg, msg := 0 }) :=
  (sampleE_run sig s).trans rfl

theorem rd_require_run (c : Bool) (sig : ByteArray) (s : RS) :
    require c sig s = ((), { s with ok := c && s.ok }) := (require_run c sig s).trans rfl

theorem verifyKeccakLayer_run (sig : ByteArray) (logSteps step : Nat) (claim : KeccakClaim)
    (hpt : claim.point ≠ []) (s : RS) :
    verifyKeccakLayer logSteps step claim sig s =
      ((layerSpec (feAt sig) logSteps step claim (s.ent + s.msg)).claim,
        ⟨(layerSpec (feAt sig) logSteps step claim (s.ent + s.msg)).pos, 0,
          (layerSpec (feAt sig) logSteps step claim (s.ent + s.msg)).ok2 &&
            ((layerSpec (feAt sig) logSteps step claim (s.ent + s.msg)).ok1 && s.ok)⟩) := by
  simp only [verifyKeccakLayer, rd_bind_run, rd_pure_run, readEs_run, rd_require_run, rd_sampleE_run,
    packRounds_run sig, sumcheck_run sig 4 (by norm_num), if_neg hpt]
  have r1 : ∀ a b : Nat, a + 40 + (b + 24 * productBits) = a + b + 40 + 24 * productBits := by
    intro a b; omega
  have r2 : ∀ a b : Nat, a + 72 + (b + 24 * productBits) = a + b + 72 + 24 * productBits := by
    intro a b; omega
  simp only [scState_replicate _ _ (show 0 < localBits by decide), layerSpec, Nat.add_zero, Nat.zero_add]
  rw [r1, r2]
  rfl

theorem packSpec_length (v : Nat → FE) : ∀ (pt : List FE) (value scale : FE) (p : Nat),
    (packSpec v pt value scale p).2.2.1.length = pt.length
  | [], _, _, _ => rfl
  | r :: rs, value, scale, p => by
    simp only [packSpec, List.length_cons]; rw [packSpec_length v rs]

/-- **`keccakLayers` on a view**: the claim, the end position and the checks (`ok` threaded). -/
def layersSpec (v : Nat → FE) (logSteps : Nat) : List Nat → KeccakClaim → Nat → Bool → KeccakClaim × Nat × Bool
  | [], claim, p, ok => (claim, p, ok)
  | step :: steps, claim, p, ok =>
    let L := layerSpec v logSteps step claim p
    layersSpec v logSteps steps L.claim L.pos (L.ok2 && (L.ok1 && ok))

theorem layerSpec_point_length (v : Nat → FE) (logSteps step : Nat) (claim : KeccakClaim) (p : Nat) :
    (layerSpec v logSteps step claim p).claim.point.length = claim.point.length :=
  packSpec_length v _ _ _ _

theorem layersSpec_point (v : Nat → FE) (logSteps : Nat) : ∀ (steps : List Nat) (claim : KeccakClaim)
    (p : Nat) (ok : Bool), (layersSpec v logSteps steps claim p ok).1.point.length = claim.point.length := by
  -- `induction`, not structural recursion: the recursion's functional cost the kernel 0.6 s
  intro steps
  induction steps with
  | nil => intro _ _ _; rfl
  | cons step steps ih =>
    intro claim p ok
    rw [layersSpec, ih, layerSpec_point_length]

/-! ## Openings and the whole GKR -/

/-- `keccakOpen`'s fold of the slot weight rows along the slot challenges (verbatim). -/
def openFold (slot : List FE) (rows : List (List FE)) : List (List FE) :=
  slot.foldl (fun rows challenge =>
    (List.range (rows.length / 2)).map fun i =>
      List.zipWith (fun lo hi => lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows

/-- **`keccakOpen` on a view**: the slot point, the folded weights, the final claim. -/
def openSpec (v : Nat → FE) (logSteps : Nat) (claim : KeccakClaim) (first count : Nat) (value : FE)
    (p : Nat) : List FE × List FE × FE :=
  let sc := scSpec v 3 p value (List.replicate keccakSlotBits none)
  (sc.1, (openFold sc.1 (keccakSlotWeights logSteps claim first count)).headD [], sc.2)

theorem keccakOpen_run (sig : ByteArray) (logSteps : Nat) (claim : KeccakClaim) (first count : Nat)
    (value : FE) (s : RS) :
    keccakOpen logSteps claim first count value sig s =
      (openSpec (feAt sig) logSteps claim first count value (s.ent + s.msg),
        ⟨s.ent + s.msg + keccakSlotBits * roundLen 3, 0, s.ok⟩) := by
  rw [show keccakOpen logSteps claim first count value =
    (sumcheck value 3 (List.replicate keccakSlotBits none) >>= fun r =>
      pure (r.1, (openFold r.1 (keccakSlotWeights logSteps claim first count)).headD [], r.2)) from rfl,
    bind_run, sumcheck_run sig 3 (by norm_num), pure_run, scState_replicate _ _ (by decide)]
  rfl

end Lvm.Q1
