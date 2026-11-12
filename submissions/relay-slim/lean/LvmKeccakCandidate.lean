-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/Candidate.lean` (formal rev 40f877dc) as `LvmKeccakCandidate` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.Candidate

  A candidate `q_keccak` column and what the reduction says of it: its states per segment and
  step, the claims the reduction starts from and ends with, `RegionValid`, and a generic
  multilinear zero test for the phase that draws the table point.
-/


import LvmKeccakWords
import LvmKeccakLayer

/-!
# Candidates

A candidate's `q_keccak` column is read as `col : ℕ → K` (word `n`, `0` past the end): word
`x + 2^h·slot` is lane `slot` of step `x`'s input state (slots `0..24`), or for slot `25 + ℓ`
lane `ℓ` of the committed state after twelve rounds (`doc/leanvm` §`keccak:segments`).

* `inState col m x`: segment `m`'s committed input at step `x` (slots `25m .. 25m + 24`);
  `statesAt col d`: the states `12 - d` rounds into each segment, as bits (depth `d`);
  `statesAt_round`: depth `d` is the round `12(m + 1) - d - 1` of depth `d + 1`
  (`afterRound`), so a layer's specification applies (`claimTrue_round`).
* The statements: `outClaimsTrue` (the table's `25` output-lane claims at `inst`, against
  `keccakF` of the inputs), `outClaimsTrueMid` (against the second segment from the committed
  middle state), `midAgree` (the first segment's output and the committed middle state agree at
  `inst`, lane by lane), `RegionValid` (they agree at every step); `colTrue`, `slicesTrue`: the
  claims the reduction leaves on `q_keccak`. `outClaims_of_regionValid`: a valid region with
  true output claims has true middle-state claims.
* `ZeroOn δ acc n`: the multilinear extension of the table `δ` on `n` bits, with its first
  `|acc|` coordinates bound to `acc`, is identically zero; `zeroOn_escape`: a coordinate drawn
  uniformly makes a nonzero part-way extension zero with probability at most `1/|E|`.
  `midAgree_iff`, `regionValid_iff`: `midAgree` at `inst` and `RegionValid` are `ZeroOn` of the
  `25` tables `midDelta` at `inst` and at `[]`. This is the escape the phase drawing `inst`
  (the table sumcheck) charges, `h/|E|` per candidate, to turn `RegionValid` into `midAgree`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open Finset
open scoped ENNReal

section

variable (h : ℕ)

/-! ## States -/

/-- Segment `m`'s committed input at step `x`: slots `25m .. 25m + 24`. -/
def inState (col : ℕ → K) (m x : ℕ) : KeccakState :=
  Vector.ofFn fun l : Fin 25 ↦ K.lane (col (x + 2 ^ h * (25 * m + l)))

/-- The state `e` rounds into segment `m` at step `x`. -/
def segState (col : ℕ → K) (m e x : ℕ) : KeccakState := roundsFrom (12 * m) e (inState h col m x)

/-- The states at depth `d` (`12 - d` rounds into each segment), as bits. -/
def statesAt (col : ℕ → K) (d : ℕ) : States := fun m x j ↦ sbit (segState h col m (12 - d) x) j

theorem statesAt_round (col : ℕ → K) {d : ℕ} (hd : d < 12) (m x j : ℕ) (hm : m < 2)
    (hj : j < 1600) : statesAt h col d m x j = afterRound (statesAt h col (d + 1)) d m x j := by
  have e : 12 - d = (12 - (d + 1)) + 1 := by omega
  rw [statesAt, segState, e, roundsFrom_succ (by omega), sbit_round _ _ hj, afterRound, layerRC]
  have e2 : keccakDepth * (m + 1) - d - 1 = 12 * m + (12 - (d + 1)) := by
    rw [show keccakDepth = 12 from rfl]; omega
  rw [e2]
  rfl

theorem claimTrue_round (col : ℕ → K) {d : ℕ} (hd : d < 12) (P : ℕ) (c : KeccakClaim) :
    ClaimTrue (statesAt h col d) P c ↔ ClaimTrue (afterRound (statesAt h col (d + 1)) d) P c := by
  unfold ClaimTrue
  rw [claimSum_congr P (fun m x j hm hj ↦ statesAt_round h col hd m x j hm hj)]

/-! ## The statements -/

/-- The multilinear extension over the steps of a `K`-valued function, at `pt`. -/
def stepMle (pt : List E) (f : ℕ → K) : E := ∑ x ∈ range (2 ^ h), eqAt pt x * ofK (f x)

/-- Lane `l` of a state as a word. -/
def laneWord (a : KeccakState) (l : ℕ) : K := K.ofLane (Keccak.lane a l)

/-- **The table's output-lane claims** at `inst`: lane `l` of `keccakF` of each step's input. -/
def outClaimsTrue (col : ℕ → K) (inst output : List E) : Prop :=
  ∀ l < 25, stepMle h inst (fun x ↦ laneWord (keccakF1600 (inState h col 0 x)) l) = output.getD l 0

/-- The output-lane claims against the second segment, from the committed middle state. -/
def outClaimsTrueMid (col : ℕ → K) (inst output : List E) : Prop :=
  ∀ l < 25, stepMle h inst (fun x ↦ laneWord (roundsFrom 12 12 (inState h col 1 x)) l) =
    output.getD l 0

/-- The first segment's output and the committed middle state agree at `inst`, lane by lane. -/
def midAgree (col : ℕ → K) (inst : List E) : Prop :=
  ∀ l < 25, stepMle h inst (fun x ↦ laneWord (roundsFrom 0 12 (inState h col 0 x)) l) =
    stepMle h inst (fun x ↦ col (x + 2 ^ h * (25 + l)))

/-- **The committed middle state is twelve rounds of the input**, at every step. -/
def RegionValid (col : ℕ → K) : Prop :=
  ∀ x < 2 ^ h, inState h col 1 x = roundsFrom 0 12 (inState h col 0 x)

/-- A column claim on `q_keccak` holds: the column's multilinear extension (step bits low, the
six slot bits high) at the claim's point. -/
def colTrue (col : ℕ → K) (c : ColumnClaim) : Prop :=
  c.column = qkeccak ∧ c.point.length = h + 6 ∧
    c.value = ∑ n ∈ range (2 ^ (h + 6)), eqAt c.point n * ofK (col n)

/-- The `64` bit-slice claims hold: slice `i`'s multilinear extension at `point` is
`slices[i]`. -/
def slicesTrue (col : ℕ → K) (point slices : List E) : Prop :=
  point.length = h + 6 ∧ slices.length = 64 ∧ ∀ i < 64,
    slices.getD i 0 = ∑ n ∈ range (2 ^ (h + 6)), eqAt point n * bitE ((col n).toBitVec.getLsbD i)

theorem lane_inState (col : ℕ → K) (m x : ℕ) {l : ℕ} (hl : l < 25) :
    Keccak.lane (inState h col m x) l = K.lane (col (x + 2 ^ h * (25 * m + l))) := by
  rw [lane_eq _ hl, inState, Vector.getElem_ofFn]

/-! ## A multilinear zero test -/

/-- The table `δ` with its first `|acc|` coordinates bound to `acc`, at the remaining index `v`. -/
def foldT (δ : ℕ → E) (acc : List E) (v : ℕ) : E :=
  ∑ w ∈ range (2 ^ acc.length), eqAt acc w * δ (w + 2 ^ acc.length * v)

/-- The multilinear extension of `δ` on `n` bits, its first coordinates bound to `acc`, is
identically zero. -/
def ZeroOn (δ : ℕ → E) (acc : List E) (n : ℕ) : Prop :=
  ∀ v < 2 ^ (n - acc.length), foldT δ acc v = 0

theorem foldT_nil (δ : ℕ → E) (v : ℕ) : foldT δ [] v = δ v := by simp [foldT]

theorem foldT_snoc (δ : ℕ → E) (acc : List E) (c : E) (v : ℕ) :
    foldT δ (acc ++ [c]) v = (1 + c) * foldT δ acc (2 * v) + c * foldT δ acc (2 * v + 1) := by
  unfold foldT
  rw [List.length_append, List.length_singleton, pow_succ, mul_comm (2 ^ acc.length) 2,
    sum_range_mul 2 (2 ^ acc.length), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.1 hw
    rw [eqAt_append, Nat.mul_zero, Nat.zero_add, Nat.div_eq_of_lt hw']
    simp only [eqAt_cons, eqAt_nil, Nat.zero_mod, zero_ne_one, ite_false, mul_one]
    rw [show w + 2 * 2 ^ acc.length * v = w + 2 ^ acc.length * (2 * v) by ring]
    ring
  · refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.1 hw
    have hd : (2 ^ acc.length * 1 + w) / 2 ^ acc.length = 1 := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hw']
    rw [eqAt_append, hd, eqAt_mod acc (2 ^ acc.length * 1 + w), Nat.add_comm,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw']
    simp only [eqAt_cons, eqAt_nil, Nat.one_mod, ite_true, mul_one]
    rw [show w + 2 ^ acc.length + 2 * 2 ^ acc.length * v =
      w + 2 ^ acc.length * (2 * v + 1) by ring]
    ring

theorem zeroOn_nil (δ : ℕ → E) (n : ℕ) : ZeroOn δ [] n ↔ ∀ v < 2 ^ n, δ v = 0 := by
  simp [ZeroOn, foldT_nil]

theorem zeroOn_full (δ : ℕ → E) {acc : List E} {n : ℕ} (h : acc.length = n) :
    ZeroOn δ acc n ↔ ∑ w ∈ range (2 ^ n), eqAt acc w * δ w = 0 := by
  rw [ZeroOn, h, Nat.sub_self]
  simp [foldT, h]

/-- **The zero test's escape**: a coordinate drawn uniformly makes a nonzero part-way extension
zero at one value at most. -/
theorem zeroOn_escape (δ : ℕ → E) {n : ℕ} {acc : List E} (hacc : acc.length < n)
    (hne : ¬ ZeroOn δ acc n) :
    avgE (fun c ↦ indE (ZeroOn δ (acc ++ [c]) n)) ≤ errE 1 := by
  obtain ⟨v, hv, hfv⟩ : ∃ v < 2 ^ (n - acc.length), foldT δ acc v ≠ 0 := by
    by_contra hall
    exact hne fun v hv ↦ by_contra fun h0 ↦ hall ⟨v, hv, h0⟩
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by omega
  have hv2 : v / 2 < 2 ^ (n - (acc.length + 1)) := by
    rw [hm, pow_succ] at hv; omega
  -- the pair at `v / 2` is not zero, so its fold is a nonzero affine function of `c`
  let a0 := foldT δ acc (2 * (v / 2))
  let a1 := foldT δ acc (2 * (v / 2) + 1)
  have hpair : ¬ (a0 = 0 ∧ a1 = 0) := by
    rintro ⟨h0, h1⟩
    rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv0
    · exact hfv (by rw [show v = 2 * (v / 2) by omega]; exact h0)
    · exact hfv (by rw [show v = 2 * (v / 2) + 1 by omega]; exact h1)
  open Polynomial in
  have hne' : (C a0 + C (a0 + a1) * X : E[X]) ≠ 0 := by
    intro he
    refine hpair ⟨?_, ?_⟩
    · have := congrArg (coeff · 0) he; simpa using this
    · have h0 : a0 = 0 := by have := congrArg (coeff · 0) he; simpa using this
      have := congrArg (coeff · 1) he
      simp at this
      rw [h0, zero_add] at this; exact this
  open Polynomial in
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
    (sz_escape hne' (q := 0) (d := 1) (natDegree_add_le_of_degree_le
      ((natDegree_C _).trans_le (by norm_num)) ((natDegree_C_mul_le _ _).trans (by simp)))
      (by simp))
  have := hc (v / 2) (by rw [List.length_append, List.length_singleton]; exact hv2)
  rw [foldT_snoc] at this
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_zero]
  rw [← this]
  ring

/-- The `25` tables of the middle state's mismatch: lane `l` of the first segment's output
minus (plus, in characteristic two) the committed middle state's, at each step. -/
def midDelta (col : ℕ → K) (l x : ℕ) : E :=
  ofK (laneWord (roundsFrom 0 12 (inState h col 0 x)) l) + ofK (col (x + 2 ^ h * (25 + l)))


open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Complete

/-! ## Shapes (lvm2 T-G)

leanVM's `KeccakShape` (`keccak.rs:50-67`): the reduction runs `depth` layers per segment over
`segments` segments of one Keccak-f. v1's tables use `12 × 2` (`Shape.v1`, the constants of
`LvmVCore`), lvm2's tape `24 × 1` (`Shape.tape`). The generic statements cover one or two
segments (`Shape.Ok`).

A claim's point has `P + 1` coordinates. With two segments the top one is the segment and
`logSteps = P + 4`; with one segment it is the pack's top bit and `logSteps = P + 5`. The layer
theory of `LvmKeccakLayer*` sums over `(m, x)` with `m < 2`: `Shape.seg` and `Shape.step` read
such a pair as a segment and a step, and `layerRCS` gives its round constant. -/

/-- A GKR shape: `depth` layers per segment, `segments` segments. -/
structure Shape where
  /-- Layers per segment (`KECCAK_DEPTH`). -/
  depth : ℕ
  /-- Segments, `24 / depth`. -/
  segments : ℕ

namespace Shape

/-- v1's shape, `12 × 2` (`keccakDepth`, `keccakSegments`). -/
def v1 : Shape := ⟨keccakDepth, keccakSegments⟩

/-- The tape's shape, `24 × 1`. -/
def tape : Shape := ⟨24, 1⟩

/-- The bits of a segment index, `log2_ceil(segments)` (`keccak.rs:247`). -/
def segBits (sh : Shape) : ℕ := log2Ceil sh.segments

/-- The shapes the generic statements cover. -/
def Ok (sh : Shape) : Prop := (sh.segments = 1 ∨ sh.segments = 2) ∧ sh.depth * sh.segments = 24

/-- The segment of a claim's top coordinate `m`. -/
def seg (sh : Shape) (m : ℕ) : ℕ := if sh.segments = 1 then 0 else m

/-- The step of the pair `(m, x)`: `x`, plus `2^(P+4)·m` with one segment. -/
def step (sh : Shape) (P m x : ℕ) : ℕ := if sh.segments = 1 then x + 2 ^ (P + 4) * m else x

/-- The log of the number of steps for claims with `P + 1` point coordinates. -/
def logSteps (sh : Shape) (P : ℕ) : ℕ := if sh.segments = 1 then P + 5 else P + 4

theorem v1_ok : v1.Ok := ⟨Or.inr rfl, rfl⟩

theorem tape_ok : tape.Ok := ⟨Or.inl rfl, rfl⟩

theorem v1_segBits : v1.segBits = 1 := by decide

theorem tape_segBits : tape.segBits = 0 := by decide

theorem v1_logSteps (P : ℕ) : v1.logSteps P = P + 4 := rfl

theorem tape_logSteps (P : ℕ) : tape.logSteps P = P + 5 := rfl

theorem segBits_of_ok {sh : Shape} (hsh : sh.Ok) : sh.segBits = sh.segments - 1 := by
  rcases hsh.1 with h | h <;> rw [segBits, h] <;> decide

theorem seg_lt {sh : Shape} (hsh : sh.Ok) {m : ℕ} (hm : m < 2) : sh.seg m < sh.segments := by
  unfold seg; rcases hsh.1 with h | h <;> simp [h] <;> omega

end Shape

/-! ### The programs at a shape (VCore's, with `sh.depth` and `sh.segments`) -/

/-- `verify_layer` at the shape `sh` (VCore's `verifyKeccakLayer`, `keccak.rs:115-196`). -/
def verifyKeccakLayerS (sh : Shape) (logSteps step : ℕ) (claim : KeccakClaim) :
    VerifierProgram KeccakClaim := do
  let packBits := logSteps - 4
  let product ← VerifierProgram.readScalars productBits
  let projected := sumE ((List.range productBits).map fun c ↦
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0)
  let segments := eqKernel (claim.point.drop packBits)
  let iota := sumE ((List.range sh.segments).map fun segment ↦
    let constant := keccakRC.getD (sh.depth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((List.range 64).filterMap fun z ↦
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))
  VerifierProgram.require (projected + iota * sumE claim.mu = claim.value)
  let s ← VerifierProgram.sampleChallenge
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  let (value, scale, point) ← keccakPackRounds claim.point (polyEval product s) 1
  let (localPoint, value) ← sumcheck value 4 (List.replicate keccakLocalBits none)
  let t ← VerifierProgram.readScalars 3
  let eq := eqKernel localPoint
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  VerifierProgram.require
    (scale * dot (eq.take keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) = value)
  let beta ← VerifierProgram.sampleChallenge
  let weights := (List.range keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)
  return ⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose weights⟩

/-- The layers at the shape `sh` (`keccak.rs:264-267`). -/
def keccakLayersS (sh : Shape) (logSteps : ℕ) : List ℕ → KeccakClaim → VerifierProgram KeccakClaim
  | [], claim => return claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayerS sh logSteps step claim
    keccakLayersS sh logSteps steps claim

theorem verifyKeccakLayer_v1 (logSteps step : ℕ) (claim : KeccakClaim) :
    verifyKeccakLayer logSteps step claim = verifyKeccakLayerS Shape.v1 logSteps step claim := rfl

theorem keccakLayers_v1 (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : KeccakClaim),
      keccakLayers logSteps steps claim = keccakLayersS Shape.v1 logSteps steps claim
  | [], _ => rfl
  | step :: steps, claim => by
    rw [keccakLayers, keccakLayersS, verifyKeccakLayer_v1]
    exact congrArg _ (funext fun c ↦ keccakLayers_v1 logSteps steps c)

/-! ### A layer at a shape -/

/-- The round constant of the pair's segment at layer `step`: round
`depth·(seg m + 1) - step - 1`. -/
def layerRCS (sh : Shape) (step m : ℕ) : UInt64 :=
  keccakRC.getD (sh.depth * (sh.seg m + 1) - step - 1) 0

/-- The states after the layer's round, at the shape `sh`. -/
def afterRoundS (sh : Shape) (T : States) (step : ℕ) : States :=
  fun m x j ↦ roundB (layerRCS sh step m) (T m x) j

theorem afterRound_v1 (T : States) (step : ℕ) : afterRound T step = afterRoundS Shape.v1 T step := rfl

/-- The verifier's `iota` at the shape `sh`. -/
def iotaOfS (sh : Shape) (logSteps step : ℕ) (claim : KeccakClaim) : E :=
  sumE ((List.range sh.segments).map fun segment ↦
    let constant := keccakRC.getD (sh.depth * (segment + 1) - step - 1) 0
    (eqKernel (claim.point.drop (logSteps - 4))).getD segment 0 *
      sumE ((List.range 64).filterMap fun z ↦
        if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))

/-- A layer at the shape `sh`, with the tuples of the `do` block as projections. -/
def layerProgS (sh : Shape) (logSteps step : ℕ) (claim : KeccakClaim) :
    VerifierProgram KeccakClaim :=
  VerifierProgram.readScalars productBits >>= fun product ↦
  VerifierProgram.require (projectedOf claim product + iotaOfS sh logSteps step claim *
      sumE claim.mu = claim.value) >>= fun _ ↦
  VerifierProgram.sampleChallenge >>= fun s ↦
  keccakPackRounds claim.point (polyEval product s) 1 >>= fun res ↦
  sumcheck res.1 4 (List.replicate keccakLocalBits none) >>= fun res2 ↦
  layerTail claim s res res2

theorem verifyKeccakLayerS_eq (sh : Shape) (logSteps step : ℕ) (claim : KeccakClaim) :
    verifyKeccakLayerS sh logSteps step claim = layerProgS sh logSteps step claim := rfl

/-- The claim's sum after the round at a shape (`claimSum_round` with `layerRCS`). -/
theorem claimSum_roundS (sh : Shape) (T : States) (step P : ℕ) (point mu w : List E)
    (hpt : point.length = P + 1) :
    claimSum (afterRoundS sh T step) P point mu w =
      ∑ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) +
        (∑ m ∈ range 2, eqAt (point.drop P) m * iotaW (layerRCS sh step m) w) *
          ∑ i ∈ range 16, mu.getD i 0 := by

  have hb : ∀ z i j, bitE (stAt (afterRoundS sh T step) P z i j) =
      bitE (chiB (Lb (stAt T P z i)) j) + bitE (iotaB (layerRCS sh step (z / 2 ^ P)) j) := by
    intro z i j
    rw [stAt, afterRoundS, roundB, bitE_xor]
    rfl
  have e1 : claimSum (afterRoundS sh T step) P point mu w =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ i ∈ range 16, mu.getD i 0 *
        ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) +
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * (∑ i ∈ range 16, mu.getD i 0) *
        iotaW (layerRCS sh step (z / 2 ^ P)) w := by
    rw [claimSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have : ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
          bitE (stAt (afterRoundS sh T step) P z i j) =
        ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
          bitE (chiB (Lb (stAt T P z i)) j) +
        (∑ i ∈ range 16, mu.getD i 0) * iotaW (layerRCS sh step (z / 2 ^ P)) w := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [hb, mul_add, Finset.sum_add_distrib, sum_iotaB]
    rw [this]
    ring
  have p1 : ∑ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ i ∈ range 16, mu.getD i 0 *
        ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) := by
    have h : ∀ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) =
        mu.getD i 0 * ∑ z ∈ range (2 ^ (P + 1)), eqAt point z *
          ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) :=
      fun i hi ↦ by rw [projE_Gpoly T P point w (Finset.mem_range.1 hi)]
    rw [Finset.sum_congr rfl h]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ by ring
  have p2 : ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * (∑ i ∈ range 16, mu.getD i 0) *
        iotaW (layerRCS sh step (z / 2 ^ P)) w =
      (∑ m ∈ range 2, eqAt (point.drop P) m * iotaW (layerRCS sh step m) w) *
        ∑ i ∈ range 16, mu.getD i 0 := by
    rw [← sum_segment hpt (fun m ↦ iotaW (layerRCS sh step m) w), Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  rw [e1, p1, p2]
/-- **The verifier's `iota` at a shape** (`keccak.rs:133-139`). -/
theorem iota_eqS {sh : Shape} (hsh : sh.Ok) (step P : ℕ) (claim : KeccakClaim)
    (hpt : claim.point.length = P + 1) :
    iotaOfS sh (sh.logSteps P) step claim =
      ∑ m ∈ range 2, eqAt (claim.point.drop P) m * iotaW (layerRCS sh step m) claim.weights := by
  have hsum : ∀ c : UInt64, sumE ((List.range 64).filterMap fun z ↦
      if c.toNat.testBit z then some (claim.weights.getD z 0) else none) = iotaW c claim.weights :=
    fun c ↦ by rw [sumE_filterMap_range]; rfl
  have hl : (claim.point.drop P).length = 1 := by simp [hpt]
  unfold iotaOfS
  simp only []
  rw [sumE_eq_sum, list_sum_range]
  rcases hsh.1 with h1 | h2
  · have hd : claim.point.drop (sh.logSteps P - 4) = [] := by
      rw [Shape.logSteps, if_pos h1]; exact List.drop_eq_nil_of_le (by rw [hpt]; omega)
    have hseg : ∀ m, layerRCS sh step m = keccakRC.getD (sh.depth * (0 + 1) - step - 1) 0 :=
      fun m ↦ by rw [layerRCS, Shape.seg, if_pos h1]
    have h2 : ∑ m ∈ range 2, eqAt (claim.point.drop P) m = 1 := by
      simpa [hl] using sum_eqAt (claim.point.drop P)
    simp only [hseg]
    rw [← Finset.sum_mul, h2, one_mul, h1, Finset.sum_range_one, hd, eqKernel_getD, hsum]
    simp
  · have hlog : sh.logSteps P - 4 = P := by rw [Shape.logSteps, if_neg (by omega)]; omega
    rw [hlog, h2]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hm' := Finset.mem_range.1 hm
    rw [eqKernel_getD, hl, ite_eq_left (by simpa using hm'), hsum, layerRCS, Shape.seg,
      if_neg (by omega)]

/-- **The product check** at a shape. -/
theorem product_checkS {sh : Shape} (hsh : sh.Ok) (T : States) (step P : ℕ) (claim : KeccakClaim)
    (hshape : ClaimShape P claim) (product : List E)
    (hG : ∀ c < 47, product.getD c 0 = (Gpoly T P claim.point claim.weights).coeff c)
    (hc : projectedOf claim product + iotaOfS sh (sh.logSteps P) step claim * sumE claim.mu =
      claim.value) :
    ClaimTrue (afterRoundS sh T step) P claim := by
  rw [ClaimTrue, claimSum_roundS sh T step P _ _ _ hshape.2.1, ← hc, projectedOf,
    projected_eq claim.mu product hshape.1 _ hG, iota_eqS hsh step P claim hshape.2.1,
    sumE_mu hshape.1]

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **One layer at a shape** (`layerSpec` with `layerRCS`): from doom of "the claim holds of the
states after the round" to doom of "the next claim holds of the states before it". -/
noncomputable def layerSpecS {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (Tq : β → States) (step P : ℕ) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax)
    (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    Spec (verifyKeccakLayerS sh (sh.logSteps P) step claim)
      (Doomed C (fun q ↦ ClaimTrue (afterRoundS sh (Tq q) step) P claim ∧ R q))
      (fun c h ↦ ClaimShape P c ∧ Doomed C (fun q ↦ ClaimTrue (Tq q) P c ∧ R q) h) εmax 0 T :=
  have h3 : (L₀ : ℝ≥0∞) * errE 3 + 0 ≤ εmax := by
    rw [add_zero]; exact le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  Spec.congr (verifyKeccakLayerS_eq sh (sh.logSteps P) step claim).symm <|
  (doomReadN (T := (L₀ : ℝ≥0∞) * errE 46 + 0) hst _ (by rw [add_zero]; exact h46) 46).bind'
    fun product ↦
  (Spec.require
    (Pre := fun h ↦ product.length = 46 + 1 ∧
      Doomed C (fun q ↦ ClaimTrue (afterRoundS sh (Tq q) step) P claim ∧ R q) h)
    (Post := fun _ h ↦ product.length = 47 ∧ Doomed C (fun q ↦ (∀ c < 47, product.getD c 0 =
      (Gpoly (Tq q) P claim.point claim.weights).coeff c) ∧ R q) h)
    fun _ hpre hc ↦ ⟨hpre.1, Doomed.mono hpre.2 fun q ⟨hG, hR⟩ ↦
      ⟨product_checkS hsh (Tq q) step P claim hshape product hG hc, hR⟩⟩).bind' fun _ ↦
  if hlen : product.length = 47 then
    ((doomSample (εmax := εmax) (T := 0) hst hcard _
      (fun s q ↦ polyEval product s = (Gpoly (Tq q) P claim.point claim.weights).eval s ∧ R q)
      (errE 46) fun q hq ↦ by
        by_cases hR : R q
        · exact (avgE_mono fun s ↦ indE_mono fun hs ↦ hs.1).trans
            (s_escape hlen (natDegree_Gpoly _ _ _ _) fun h ↦ hq ⟨h, hR⟩)
        · exact (avgE_mono fun s ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
            ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)).mono
      (fun _ h ↦ h.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun s ↦
    ((packSpec (T := 0) hst hcard R (FP_eqFamily P s claim.weights Tq claim.point hshape.2.1)
      le_rfl h0 h3 claim.point [] (polyEval product s) 1 rfl).mono
      (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨by
        rw [hv, one_mul, FP_nil], hR⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res ↦
    if hres : res.2.2.length = P + 1 then
      ((sumcheckSpec (T := 0) hst hcard R
        (FX_plainFamily P s claim.weights Tq res.2.2 res.2.1) (count := 4) (by norm_num)
        (by norm_num) h0 h3 11 [] res.1 (by simp)).mono
        (fun _ (hd : res.2.2.length = claim.point.length ∧ Doomed C _ _) ↦ Doomed.mono hd.2
          fun q ⟨hv, hR⟩ ↦ ⟨by
            rw [hv, FX_nil, List.nil_append, FP_full _ _ _ _ _ _ hshape.2.1 hres], hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res2 ↦
      if hres2 : res2.1.length = 11 then
        (tailSpec hst hcard R Tq P claim hshape s res hres res2 hres2 hβ).mono
          (fun _ (hd : res2.1.length = 11 ∧ Doomed C _ _) ↦ Doomed.mono hd.2 fun q ⟨hv, hR⟩ ↦
            ⟨by rw [hv, List.nil_append, FX_full _ _ _ _ _ _ _ hres2], hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h ↦ hres2 h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h ↦ hres (h.1.trans hshape.2.1)) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl
  else Spec.dead.mono (fun _ h ↦ hlen h.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
/-! ### States at a shape

A candidate gives each segment's input at each step, `I m x` (v1: `inState h col`, the
committed column; the tape: the virtual inputs). -/

/-- The state `e` rounds into segment `m` at step `x`. -/
def segStateS (sh : Shape) (I : ℕ → ℕ → KeccakState) (m e x : ℕ) : KeccakState :=
  roundsFrom (sh.depth * m) e (I m x)

/-- The states at depth `d` (`depth - d` rounds into each segment), as bits, indexed as the
layer theory reads them (`Shape.seg`, `Shape.step`). -/
def statesOfS (sh : Shape) (P : ℕ) (I : ℕ → ℕ → KeccakState) (d : ℕ) : States :=
  fun m x j ↦ sbit (segStateS sh I (sh.seg m) (sh.depth - d) (sh.step P m x)) j

theorem statesAt_v1 (h P : ℕ) (col : ℕ → K) (d : ℕ) :
    statesAt h col d = statesOfS Shape.v1 P (inState h col) d := rfl

theorem statesOfS_round {sh : Shape} (hsh : sh.Ok) (P : ℕ) (I : ℕ → ℕ → KeccakState) {d : ℕ}
    (hd : d < sh.depth) (m x j : ℕ) (hm : m < 2) (hj : j < 1600) :
    statesOfS sh P I d m x j = afterRoundS sh (statesOfS sh P I (d + 1)) d m x j := by
  have hs := Shape.seg_lt hsh hm
  have hD := hsh.2
  generalize hsm : sh.seg m = sm at hs
  have hle : sh.depth * (sm + 1) ≤ sh.depth * sh.segments := Nat.mul_le_mul_left _ hs
  rw [mul_add, mul_one] at hle
  generalize hA : sh.depth * sm = A at hle
  have e : sh.depth - d = (sh.depth - (d + 1)) + 1 := by omega
  have hlt : A + (sh.depth - (d + 1)) < 24 := by omega
  have e2 : sh.depth * (sm + 1) - d - 1 = A + (sh.depth - (d + 1)) := by
    rw [mul_add, mul_one, hA]; omega
  rw [statesOfS, segStateS, hsm, hA, e, roundsFrom_succ hlt, sbit_round _ _ hj, afterRoundS,
    layerRCS, hsm, e2]
  show _ = roundB _ (fun j ↦ sbit (roundsFrom (sh.depth * sh.seg m) (sh.depth - (d + 1))
    (I (sh.seg m) (sh.step P m x))) j) j
  rw [hsm, hA]

theorem claimTrue_roundS {sh : Shape} (hsh : sh.Ok) (P : ℕ) (I : ℕ → ℕ → KeccakState) {d : ℕ}
    (hd : d < sh.depth) (c : KeccakClaim) :
    ClaimTrue (statesOfS sh P I d) P c ↔
      ClaimTrue (afterRoundS sh (statesOfS sh P I (d + 1)) d) P c := by
  unfold ClaimTrue
  rw [claimSum_congr P (fun m x j hm hj ↦ statesOfS_round hsh P I hd m x j hm hj)]

/-- The states at the inputs' depth on one segment: the inputs themselves, at step `i + 16·z`. -/
theorem claimTrue_inputs_tape (P : ℕ) (I : ℕ → ℕ → KeccakState) (c : KeccakClaim) :
    ClaimTrue (statesOfS Shape.tape P I 24) P c ↔
      c.value = ∑ z ∈ range (2 ^ (P + 1)), eqAt c.point z * ∑ i ∈ range 16, c.mu.getD i 0 *
        ∑ j ∈ range 1600, c.weights.getD j 0 * bitE (sbit (I 0 (i + 16 * z)) j) := by
  unfold ClaimTrue claimSum
  have e : ∀ z i j, stAt (statesOfS Shape.tape P I 24) P z i j = sbit (I 0 (i + 16 * z)) j := by
    intro z i j
    have h := Nat.mod_add_div z (2 ^ P)
    have : i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P) = i + 16 * z := by
      calc i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P)
          = i + 16 * (z % 2 ^ P + 2 ^ P * (z / 2 ^ P)) := by rw [pow_add]; ring
        _ = i + 16 * z := by rw [h]
    show sbit (roundsFrom (24 * 0) (24 - 24)
      (I 0 (i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P)))) j = _
    rw [this]; rfl
  simp only [e]

end
end LeanVM.Protocol.KeccakGkr
