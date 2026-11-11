-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/Gkr.lean` (formal rev 40f877dc) as `LvmKeccakGkr` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.Gkr

  The round-by-round soundness of the Keccak reduction `verifyKeccak`: a doom specification
  from "no candidate makes the table's output claims true" to "no candidate makes the column
  claims and slice claims the reduction leaves true", with the escape of every challenge.
-/


import LvmKeccakGkrTail

/-!
# `verifyKeccak` as a specification

`verify_keccak` (`crates/verifier/src/keccak.rs:235-294`) is `gkrProg` (by `rfl`): the segment and
lane challenges, `committed`, twelve layers, the committed outputs' opening and the inputs' opening
(`inputTail`). Candidates are stacks of type `β`, each with its `q_keccak` column `qk q` (word `n`
at `qk q n`); `C h` is the set of candidates a history binds (`Stable`, at most `L₀`).

**Alive predicates**, in order (`R` is carried throughout):

| after | a candidate `q` is alive when |
| --- | --- |
| the start | `outClaimsTrueMid` and `midAgree` at `inst` |
| `j` of the six segment and lane challenges | the mismatch table's extension at them is zero (`ZeroOn`) |
| `committed` | the first claim holds of `q`'s states, and `committed` opens `q`'s middle state |
| each layer | as in `layerSpec`; the open value is carried |
| the outputs' slot rounds | as in `sumcheckSpec`, for the family `Fo` |
| `word` and the check | the column claim at `(inst, ρ)` holds; the claim at depth `12` is carried |
| the inputs' opening | as in `inputSpec` |

**Escape bounds** (each group, `|E| = 2^192`): the start's six challenges `L₀/|E|` each (lead
`L₀·6/|E|`); per layer, `s` at `L₀·46/|E|`, each of the `P + 1` pack rounds and `11` position
rounds at `L₀·3/|E|`, `β` at `L₀·2/|E|`; the openings' `6 + 4 + 6` rounds at `L₀·2/|E|`. The
largest is `L₀·46/|E|`, which is the hypothesis `h46 : L₀·46/|E| ≤ εmax`; for `L₀ ≤ 2^12` it is
below `2^-174 < 2^-128` (`EndToEnd.Sound.phase_errors`).

`gkrSpec` states it with `Pre := Doomed C (outClaimsTrueMid ∧ midAgree ∧ R)`. The statement in
terms of `keccakF` of the inputs needs `RegionValid` (the committed middle state is twelve
rounds of the input at every step): `gkrSpec_regionValid`, from `Doomed C (outClaimsTrue ∧
RegionValid ∧ R)` to doom of the reduction's claims with `RegionValid` carried. `RegionValid`
cannot be dropped from the carried predicate: `inst` is drawn before this phase, and a middle
state wrong at some step but agreeing with twelve rounds of the input at `inst` passes every
check here (the phase drawing `inst` charges that, `zeroOn_escape`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

section

/-! ## The program -/

/-- `verify_keccak`, the `do` block's join points inlined. -/
def gkrProg (h : ℕ) (inst output : List E) : VerifierProgram (List ColumnClaim × List E × List E) :=
  VerifierProgram.sampleChallenges keccakSegmentBits >>= fun segment ↦
  VerifierProgram.sampleChallenges keccakLaneBits >>= fun lanesPt ↦
  VerifierProgram.readScalar >>= fun committed ↦
  keccakLayers h (List.range keccakDepth) (firstClaim inst segment lanesPt output committed) >>=
    fun claim ↦
  keccakOpen h (firstClaim inst segment lanesPt output committed) 1 (keccakSegments - 1)
    committed >>= fun x ↦
  VerifierProgram.readScalar >>= fun word ↦
  VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
  inputTail h claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)]

theorem verifyKeccak_eq (h : ℕ) (inst output : List E) :
    verifyKeccak h inst output = gkrProg h inst output := rfl

/-! ## The committed outputs' check -/

/-- **The outputs' check**: a true column claim and the check give the slot rounds' last
claim. -/
theorem final_out (P : ℕ) (col : ℕ → K) {inst segment lanesPt output : List E}
    (hi : inst.length = P + 4) (committed : E) {slot : List E} (hslot : slot.length = 6)
    (word value : E)
    (htrue : colTrue (P + 4) col ⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ slot, word⟩)
    (hc : ((foldAll slot (keccakSlotWeights (P + 4)
      (firstClaim inst segment lanesPt output committed) 1 1)).headD []).headD 0 * word = value) :
    value = Fo (P + 4) col inst segment lanesPt slot := by
  rw [← hc, fold_out hi committed hslot, Fo, cubeSum_full _ hslot]
  refine congrArg (HMul.hMul _) ?_
  obtain ⟨-, -, hv⟩ := htrue
  change word = _ at hv
  rw [hv, List.take_append_drop, ← hslot, col_split hi, Qo, hslot]
  rfl

/-- v1's openings after the layers (the end of `gkrProg`). -/
def v1Tail (h : ℕ) (inst output segment lanesPt : List E) (committed : E) (claim : KeccakClaim) :
    VerifierProgram (List ColumnClaim × List E × List E) :=
  keccakOpen h (firstClaim inst segment lanesPt output committed) 1 (keccakSegments - 1)
    committed >>= fun x ↦
  VerifierProgram.readScalar >>= fun word ↦
  VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
  inputTail h claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)]

/-! ## The specification -/

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- The alive predicate after `committed`. -/
def AliveC (qk : β → ℕ → K) (R : β → Prop) (P : ℕ) (inst segment lanesPt output : List E)
    (committed : E) (q : β) : Prop :=
  ClaimTrue (statesAt (P + 4) (qk q) 0) P (firstClaim inst segment lanesPt output committed) ∧
    (OpenTrue (P + 4) (qk q) inst segment lanesPt committed ∧ R q)

/-- The postcondition: the column claims and the slice claims. -/
def KeccakPost (qk : β → ℕ → K) (R : β → Prop) (P : ℕ) (C : List Ev → Set β)
    (res : List ColumnClaim × List E × List E) (h : List Ev) : Prop :=
  Doomed C (fun q ↦ (∀ c ∈ res.1, colTrue (P + 4) (qk q) c) ∧
    slicesTrue (P + 4) (qk q) res.2.1 res.2.2 ∧ R q) h

open Classical in
/-- v1's openings after the layers (`v1Tail`): the committed outputs' slot rounds and check, then
the inputs' opening. Lead `0`. -/
noncomputable def outTailSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst segment lanesPt : List E} (output : List E)
    (hi : inst.length = P + 4) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (committed : E) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (claim : KeccakClaim)
    (hc : ClaimShape P claim) :
    Spec (v1Tail (P + 4) inst output segment lanesPt committed claim)
      (Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧
        (OpenTrue (P + 4) (qk q) inst segment lanesPt committed ∧ R q)))
      (KeccakPost qk R P C) εmax 0 T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  have h2 : (L₀ : ℝ≥0∞) * errE 2 ≤ εmax := le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  have h2' : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by rw [add_zero]; exact h2
  let first := firstClaim inst segment lanesPt output committed
  (Spec.congr (keccakOpen_eq (P + 4) first 1 (keccakSegments - 1) committed).symm <|
    Spec.congr (p := sumcheck committed 3 (List.replicate 6 none) >>= fun x ↦
      VerifierProgram.ret (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD
          [], x.2))
      (by rw [qkeccakSlotBits_eq]; rfl) <|
    ((sumcheckSpec (T := 0) hst hcard
      (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)
      (Fo_plainFamily (P + 4) qk inst segment lanesPt) (count := 3) (by norm_num)
      (by norm_num) h0 h2' 6 [] committed (by simp)).mono
      (fun _ (hd : Doomed C _ _) ↦ Doomed.mono hd
        fun q ⟨hv, hct, hR⟩ ↦ ⟨hct, by
          rw [OpenTrue, hv, Fo_nil (P + 4) (qk q) inst hs hl], hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun x ↦
    (Spec.ret (Post := fun (x' : List E × List E × E) h ↦ x'.1.length = 6 ∧
        x'.2.1 = (foldAll x'.1 (keccakSlotWeights (P + 4) first 1 1)).headD [] ∧
        Doomed C (fun q ↦ x'.2.2 = Fo (P + 4) (qk q) inst segment lanesPt x'.1 ∧
          (ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)) h)
      (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD [], x.2)).mono
      (fun _ hd ↦ ⟨hd.1, rfl, by simpa using hd.2⟩) (fun _ _ h' ↦ h') le_rfl le_rfl
      le_rfl).bind' fun x ↦
  if hx : x.1.length = 6 ∧
      x.2.1 = (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD [] then
    ((doomRead (T := 0) hst _ h0).mono (fun _ hd ↦ hd.2.2) (fun _ _ h' ↦ h') le_rfl le_rfl
      le_rfl).bind' fun word ↦
    (Spec.require
      (Pre := Doomed C (fun q ↦ x.2.2 = Fo (P + 4) (qk q) inst segment lanesPt x.1 ∧
          (ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)))
      (Post := fun _ h ↦ Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧
        ((∀ c ∈ [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)],
          colTrue (P + 4) (qk q) c) ∧ R q)) h)
      fun _ hd hcheck ↦ Doomed.mono hd fun q ⟨hct, hcol, hR⟩ ↦ ⟨by
        rw [hx.2] at hcheck
        exact final_out P (qk q) hi committed hx.1 word _ (hcol _ (List.mem_singleton_self _))
          hcheck, hct, hR⟩).bind' fun _ ↦
    (inputSpec hst hcard _ qk P claim hc _ hT h2).mono (fun _ h' ↦ h')
      (fun res h' (hr : res.1 = _ ∧ _) ↦ Doomed.mono hr.2 fun q ⟨hcol, hsl, hR⟩ ↦
        ⟨hsl, by rw [← hr.1]; exact hcol, hR⟩) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hx ⟨hd.1, hd.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

open Classical in
/-- After `committed`: the layers and the two openings. Lead `0`. -/
noncomputable def midSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst segment lanesPt : List E} (output : List E)
    (hi : inst.length = P + 4) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (committed : E) (hT : T ≤ εmax)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (keccakLayers (P + 4) (List.range keccakDepth)
        (firstClaim inst segment lanesPt output committed) >>= fun claim ↦
      keccakOpen (P + 4) (firstClaim inst segment lanesPt output committed) 1 (keccakSegments - 1)
        committed >>= fun x ↦
      VerifierProgram.readScalar >>= fun word ↦
      VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
      inputTail (P + 4) claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)])
      (Doomed C (AliveC qk R P inst segment lanesPt output committed))
      (KeccakPost qk R P C) εmax 0 T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  have h2 : (L₀ : ℝ≥0∞) * errE 2 ≤ εmax := le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  have h2' : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by rw [add_zero]; exact h2
  let first := firstClaim inst segment lanesPt output committed
  (Spec.congr (p := keccakLayers (P + 4) (List.range' 0 12) first) (by rw [List.range_eq_range']; rfl)
    (layersSpec (T := 0) hst hcard (fun q ↦ OpenTrue (P + 4) (qk q) inst segment lanesPt committed ∧ R q)
      qk P h46 h2' 12 0 rfl first (firstClaim_shape committed hi hs))).bind' fun claim ↦
  if hc : ClaimShape P claim then
    (outTailSpec hst hcard R qk P output hi hs hl committed hT h46 claim hc).mono
      (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-! ## The start -/

/-- The escape bound of the `i`-th of `n` zero-test coordinates (`1` past them, never used). -/
noncomputable def ztE (n i : ℕ) : ℝ≥0∞ := if i < n then errE 1 else 1

omit [Finite β] in
theorem zt_escape (δ : β → ℕ → E) (R : β → Prop) (pre : List E) {n : ℕ}
    (hpre : pre.length + n = 6) (acc : List E) (q : β)
    (hq : ¬ (ZeroOn (δ q) (pre ++ acc) 6 ∧ R q)) :
    avgE (fun c ↦ indE (ZeroOn (δ q) (pre ++ (acc ++ [c])) 6 ∧ R q)) ≤ ztE n acc.length := by
  unfold ztE
  split_ifs with hn
  · by_cases hR : R q
    · refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (zeroOn_escape (δ q) (acc := pre ++ acc) (by simp; omega) fun h ↦ hq ⟨h, hR⟩)
      rw [List.append_assoc]; exact hc.1
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · exact avgE_indE_le_one _

theorem keccakSegmentBits_eq : keccakSegmentBits = 1 := by decide

theorem lead_eq (L₀ : ℕ) :
    (∑ i ∈ range 1, (L₀ : ℝ≥0∞) * ztE 6 (0 + i)) +
        ((∑ i ∈ range 5, (L₀ : ℝ≥0∞) * ztE 5 (0 + i)) + 0) = (L₀ : ℝ≥0∞) * errE 6 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ztE, errE]
  norm_num
  ring

/-! ## The reduction at a shape (lvm2 T-G)

`gkrProgS sh h inst output k`: the segment and lane challenges, `committed` (read with two
segments, `0` with one), `sh.depth` layers from the first claim, then the continuation `k` on the
challenges, `committed` and the claim on the inputs. v1's `gkrProg` is `gkrProgS Shape.v1` with
the openings of the committed outputs and inputs as `k` (`gkrProg_v1`); the tape's reduction
(BLUEPRINT2 T2) is `gkrProgS Shape.tape` with `k` returning the claim (`tapeGkr`).

`gkrSpecS`: from doom of "the output claims and the segments' agreement hold at `inst`" to the
continuation's specification, with doom of "the claim on the inputs holds and `committed` is
open" (`AliveKS`). Lead `L₀·(segBits + 5)/|E|`; each layer's groups as in `layerSpecS`. The layers
are one recursive specification (`layersSpecS`), not unrolled. -/

/-- The reduction at a shape, with the continuation `k` after the layers. -/
def gkrProgS {α : Type} (sh : Shape) (h : ℕ) (inst output : List E)
    (k : List E → List E → E → KeccakClaim → VerifierProgram α) : VerifierProgram α :=
  VerifierProgram.sampleChallenges sh.segBits >>= fun segment ↦
  VerifierProgram.sampleChallenges keccakLaneBits >>= fun lanesPt ↦
  (if 1 < sh.segments then VerifierProgram.readScalar else pure 0) >>= fun committed ↦
  keccakLayersS sh h (List.range sh.depth) (firstClaimS sh inst segment lanesPt output committed) >>=
    fun claim ↦
  k segment lanesPt committed claim

theorem gkrProg_v1 (h : ℕ) (inst output : List E) :
    gkrProg h inst output = gkrProgS Shape.v1 h inst output (v1Tail h inst output) := by
  simp only [gkrProg, gkrProgS, keccakLayers_v1]
  rfl

/-- **The tape's reduction** (BLUEPRINT2 §1.2 T2): `24 × 1`, no openings; it returns the claim on
the inputs. -/
def tapeGkr (h : ℕ) (inst output : List E) : VerifierProgram KeccakClaim :=
  gkrProgS Shape.tape h inst output fun _ _ _ claim ↦ pure claim


open Classical in
/-- **The layers at a shape, from depth `d`** (at least one): lead `0`; each layer's groups as in
`layerSpecS`, the last one's follower lead `T`. -/
noncomputable def layersSpecS {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    (n d : ℕ) → d + n + 1 = sh.depth → (claim : KeccakClaim) → ClaimShape P claim →
      Spec (keccakLayersS sh (sh.logSteps P) (List.range' d (n + 1)) claim)
        (Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) d) P claim ∧ R q))
        (fun c h ↦ ClaimShape P c ∧
          Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) εmax 0 T
  | 0, d, hd, claim, hs =>
    ((layerSpecS (T := T) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      h46 hβ).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundS hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    (Spec.ret (Post := fun c h ↦ ClaimShape P c ∧
        Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) c).mono
      (fun _ h' ↦ by rw [show d + 1 = sh.depth by omega] at h'; exact h') (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl
  | n + 1, d, hd, claim, hs =>
    ((layerSpecS (T := T) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      h46 hβ).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundS hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    if hc : ClaimShape P c then
      (layersSpecS hsh hst hcard R Iq P h46 hβ n (d + 1) (by omega) c hc).mono
        (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl zero_le le_rfl
    else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- The alive predicate after `committed`, at a shape. -/
def AliveKS (sh : Shape) (Iq : β → ℕ → ℕ → KeccakState) (R : β → Prop) (P : ℕ)
    (inst segment lanesPt output : List E) (committed : E) (q : β) : Prop :=
  ClaimTrue (statesOfS sh P (Iq q) 0) P (firstClaimS sh inst segment lanesPt output committed) ∧
    (OpenTrueS sh (sh.logSteps P) (Iq q) inst segment lanesPt committed ∧ R q)

omit [Finite β] in
/-- The escape of the `i`-th of `n` zero-test coordinates (`zt_escape` on `n` bits). -/
theorem zt_escapeS {n : ℕ} (δ : β → ℕ → E) (R : β → Prop) (pre : List E) {k : ℕ}
    (hpre : pre.length + k = n) (acc : List E) (q : β)
    (hq : ¬ (ZeroOn (δ q) (pre ++ acc) n ∧ R q)) :
    avgE (fun c ↦ indE (ZeroOn (δ q) (pre ++ (acc ++ [c])) n ∧ R q)) ≤ ztE k acc.length := by
  unfold ztE
  split_ifs with hn
  · by_cases hR : R q
    · refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (zeroOn_escape (δ q) (acc := pre ++ acc) (by simp; omega) fun h ↦ hq ⟨h, hR⟩)
      rw [List.append_assoc]; exact hc.1
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · exact avgE_indE_le_one _

theorem lead_eqS (L₀ b : ℕ) :
    (∑ i ∈ range b, (L₀ : ℝ≥0∞) * ztE (b + 5) (0 + i)) +
        ((∑ i ∈ range 5, (L₀ : ℝ≥0∞) * ztE 5 (0 + i)) + 0) = (L₀ : ℝ≥0∞) * errE (b + 5) := by
  have e1 : ∀ n k, n ≤ k → ∑ i ∈ range n, (L₀ : ℝ≥0∞) * ztE k (0 + i) =
      n * ((L₀ : ℝ≥0∞) * errE 1) := by
    intro n k hnk
    rw [Finset.sum_congr rfl fun i hi ↦ by
      rw [ztE, if_pos (by have := Finset.mem_range.1 hi; omega)], Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  rw [e1 b (b + 5) (by omega), e1 5 5 le_rfl, errE, errE]
  push_cast
  ring

theorem depth_pos {sh : Shape} (hsh : sh.Ok) : 0 < sh.depth := by
  rcases Nat.eq_zero_or_pos sh.depth with h | h
  · have := hsh.2; rw [h, zero_mul] at this; omega
  · exact h

open Classical in
/-- After `committed`, at a shape: the layers, then the continuation. Lead `0`. -/
noncomputable def midSpecS {α : Type} {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    {inst segment lanesPt : List E} (output : List E) (hi : inst.length = sh.logSteps P)
    (hs : segment.length = sh.segBits) (hl : lanesPt.length = 5) (committed : E)
    (hc0 : sh.segments = 1 → committed = 0)
    {Tk : ℝ≥0∞} {Post : α → List Ev → Prop}
    (k : List E → List E → E → KeccakClaim → VerifierProgram α)
    (hk : ∀ claim, ClaimShape P claim →
      Spec (k segment lanesPt committed claim)
        (Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) sh.depth) P claim ∧
          (OpenTrueS sh (sh.logSteps P) (Iq q) inst segment lanesPt committed ∧ R q)))
        Post εmax Tk T)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (hβ : (L₀ : ℝ≥0∞) * errE 2 + Tk ≤ εmax) :
    Spec (keccakLayersS sh (sh.logSteps P) (List.range sh.depth)
        (firstClaimS sh inst segment lanesPt output committed) >>= fun claim ↦
      k segment lanesPt committed claim)
      (Doomed C (AliveKS sh Iq R P inst segment lanesPt output committed)) Post εmax 0 T :=
  have hd := depth_pos hsh
  Spec.congr (p := keccakLayersS sh (sh.logSteps P) (List.range' 0 (sh.depth - 1 + 1))
      (firstClaimS sh inst segment lanesPt output committed) >>= fun claim ↦
      k segment lanesPt committed claim)
    (by rw [show sh.depth - 1 + 1 = sh.depth by omega, List.range_eq_range']) <|
  ((layersSpecS (T := Tk) hsh hst hcard
      (fun q ↦ OpenTrueS sh (sh.logSteps P) (Iq q) inst segment lanesPt committed ∧ R q) Iq P h46 hβ
      (sh.depth - 1) 0 (by omega) _ (firstClaimS_shape hsh committed hi hs)).mono
    (fun _ h' ↦ h') (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun claim ↦
  if hc : ClaimShape P claim then
    (hk claim hc).mono (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

open Classical in
/-- `committed`: read with two segments, `0` with one. Lead `0`. -/
noncomputable def committedSpecS {sh : Shape} (hsh : sh.Ok) (hst : Stable C) (R : β → Prop)
    (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ) {inst segment lanesPt output : List E}
    (hi : inst.length = sh.logSteps P) (ho : output.length = 25)
    (hs : segment.length = sh.segBits) (hl : lanesPt.length = 5) (h0 : (0 : ℝ≥0∞) ≤ εmax) :
    Spec (if 1 < sh.segments then VerifierProgram.readScalar else pure 0)
      (fun h ↦ lanesPt.length = 5 ∧ Doomed C (fun q ↦ ZeroOn
        (startDeltaS sh (sh.logSteps P) (Iq q) inst output) (segment ++ ([] ++ lanesPt))
        (sh.segBits + 5) ∧ R q) h)
      (fun c h ↦ (sh.segments = 1 → c = 0) ∧
        Doomed C (AliveKS sh Iq R P inst segment lanesPt output c) h) εmax 0 0 :=
  Spec.ite
    (fun hseg ↦ Spec.readE (fun h₀ c hd ↦ ⟨fun h1 ↦ absurd h1 (by omega),
      (Doomed.append hst rfl).mpr (Doomed.mono hd.2 fun q ⟨htrue, hopen, hR⟩ ↦
        ⟨by rw [List.nil_append]; exact zeroOn_of_firstS hsh P (Iq q) hi hs hl ho c hopen htrue,
          hR⟩)⟩) h0)
    (fun _ ↦ (Spec.ret (Post := fun c h ↦ (sh.segments = 1 → c = 0) ∧
        Doomed C (AliveKS sh Iq R P inst segment lanesPt output c) h) 0).mono
      (fun _ hd ↦ ⟨fun _ ↦ rfl, Doomed.mono hd.2 fun q ⟨htrue, hopen, hR⟩ ↦
        ⟨by rw [List.nil_append]; exact zeroOn_of_firstS hsh P (Iq q) hi hs hl ho 0 hopen htrue,
          hR⟩⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl)

open Classical in
/-- **The Keccak reduction at a shape**, round by round, up to the continuation `k`: from doom
of "the output claims and the segments' agreement hold at `inst`" to `k`'s postcondition. Lead
`L₀·(segBits + 5)/|E|`; the layers' groups `L₀·46/|E|`, `L₀·3/|E|`, `L₀·2/|E|`; `k`'s lead `Tk`. -/
noncomputable def gkrSpecS {α : Type} {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    {inst output : List E} (hi : inst.length = sh.logSteps P) (ho : output.length = 25)
    {Tk : ℝ≥0∞} {Post : α → List Ev → Prop}
    (k : List E → List E → E → KeccakClaim → VerifierProgram α)
    (hk : ∀ segment lanesPt committed claim, segment.length = sh.segBits → lanesPt.length = 5 →
      ClaimShape P claim → (sh.segments = 1 → committed = 0) →
      Spec (k segment lanesPt committed claim)
        (Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) sh.depth) P claim ∧
          (OpenTrueS sh (sh.logSteps P) (Iq q) inst segment lanesPt committed ∧ R q)))
        Post εmax Tk T)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (hβ : (L₀ : ℝ≥0∞) * errE 2 + Tk ≤ εmax) :
    Spec (gkrProgS sh (sh.logSteps P) inst output k)
      (Doomed C (fun q ↦ outClaimsTrueMidS sh (sh.logSteps P) (Iq q) inst output ∧
        midAgreeS sh (sh.logSteps P) (Iq q) inst ∧ R q))
      Post εmax ((L₀ : ℝ≥0∞) * errE (sh.segBits + 5)) T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  let δ := fun q ↦ startDeltaS sh (sh.logSteps P) (Iq q) inst output
  ((doomSampleN (εmax := εmax) hst hcard
    (fun acc q ↦ ZeroOn (δ q) ([] ++ acc) (sh.segBits + 5) ∧ R q)
    (ztE (sh.segBits + 5)) (fun acc q hq ↦ zt_escapeS δ R [] (by simp) acc q hq) sh.segBits
    []).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ by
      obtain ⟨h1, h2⟩ := claims_of_zeroOnS hsh _ (Iq q) inst output (by simpa using hz)
      exact ⟨h1, h2, hR⟩)
    (fun _ _ h' ↦ h') le_rfl (le_of_eq (lead_eqS L₀ sh.segBits)) le_rfl).bind' fun segment ↦
  if hs : segment.length = sh.segBits then
    ((doomSampleN (εmax := εmax) hst hcard
      (fun acc q ↦ ZeroOn (δ q) (segment ++ acc) (sh.segBits + 5) ∧ R q)
      (ztE 5) (fun acc q hq ↦ zt_escapeS δ R segment (by rw [hs]) acc q hq) 5 []).mono
      (fun _ (hd : segment.length = sh.segBits ∧ _) ↦ by simpa using hd.2) (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl).bind' fun lanesPt ↦
    if hl : lanesPt.length = 5 then
      (committedSpecS hsh hst R Iq P hi ho hs hl h0).bind' fun committed ↦
      if hc0 : sh.segments = 1 → committed = 0 then
        (midSpecS hsh hst hcard R Iq P output hi hs hl committed hc0 k
          (fun claim hc ↦ hk segment lanesPt committed claim hs hl hc hc0) h46 hβ).mono
          (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h' ↦ hc0 h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hl hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-! ### The tape: `24 × 1` -/

theorem keccakF_roundsFrom (a : KeccakState) : keccakF1600 a = roundsFrom 0 24 a := rfl

/-- The tape's states on the inputs `I` (one segment): row `x`'s state after `24 - d` rounds. -/
abbrev tapeStates (P : ℕ) (I : ℕ → KeccakState) (d : ℕ) : States :=
  statesOfS Shape.tape P (fun _ ↦ I) d

/-- **The tape's input claim** (BLUEPRINT2 T2's `C_in = Σ_i ι(i)·⟨ω, in(i)⟩`): a claim holds of the
tape's inputs when its value is `Σ_x eq(point, x ≫ 4)·μ[x & 15]·⟨w, bits(I x)⟩` over the
`2^(P+5)` rows. -/
theorem claimTrue_tapeStates (P : ℕ) (I : ℕ → KeccakState) (c : KeccakClaim) :
    ClaimTrue (tapeStates P I 24) P c ↔
      c.value = ∑ x ∈ range (2 ^ (P + 5)), eqAt c.point (x / 16) * c.mu.getD (x % 16) 0 *
        ∑ j ∈ range 1600, c.weights.getD j 0 * bitE (sbit (I x) j) := by
  rw [tapeStates, claimTrue_inputs_tape,
    show 2 ^ (P + 5) = 2 ^ (P + 1) * 16 by rw [show P + 5 = (P + 1) + 4 from rfl, pow_add]; rfl,
    sum_range_mul]
  refine Iff.of_eq (congrArg _ (Finset.sum_congr rfl fun z _ ↦ ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  rw [show (16 * z + i) / 16 = z by omega, show (16 * z + i) % 16 = i by omega,
    show i + 16 * z = 16 * z + i by ring]
  ring

/-- The tape's first claim (`firstClaimS Shape.tape` with no segment and `committed = 0`): the
lanes of the outputs at `inst`, combined at `lanesPt`. -/
def tapeFirstClaim (inst lanesPt output : List E) : KeccakClaim :=
  ⟨dot ((eqKernel lanesPt).take 25) output, eqKernel (inst.take 4), inst.drop 4,
    firstWeights lanesPt⟩

theorem firstClaimS_tape (inst lanesPt output : List E) :
    firstClaimS Shape.tape inst [] lanesPt output 0 = tapeFirstClaim inst lanesPt output := by
  have e : (eqKernel ([] : List E)).getD (Shape.tape.segments - 1) 0 = 1 := by
    rw [eqKernel_getD, show Shape.tape.segments - 1 = 0 from rfl]; simp
  simp only [firstClaimS, tapeFirstClaim, e, zero_add, one_mul, List.append_nil]

/-- **The tape's reduction, flat**: five lane challenges, then the `24` layers from the first
claim. No segment challenge, no `committed`, no openings. -/
theorem tapeGkr_eq (h : ℕ) (inst output : List E) :
    tapeGkr h inst output = VerifierProgram.sampleChallenges keccakLaneBits >>= fun lanesPt ↦
      keccakLayersS Shape.tape h (List.range 24) (tapeFirstClaim inst lanesPt output) := by
  simp only [tapeGkr, gkrProgS, bind_pure, ← firstClaimS_tape]
  rfl

open Classical in
/-- **The tape's reduction** (`24 × 1`, BLUEPRINT2 T2): from doom of "the `25` output-lane claims
`Σ_x eq(inst, x)·lane_l(keccakF(I x)) = output_l` hold" to doom of "the returned claim holds of the
inputs" (`claimTrue_inputs_tape` spells it out: `value = Σ_i eq(point, i ≫ 4)·μ[i & 15]·⟨w, I i⟩`).
Lead `L₀·5/|E|`; per layer `L₀·46/|E|` (`s`), `L₀·3/|E|` (each of the `P + 1 + 11` rounds),
`L₀·2/|E|` (`β`); the follower's lead `T`. `logSteps = P + 5` (at least `5`); the caller states the
row count (leanVM's shape check, `keccak.rs:243-246`, is the caller's: `n_log = 21`, `P = 16`). -/
noncomputable def tapeGkrSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (Iq : β → ℕ → KeccakState) (P : ℕ) {inst output : List E} (hi : inst.length = P + 5)
    (ho : output.length = 25) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax)
    (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    Spec (tapeGkr (P + 5) inst output)
      (Doomed C (fun q ↦ (∀ l < 25, stepMle (P + 5) inst
        (fun x ↦ laneWord (keccakF1600 (Iq q x)) l) = output.getD l 0) ∧ R q))
      (fun c h ↦ ClaimShape P c ∧ Doomed C (fun q ↦ ClaimTrue (tapeStates P (Iq q) 24) P c ∧ R q) h)
      εmax ((L₀ : ℝ≥0∞) * errE 5) T :=
  (gkrSpecS Shape.tape_ok hst hcard R (fun q _ ↦ Iq q) P hi ho (fun _ _ _ claim ↦ pure claim)
    (fun _ _ committed claim _ _ hc hc0 ↦
      (Spec.ret (Post := fun c h ↦ ClaimShape P c ∧
          Doomed C (fun q ↦ ClaimTrue (tapeStates P (Iq q) 24) P c ∧ R q) h) claim).mono
        (fun _ hd ↦ ⟨hc, Doomed.mono hd fun q ⟨hct, hR⟩ ↦
          ⟨hct, by rw [OpenTrueS, if_pos (show Shape.tape.segments = 1 from rfl)]; exact hc0 rfl, hR⟩⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl) h46 hβ).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hout, _, hR⟩ ↦ ⟨fun l hl ↦ hout l hl, hR⟩)
    (fun _ _ h' ↦ h') le_rfl (le_of_eq (by rw [Shape.tape_segBits])) le_rfl

open Classical in
/-- **The Keccak reduction** (`verify_keccak`, `keccak.rs:235-294`), round by round: from
doom of "the output-lane claims (against the committed middle state) and the middle state's
claims hold at `inst`" to doom of "the column claims and the `64` slice claims it leaves hold".
Lead `L₀·6/|E|` (the segment and lane challenges); every other group's lead is at most
`L₀·46/|E| ≤ εmax`; the follower's lead `T` after the slices. -/
noncomputable def gkrSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst output : List E} (hi : inst.length = P + 4)
    (ho : output.length = 25) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (verifyKeccak (P + 4) inst output)
      (Doomed C (fun q ↦ outClaimsTrueMid (P + 4) (qk q) inst output ∧
        midAgree (P + 4) (qk q) inst ∧ R q))
      (KeccakPost qk R P C) εmax ((L₀ : ℝ≥0∞) * errE 6) T :=
  have h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by
    rw [add_zero]; exact le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  Spec.congr ((gkrProg_v1 (P + 4) inst output).symm.trans (verifyKeccak_eq (P + 4) inst output).symm) <|
  (gkrSpecS Shape.v1_ok hst hcard R (fun q ↦ inState (P + 4) (qk q)) P hi ho
    (v1Tail (P + 4) inst output)
    (fun segment lanesPt committed claim hs hl hc _ ↦
      (outTailSpec hst hcard R qk P output hi (hs.trans Shape.v1_segBits) hl committed hT h46 claim
        hc).mono
        (fun _ hd ↦ Doomed.mono hd fun q ⟨hct, hopen, hR⟩ ↦
          ⟨hct, (openTrue_v1 _ _ _ _ _ _).1 hopen, hR⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl) h46 h2).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hmid, hagree, hR⟩ ↦
      ⟨hmid, (midAgree_v1 _ _ _).2 hagree, hR⟩)
    (fun _ _ h' ↦ h') le_rfl (le_of_eq (by rw [Shape.v1_segBits])) le_rfl

/-! ## The statement against `keccakF` -/

theorem outClaims_iff_of_regionValid (h : ℕ) (col : ℕ → K) (inst output : List E)
    (hv : RegionValid h col) :
    outClaimsTrue h col inst output ↔ outClaimsTrueMid h col inst output := by
  have hx : ∀ x ∈ range (2 ^ h), keccakF1600 (inState h col 0 x) = roundsFrom 12 12 (inState h col 1 x) :=
    fun x hx ↦ by rw [keccakF_eq, hv x (Finset.mem_range.1 hx)]
  have e : ∀ l, stepMle h inst (fun x ↦ laneWord (keccakF1600 (inState h col 0 x)) l) =
      stepMle h inst (fun x ↦ laneWord (roundsFrom 12 12 (inState h col 1 x)) l) := fun l ↦
    Finset.sum_congr rfl fun x hxr ↦ by simp only; rw [hx x hxr]
  unfold outClaimsTrue outClaimsTrueMid
  simp only [e]

/-- **The Keccak reduction against `keccakF`**: from doom of "the output-lane claims against
`keccakF` of the inputs hold at `inst`, the region is valid, and `R`", to doom of the reduction's
claims with `RegionValid` and `R` carried. -/
noncomputable def gkrSpec_regionValid (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) (qk : β → ℕ → K) (P : ℕ) {inst output : List E} (hi : inst.length = P + 4)
    (ho : output.length = 25) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (verifyKeccak (P + 4) inst output)
      (Doomed C (fun q ↦ outClaimsTrue (P + 4) (qk q) inst output ∧
        RegionValid (P + 4) (qk q) ∧ R q))
      (KeccakPost qk (fun q ↦ RegionValid (P + 4) (qk q) ∧ R q) P C) εmax
      ((L₀ : ℝ≥0∞) * errE 6) T :=
  (gkrSpec hst hcard (fun q ↦ RegionValid (P + 4) (qk q) ∧ R q) qk P hi ho hT h46).mono
    (fun _ hd ↦ Doomed.mono hd fun _ ⟨hmid, _, hv, hR⟩ ↦
      ⟨(outClaims_iff_of_regionValid _ _ _ _ hv).2 hmid, hv, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- A column given on `Fin (2^(h + 6))`, read as words of `ℕ` (`0` past the end). -/
def colOfFin {h : ℕ} (c : Fin (2 ^ (h + 6)) → K) : ℕ → K :=
  fun n ↦ if hn : n < 2 ^ (h + 6) then c ⟨n, hn⟩ else 0


end
end LeanVM.Protocol.KeccakGkr
