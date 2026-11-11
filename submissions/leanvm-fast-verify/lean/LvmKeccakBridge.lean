-- Ported from leanVM (formal rev 40f877dc) for lvm (WP-2) as `LvmKeccakBridge`: the generic parts of
-- `EndToEnd/Sound/Returns.lean` (the return invariant `RetOK`, lines 46-107), of
-- `EndToEnd/Front/LayoutBridgeB.lean` (`castColumn`, `holds_castColumn`, `sum_eqEval_mul`, lines
-- 37-56) and of `EndToEnd/Front/KeccakBridge.lean` (the returns of the Keccak reduction and the
-- equality weights, lines 57-234). Cut (leanISA): `retOK_verifyBusBalance` ... `retOK_publicInputPhase`
-- of Returns, the candidate reading of LayoutBridgeB (`toI`, `WireHolds`, ...), and from KeccakBridge
-- line 235 on (`q_keccak` on a leanISA candidate, `tablePost_pubPre`, `keccakPhaseSpec`): the Keccak
-- phase spec over the leanISA layout. lvm's Keccak phase (caller claims, WP-8) uses `gkrSpec`
-- (`LvmKeccakGkr`) directly.
import LvmKeccakGkr
import LvmClaims
import LvmEqLemmas
import LvmLayoutArith
import LvmSpineKeccakZero
import LvmSpecRulesBasic

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

section

variable {α β : Type}

variable {α β : Type}

/-! ## The return invariant -/

/-- Every return of `p` satisfies `Q`. -/
def RetOK (Q : α → Prop) (p : VerifierProgram α) : Prop :=
  ∀ (l : List Ev) (a : α), p.after l = some (.ret a) → Q a

/-- A weaker predicate holds of every return. -/
theorem RetOK.mono {Q Q' : α → Prop} {p : VerifierProgram α} (h : RetOK Q p) (hQ : ∀ a, Q a →
    Q' a) :
    RetOK Q' p :=
  fun l a hl ↦ hQ a (h l a hl)

/-- A program that returns at once returns its value. -/
theorem RetOK.ret {Q : α → Prop} {a : α} (h : Q a) : RetOK Q (VerifierProgram.ret a) := by
  intro l b hl
  cases l with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq, VerifierProgram.ret.injEq] at hl
    exact hl ▸ h
  | cons e l => cases e <;> simp [VerifierProgram.after] at hl

/-- A rejecting program returns nothing. -/
theorem RetOK.fail {Q : α → Prop} : RetOK Q (VerifierProgram.fail : VerifierProgram α) := by
  intro l b hl
  cases l with
  | nil => simp [VerifierProgram.after] at hl
  | cons e l => cases e <;> simp [VerifierProgram.after] at hl

/-- The trivial predicate holds of every return. -/
theorem RetOK.true (p : VerifierProgram α) : RetOK (fun _ ↦ True) p :=
  fun _ _ _ ↦ trivial

/-- A sequence that returns at once: both parts return. -/
private theorem bind_eq_ret' {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β} (h : p.bind
    f = .ret b) :
    ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [VerifierProgram.bind]

/-- A sequence returns what its continuation returns on a return of its first part. -/
theorem RetOK.bind {Q' : α → Prop} {Q : β → Prop} {p : VerifierProgram α} {f : α →
    VerifierProgram β}
    (hp : RetOK Q' p) (hf : ∀ a, Q' a → RetOK Q (f a)) : RetOK Q (p.bind f) := by
  intro l b hl
  rcases VerifierProgram.after_bind_cases f hl with ⟨q, hq, hr⟩ | ⟨a, l₁, l₂, -, h1, -, h2⟩
  · obtain ⟨a, rfl, hfa⟩ := bind_eq_ret' hr.symm
    exact hf a (hp l a hq) [] b (by simp [VerifierProgram.after, hfa])
  · exact hf a (hp l₁ a h1) l₂ b h2

/-- A sequence whose continuation's returns satisfy `Q` whatever the first part returns. -/
theorem RetOK.bind_true {Q : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hf : ∀ a, RetOK Q (f a)) : RetOK Q (p.bind f) :=
  (RetOK.true p).bind fun a _ ↦ hf a

/-- `readN n` returns `n` scalars. -/
theorem RetOK.readN : ∀ n : ℕ, RetOK (fun xs : List E ↦ xs.length = n)
    (VerifierProgram.readScalars n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (RetOK.readN n).bind fun xs hxs ↦
      RetOK.ret (by simp [hxs])


end

end LeanVM.Protocol.EndToEnd.Sound

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
open LeanVM.Protocol.EndToEnd.Sound (RetOK RetOK.ret RetOK.bind RetOK.bind_true)
open Finset
open scoped NNReal ENNReal

section

/-! ## Stacks on equal numbers of variables -/

/-- A stack on `a` variables read on `b = a`. -/
def castColumn {a b : ℕ} (h : a = b) (q : Column a) : Column b :=
  ⟨Vector.cast (congrArg (2 ^ ·) h) q.values⟩

/-- A stack claim holds of a stack exactly when it holds of the stack read on equal variables. -/
theorem holds_castColumn {a b : ℕ} (h : a = b) (c : StackClaim) (q : Column a) :
    StackClaim.Holds a c q ↔ StackClaim.Holds b c (castColumn h q) := by
  subst h
  simp [castColumn]

/-- Pairing the equality weight of `z` with a stack is the stack's extension at `z`. -/
theorem sum_eqEval_mul {μ : ℕ} (z : Vector E μ) (q : Column μ) :
    ∑ x : Fin (2 ^ μ), eqEval z.toList (boolPoint μ x) * ofK (q.values.getD x 0) =
      eval₂Mle q.values (algebraMap K E) z := by
  rw [eval₂Mle, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqEval_boolPoint, mul_comm]
  simp [CMlPolynomialEval.map, Vector.getD, x.isLt]


/-- A sumcheck returns one challenge per round. -/
theorem retOK_sumcheck (count : ℕ) : ∀ (eqs : List (Option E)) (claim : E),
    RetOK (fun r : List E × E ↦ r.1.length = eqs.length) (Verifier.sumcheck claim count eqs)
  | [], _ => RetOK.ret rfl
  | _ :: eqs, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_sumcheck count eqs _).bind fun r hr ↦ RetOK.ret (by simp [hr])

/-- `keccak_open` returns a slot of six challenges. -/
theorem retOK_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    RetOK (fun r : List E × List E × E ↦ r.1.length = qkeccakSlotBits)
      (keccakOpen logSteps claim first count value) :=
  (retOK_sumcheck 3 _ value).bind fun r hr ↦ RetOK.ret (by simpa using hr)

/-- **The Keccak reduction's column claims are on `QKECCAK`**, at `|inst| + 6` coordinates when
`inst` has at least four. -/
theorem retOK_verifyKeccak (logSteps : ℕ) (inst output : List E) (hi : 4 ≤ inst.length) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦
      ∀ c ∈ r.1, c.column = qkeccak ∧ c.point.length = inst.length + 6)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine (retOK_keccakOpen _ _ _ _ _).bind fun r hr ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (RetOK.ret (Q := fun cs : List Verifier.ColumnClaim ↦
      ∀ c ∈ cs, c.column = qkeccak ∧ c.point.length = inst.length + 6) ?_).bind fun cs hcs ↦ ?_
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [show (slot, weights, value).1 = slot from rfl] at hr
    rw [hr, show qkeccakSlotBits = 6 by decide]
    omega
  · refine RetOK.bind_true fun r ↦ ?_
    obtain ⟨low, v⟩ := r
    refine RetOK.bind_true fun r ↦ ?_
    obtain ⟨slot', weights', value'⟩ := r
    exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hcs

/-- The Keccak reduction returns one column claim. -/
theorem retOK_verifyKeccak_count (logSteps : ℕ) (inst output : List E) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦ r.1.length ≤ 1)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (RetOK.ret (Q := fun cs : List Verifier.ColumnClaim ↦ cs.length ≤ 1) (by simp)).bind
      fun cs hcs ↦ ?_
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨low, v⟩ := r
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot', weights', value'⟩ := r
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hcs

-- lvm (WP-2): `retOK_keccakPhase` (leanISA's `keccakPhaseClaims`) is not ported.

/-- `sampleN n` returns `n` challenges. -/
theorem retOK_sampleN : ∀ n : ℕ, RetOK (fun xs : List E ↦ xs.length = n)
    (VerifierProgram.sampleChallenges n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (retOK_sampleN n).bind fun xs hxs ↦
      RetOK.ret (by simp [hxs])

/-- The pack rounds return one challenge per coordinate of the point. -/
theorem retOK_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    RetOK (fun r : E × E × List E ↦ r.2.2.length = rs.length) (keccakPackRounds rs value scale)
  | [], _, _ => RetOK.ret rfl
  | _ :: rs, _, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_keccakPackRounds rs _ _).bind fun r hr ↦ RetOK.ret (by simp [hr])

/-- A layer keeps the length of the claim's point. -/
theorem retOK_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    RetOK (fun c : KeccakClaim ↦ c.point.length = claim.point.length)
      (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ ?_
  refine (retOK_keccakPackRounds _ _ _).bind fun r hr ↦ ?_
  obtain ⟨value, scale, point⟩ := r
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨localPoint, value'⟩ := r
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hr

/-- The layers keep the length of the claim's point. -/
theorem retOK_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    RetOK (fun c : KeccakClaim ↦ c.point.length = claim.point.length)
      (keccakLayers logSteps steps claim)
  | [], _ => RetOK.ret rfl
  | _ :: steps, _ => (retOK_verifyKeccakLayer _ _ _).bind fun c hc ↦
      (retOK_keccakLayers logSteps steps c).mono fun _ h ↦ h.trans hc

/-- **The Keccak reduction's point and slices**: the point it leaves for ring switching has
`|inst| + 6` coordinates, and it leaves 64 slices, when `inst` has at least four. -/
theorem retOK_verifyKeccak_point (logSteps : ℕ) (inst output : List E)
    (hi : 4 ≤ inst.length) (hl : inst.length = logSteps) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦
      r.2.1.length = inst.length + 6 ∧ r.2.2.length = 64)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine (retOK_sampleN _).bind fun segment hseg ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  refine (retOK_keccakLayers _ _ _).bind fun claim hclaim ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ ?_
  refine (retOK_sumcheck 3 _ _).bind fun r hr ↦ ?_
  obtain ⟨low, v⟩ := r
  refine (retOK_keccakOpen _ _ _ _ _).bind fun r hr' ↦ ?_
  obtain ⟨slot', weights', value'⟩ := r
  refine (RetOK.readN _).bind fun slices hs ↦ RetOK.bind_true fun _ ↦ RetOK.ret ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_take] at hr hr' ⊢
    rw [hclaim]
    simp only [keccakFirstClaim, List.length_append, List.length_drop, List.length_replicate]
      at hr ⊢
    rw [hseg, hr, hr', show qkeccakSlotBits = 6 by decide,
      show keccakSegmentBits = 1 by decide]
    omega
  · exact hs

/-! ## Equality weights -/

/-- The cube point of `x` on `n + 1` coordinates: bit `0`, then the cube point of `x / 2`. -/
theorem boolPoint_succ (n x : ℕ) :
    boolPoint (n + 1) x = (if x.testBit 0 then 1 else 0) :: boolPoint n (x / 2) := by
  simp only [boolPoint, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp [Nat.testBit_succ]

/-- `eq_eval` at the cube point of `x` is the Keccak reduction's equality weight of `x`. -/
theorem eqAt_eq_eqEval : ∀ (pt : List E) (x : ℕ),
    KeccakGkr.eqAt pt x = eqEval pt (boolPoint pt.length x)
  | [], x => by simp [eqEval]
  | r :: rs, x => by
    rw [KeccakGkr.eqAt_cons, eqAt_eq_eqEval rs (x / 2), List.length_cons, boolPoint_succ,
      eqEval_eq_list_prod, eqEval_eq_list_prod, List.zipWith_cons_cons, List.prod_cons,
      Nat.testBit_zero]
    congr 1
    by_cases h : x % 2 = 1
    · simp only [h, ↓reduceIte, decide_true]
      rw [add_comm 1 r, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp [h]

/-- The table sumcheck's zero test weighs as the Keccak reduction (characteristic two). -/
theorem keccakZero_eqAt : ∀ (pt : List E) (x : ℕ), KeccakZero.eqAt pt x = KeccakGkr.eqAt pt x
  | [], _ => rfl
  | r :: rs, x => by
    rw [KeccakZero.eqAt, KeccakGkr.eqAt_cons, keccakZero_eqAt rs, CharTwo.sub_eq_add]

/-- **A column's extension** is the sum of its cells weighted by the equality weights of the
point. -/
theorem eval₂Mle_eq_sum_eqAt {n : ℕ} (v : Vector K (2 ^ n)) (z : Vector E n) :
    eval₂Mle v (algebraMap K E) z =
      ∑ x ∈ range (2 ^ n), KeccakGkr.eqAt z.toList x * ofK (v.getD x 0) := by
  rw [← sum_eqEval_mul z ⟨v⟩, Finset.sum_range]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqAt_eq_eqEval, Vector.length_toList]

end

end LeanVM.Protocol.EndToEnd.Front
