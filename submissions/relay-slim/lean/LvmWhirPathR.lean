-- New for lvm2 (WP JB-L, J2): the WHIR doom relativised to the candidates that are not good (JB-L report §4,
-- "the relativised doom"). No upstream template: leanVM's extractor enumerates the list instead.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the relativised doom, definitions)
-/

import LvmWhirStart

/-!
# The doom relativised to the non-good candidates

At the Johnson radius a root has a list of candidates, some of which may be **good** (they satisfy
the statement's relation). Unique decoding's doom "every candidate violates the claim" fails as soon
as one candidate is good, yet the extractor only needs the transcript to follow a good candidate.
This module defines the doom that tracks only the list members that are *not* on a good path:

* `rootMsg q`, `qMle q pt`: a root column's message (lane bits first, then the message bits, the
  order in which the levels fold them) and its multilinear extension at `pt`.
* `PathAt q fs g`: the message `g` (lane bits `u`, message bits `x`) is `q`'s **path** after the fold
  challenges `fs`: `g u x = q̃(fs ++ u ++ x)`. Folding keeps paths (`pathAt_fold`); a next level's
  member is on a path iff its joined message is (`pathAt_joinMsg_iff`); at the root a member is on
  `q`'s path iff it is `q`'s encoding (`pathAt_rootMsg_iff`).
* `Tracked Gd fs g`: on no path of the good set `Gd`; `ViolR P Gd fs O Φ σ`: **every tracked member
  of the list of `O` violates `(Φ, σ)`** (`Viol` relativised; `Viol` implies it).
* `card_foldStep_bad_le_R`: the fold step keeps `ViolR` except at `2·L + 2^m·M` challenges, the same
  count as `card_foldStep_bad_le`: a tracked member of the folded list is the fold of a tracked
  member (a fold of a path is a path), so no collision event is charged.
* The good set shrinks along the levels to the candidates whose path is in every later oracle's
  list (`ConsAt`, `gdNext`, `gdFinal`): for a member of the next list, being tracked for the old
  or the new set is the same (`tracked_gdNext_iff`), and the extractor gets each level's member.
* `GoodRes`: the residual's encoding is in the list of the final folded word and the residual is
  the path of a candidate of the final good set: **an accepting transcript ends in a fold of a good
  candidate**.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

section

/-! ## Paths -/

/-- The message of a root column `q`: lane bits `u` (the root's `2^6` lanes), then the message bits
`x` of a lane (`blockOf`). -/
noncomputable def rootMsg {μ : ℕ} (q : Column μ) :
    (Fin laneBits → Bool) → (Fin (μ - laneBits) → Bool) → E :=
  fun u x ↦ blockOf q (bitsEquiv laneBits u) x

/-- The multilinear extension of `q`'s message at the point `pt` (lane bits first). -/
noncomputable def qMle {μ : ℕ} (q : Column μ) (pt : List E) : E :=
  claimSum (eqEval pt) (rootMsg q)

/-- **`g` is `q`'s path after the fold challenges `fs`**: `g u x = q̃(fs ++ u ++ x)`. -/
def PathAt {μ m κ : ℕ} (q : Column μ) (fs : List E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    Prop :=
  ∀ u x, g u x = qMle q (fs ++ bitsL u ++ bitsL x)

/-- On no path of the good set. -/
def Tracked {μ m κ : ℕ} (Gd : Set (Column μ)) (fs : List E)
    (g : (Fin m → Bool) → (Fin κ → Bool) → E) : Prop :=
  ∀ q ∈ Gd, ¬ PathAt q fs g

/-- **The relativised doom of a word**: every tracked member of its list violates `(Φ, σ)`. -/
def ViolR (P : LevelCode) {μ m : ℕ} (Gd : Set (Column μ)) (fs : List E)
    (O : (Fin m → Bool) → Fin P.n → E) (Φ : List E → E) (σ : E) : Prop :=
  ∀ V ∈ iList P.code P.thr O, Tracked Gd fs (decode P V) → claimSum Φ (decode P V) ≠ σ

private theorem eqEval_cons' (x z : E) (a b : List E) :
    eqEval (x :: a) (z :: b) = (1 + x + z) * eqEval a b := by
  simp only [eqEval, List.zipWith_cons_cons, foldl_mul_eq, List.prod_cons, one_mul]

private theorem eqEval_nil_right' (a : List E) : eqEval a [] = 1 := by
  cases a <;> simp [eqEval]

/-- The equality kernel is affine in each coordinate of its first point. -/
private theorem eqEval_affine (a b r : List E) (c : E) :
    eqEval (a ++ c :: b) r = (1 - c) * eqEval (a ++ 0 :: b) r + c * eqEval (a ++ 1 :: b) r := by
  induction a generalizing r with
  | nil =>
    cases r with
    | nil => simp only [eqEval_nil_right']; ring
    | cons z r => simp only [List.nil_append, eqEval_cons']; ring
  | cons x a ih =>
    cases r with
    | nil => simp only [eqEval_nil_right']; ring
    | cons z r => simp only [List.cons_append, eqEval_cons', ih r]; ring

/-- The equality kernel of two lists of equal length splits over concatenation. -/
private theorem eqEval_append' : ∀ (a₁ a₂ b₁ b₂ : List E), a₁.length = b₁.length →
    eqEval (a₁ ++ a₂) (b₁ ++ b₂) = eqEval a₁ b₁ * eqEval a₂ b₂
  | [], _, [], _, _ => by simp [eqEval]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | x :: a₁, a₂, z :: b₁, b₂, h => by
    simp only [List.cons_append, eqEval_cons', eqEval_append' a₁ a₂ b₁ b₂ (by simpa using h)]
    ring

/-- At two cube points the equality kernel is the indicator of their equality. -/
private theorem eqEval_bitsL_bitsL {n : ℕ} (p p' : Fin n → Bool) :
    eqEval (bitsL p') (bitsL p) = if p = p' then 1 else 0 := by
  classical
  rw [eqEval_bitsL (bitsL p') (length_bitsL p') p]
  have hb : ∀ b : Fin n, (if p b then (bitsL p').getD b 0 else 1 - (bitsL p').getD b 0) =
      if p b = p' b then 1 else 0 := by
    intro b
    have hg : (bitsL p').getD b 0 = bitE (p' b) := by simp [bitsL, List.getD_eq_getElem?_getD]
    rw [hg]
    cases p b <;> cases p' b <;> simp [bitE]
  rw [Finset.prod_congr rfl fun b _ ↦ hb b, Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, funext_iff]

/-- The extension is affine in each coordinate (characteristic 2: `eq(c, z) = 1 + c + z`). -/
theorem qMle_affine {μ : ℕ} (q : Column μ) (a b : List E) (c : E) :
    qMle q (a ++ c :: b) = (1 - c) * qMle q (a ++ 0 :: b) + c * qMle q (a ++ 1 :: b) := by
  simp only [qMle, claimSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqEval_affine]
  ring

/-- At a Boolean point the extension is the message. -/
theorem qMle_bitsL {μ : ℕ} (q : Column μ) (u : Fin laneBits → Bool)
    (x : Fin (μ - laneBits) → Bool) : qMle q (bitsL u ++ bitsL x) = rootMsg q u x := by
  classical
  have hk : ∀ u' x', eqEval (bitsL u ++ bitsL x) (bitsL u' ++ bitsL x') * rootMsg q u' x' =
      if u' = u then (if x' = x then rootMsg q u x else 0) else 0 := by
    intro u' x'
    rw [eqEval_append' _ _ _ _ (by simp), eqEval_bitsL_bitsL, eqEval_bitsL_bitsL]
    split_ifs <;> simp_all
  simp only [qMle, claimSum, hk]
  simp

/-- **Folding keeps paths.** -/
theorem pathAt_fold {μ m κ : ℕ} {q : Column μ} {fs : List E}
    {g : (Fin (m + 1) → Bool) → (Fin κ → Bool) → E} (h : PathAt q fs g) (c : E) :
    PathAt q (fs ++ [c]) (foldRows c g) := by
  intro u x
  rw [foldRows, h, h, bitsL_cons, bitsL_cons, bitE_false, bitE_true]
  have := qMle_affine q fs (bitsL u ++ bitsL x) c
  simp only [List.append_assoc, List.cons_append] at this ⊢
  exact this.symm

/-- **A next level's member is on a path iff its joined message is.** -/
theorem pathAt_joinMsg_iff {μ n m κ' : ℕ} (hn : n = m + κ') (q : Column μ) (fs : List E)
    (g : (Fin m → Bool) → (Fin κ' → Bool) → E) :
    PathAt q fs (fun (_ : Fin 0 → Bool) ↦ joinMsg hn g) ↔ PathAt q fs g := by
  subst hn
  constructor
  · intro h u x
    have := h Fin.elim0 (Fin.append u x)
    simpa [joinMsg, bitsL_append] using this
  · intro h u p
    simp only [bitsL_zero, List.append_nil, joinMsg, Fin.cast_eq_self]
    rw [h, List.append_assoc, ← bitsL_append]
    congr 3
    funext i
    simpa using congrFun (Fin.append_castAdd_natAdd (f := p)) i

/-- **At the root a message is on `q`'s path iff it is `q`'s message.** -/
theorem pathAt_rootMsg_iff {μ : ℕ} (hμ : laneBits ≤ μ) (q q' : Column μ) :
    PathAt q [] (rootMsg q') ↔ q' = q := by
  constructor
  · intro h
    refine eq_of_blockOf_eq hμ fun u ↦ funext fun x ↦ ?_
    have := h ((bitsEquiv laneBits).symm u) x
    rw [List.nil_append, qMle_bitsL] at this
    simpa [rootMsg] using this
  · rintro rfl u x
    rw [List.nil_append, qMle_bitsL]

/-- `Viol` is `ViolR` for every good set. -/
theorem violR_of_viol (P : LevelCode) {μ m : ℕ} (Gd : Set (Column μ)) (fs : List E)
    {O : (Fin m → Bool) → Fin P.n → E} {Φ : List E → E} {σ : E} (h : Viol P O Φ σ) :
    ViolR P Gd fs O Φ σ :=
  fun V hV _ ↦ h V hV

open Classical in
/-- **The fold step, relativised**: if every tracked member of the list of `rowsOf (m+1) O`
violates `(Φ, σ)` after the challenges `fs`, and the prover's quadratic has `h(0) + h(1) = σ`, at most
`2·listMax + 2^m·mcaMax` challenges `s` leave a tracked member of the list of
`rowsOf m (foldN s O)` (after `fs ++ [s]`) satisfying `(Φ(s, ·), h(s))`. -/
theorem card_foldStep_bad_le_R (P : LevelCode) {μ m : ℕ} (Gd : Set (Column μ)) (fs : List E)
    (Φ : List E → E) (hΦ : IsMultiaffine (m + 1 + P.κ) Φ) (O : ℕ → Fin P.n → E)
    (σ c₀ c₁ c₂ : E) (hσ : polyEval [c₀, c₁, c₂] 0 + polyEval [c₀, c₁, c₂] 1 = σ)
    (hviol : ViolR P Gd fs (rowsOf (m + 1) O) Φ σ) :
    (univ.filter fun s ↦ ¬ ViolR P Gd (fs ++ [s]) (rowsOf m (foldN s O)) (fun r ↦ Φ (s :: r))
        (polyEval [c₀, c₁, c₂] s)).card ≤
      2 * P.listMax + 2 ^ m * P.mcaMax := by
  classical
  set Q := rowsOf (m + 1) O
  set L := (iList P.code P.thr Q).filter fun V ↦ Tracked Gd fs (decode P V)
  let B₁ : Finset E := univ.filter fun s ↦
    ∃ V ∈ L, polyEval [c₀, c₁, c₂] s = claimSum (fun r ↦ Φ (s :: r)) (foldRows s (decode P V))
  have hB₁ : B₁.card ≤ 2 * P.listMax := by
    refine (card_filter_exists_le L _ (N := 2) fun V hV ↦
      card_sumcheck_bad_le Φ hΦ (decode P V) σ c₀ c₁ c₂ hσ
        (hviol V (Finset.mem_filter.mp hV).1 (Finset.mem_filter.mp hV).2)).trans ?_
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ ((Finset.card_filter_le _ _).trans (P.card_iList_le Q))
  have hB₂ : (foldBad P.code P.thr (consRows Q)).card ≤ 2 ^ m * P.mcaMax := by
    have := P.card_foldBad_le (consRows Q)
    simpa using this
  refine (Finset.card_le_card fun s hs ↦ ?_).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add hB₁ hB₂))
  rw [Finset.mem_union]
  by_contra hgood
  push Not at hgood
  obtain ⟨hs₁, hs₂⟩ := hgood
  refine (Finset.mem_filter.mp hs).2 fun V' hV' htr ↦ ?_
  rw [rowsOf_foldN] at hV'
  have hlist := not_not.mp ((not_congr (mem_foldBad _ _ _ s)).mp hs₂)
  rw [hlist] at hV'
  obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hV'
  rw [← consRows_unconsRows W', consRows_mem_iList] at hW'
  rw [← consRows_unconsRows W', decode_fold P ((mem_iList _ _ _ _).mp hW').1] at htr ⊢
  intro heq
  exact hs₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, _,
    Finset.mem_filter.mpr ⟨hW', fun q hq hp ↦ htr q hq (pathAt_fold hp s)⟩, heq.symm⟩)

/-! ## The good set along the levels -/

/-- **Consistency of `q` at level `j`** (code `P`, `ℓ` lane bits): `q`'s path after `fs` is a member
of the list of the level's oracle (`rowsOf ℓ (laneO j cs P.n)`). -/
def ConsAt (P : LevelCode) (ℓ j : ℕ) (cs : List (ℕ × ℕ × Word)) (fs : List E) {μ : ℕ}
    (q : Column μ) : Prop :=
  ∃ V ∈ iList P.code P.thr (rowsOf ℓ (laneO j cs P.n)), PathAt q fs (decode P V)

/-- The good set of the next level: the candidates consistent at it. -/
def gdNext (P : LevelCode) (ℓ j : ℕ) (cs : List (ℕ × ℕ × Word)) (fs : List E) {μ : ℕ}
    (Gd : Set (Column μ)) : Set (Column μ) :=
  {q | q ∈ Gd ∧ ConsAt P ℓ j cs fs q}

/-- **For a member of the next level's list, tracked for the old or the new set is the same**:
a member on `q`'s path witnesses `q`'s consistency. -/
theorem tracked_gdNext_iff (P : LevelCode) (ℓ j : ℕ) (cs : List (ℕ × ℕ × Word)) (fs : List E)
    {μ : ℕ} (Gd : Set (Column μ)) {V : (Fin ℓ → Bool) → Fin P.n → E}
    (hV : V ∈ iList P.code P.thr (rowsOf ℓ (laneO j cs P.n))) :
    Tracked (gdNext P ℓ j cs fs Gd) fs (decode P V) ↔ Tracked Gd fs (decode P V) := by
  constructor
  · intro h q hq hp
    exact h q ⟨hq, V, hV, hp⟩ hp
  · intro h q hq
    exact h q hq.1

/-- The good set of the final level, from the good set `Gd` of level `i` (fold challenges counted
by `pre` before it) and the levels from `i`, all fold challenges `fs`. -/
def gdFinal (codes : ℕ → LevelCode) (cs : List (ℕ × ℕ × Word)) (fs : List E) {μ : ℕ} :
    ℕ → ℕ → List Whir.Level → Set (Column μ) → Set (Column μ)
  | _, _, [], Gd => Gd
  | _, _, [_], Gd => Gd
  | i, pre, level :: next :: rest, Gd =>
    gdFinal codes cs fs (i + 1) (pre + level.fold) (next :: rest)
      (gdNext (codes (i + 1)) next.fold (i + 1) cs (fs.take (pre + level.fold)) Gd)

/-- The final level's index, fold challenges before it, and fold count, from level `i`. -/
def finInfo : ℕ → ℕ → List Whir.Level → ℕ × ℕ × ℕ
  | i, pre, [] => (i, pre, 0)
  | i, pre, [level] => (i, pre, level.fold)
  | i, pre, level :: next :: rest => finInfo (i + 1) (pre + level.fold) (next :: rest)

/-- The good root set: the good candidates of the root's word. -/
def gdRoot {μ : ℕ} (P₀ : LevelCode) (Good : Column μ → Prop) (cs : List (ℕ × ℕ × Word)) :
    Set (Column μ) :=
  {q | q ∈ Candidates μ P₀.R P₀.thr (wordOf cs 0) ∧ Good q}

/-! ## The end -/

/-- **The residual is good**: its encoding is in the list of the final folded word (`foldedW`),
and it is the path of a candidate of the good set after all the fold challenges. -/
def GoodRes (P : LevelCode) (i : ℕ) {μ : ℕ} (Gd : Set (Column μ)) (r : WhirStateT × List E)
    (res : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (fun _ : Fin 0 → Bool ↦ enc P.κ P.R (resMsg res)) ∈
      iList P.code P.thr (fun _ : Fin 0 → Bool ↦ foldedW i P r cs) ∧
    ∃ q ∈ Gd, ∀ x : Fin P.κ → Bool, resMsg res x = qMle q (r.1.folds ++ bitsL x)

/-- **The post of the levels from `i`** (the run up to the residual, returning the final level's
fold state `a.1` and the residual `a.2`): the residual is good for the final good set, or the
residual's doom `ResC` holds (from there the final level's queries reject but for `eQueryFinal`). -/
def PostR (μ ℓ₀ : ℕ) (w : List E → E) (codes : ℕ → LevelCode) (c₀ n₀ : ℕ) (i pre : ℕ)
    (levels : List Whir.Level) (Gd : Set (Column μ))
    (a : (WhirStateT × List E) × List E) (h : List Ev) : Prop :=
  let cs := viewC c₀ n₀ (commits h)
  let f := finInfo i pre levels
  GoodRes (codes f.1) f.1 (gdFinal codes cs a.1.1.folds i pre levels Gd) a.1 a.2 cs ∨
    ResC μ ℓ₀ w f.1 (codes f.1) f.2.2 f.2.1 a.1 a.2 cs

end
end LeanVM.Protocol.Whir.Sound
