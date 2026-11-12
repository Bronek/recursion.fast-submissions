-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Defs.lean` (formal rev 40f877dc) as `LvmWhirDefs` for
-- lvm (WP-7). Changed for the unique-decoding regime: `eOod` is cut and `eQuery` becomes `eQueryUd`
-- (`((A − 1)/n)^t + t·L'/|E|`: no out-of-domain claim in the glue); no proof-of-work discount.
/-
  LeanVM.Protocol.Whir.Sound.Defs

  The shapes of the WHIR commitments, the doom at the start of a level, and the escape bounds of
  each group of challenges of a level.
-/


import LvmWhirProg
import LvmWhirInterface

/-!
# Level doom and escape bounds

A level `i` of the opening (`LeanVM.Protocol.Verifier.whirLevelsUd`) opens the `i`-th commitment
of the opening's view (`viewC`), a matrix of `2^(κ_i + R_i)` rows of `wdOf i ℓ_i` words: `2^ℓ₀`
`K`-words at level `0` (the stack's lanes), `3·2^ℓ_i` words (the lanes in `E`) deeper. `ShapeOK`
records that the view has exactly the commitments `0..i` and that the `i`-th has this shape;
`LevelPre` is the doom at the start of a level: `A(i, 0)` and `ShapeOK`.

The escape bounds of a level's groups, each a probability over the group's challenges:

* `eFold P ℓ` (`LeanVM.Protocol.Whir.Sound.Folds`): `(2·L + 2^(ℓ−1)·E_mca) / |E|` per fold;
* `eQueryUd P P' t`: `((A − 1)/n)^t + t·L' / |E|` for the query positions and `λ`, `A` the
  threshold `thr` and `n` the block length of the current level;
* `eQueryFinal P t`: `((A − 1)/n)^t + t / |E|` on the final level;
* `eTail`: `2 / |E|` per tail round.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Finset

section

/-- The width of commitment `i`: `2^ℓ` words at level `0`, `3·2^ℓ` deeper. -/
def wdOf (i ℓ : ℕ) : ℕ := if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ

/-- The history has the commitments `0..i`, the `i`-th of `2^(κ+R)` rows of `wdOf i ℓ` words. -/
def ShapeOK (i : ℕ) (P : LevelCode) (ℓ : ℕ) (cs : List (ℕ × ℕ × Word)) : Prop :=
  cs.length = i + 1 ∧ ∃ W, cs[i]? = some (P.κ + P.R, wdOf i ℓ, W) ∧ WellShaped (wdOf i ℓ) W

/-- **The doom at the start of level `i`**: `A(i, 0)` and the commitments' shape. -/
def LevelPre (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (ℓ pre : ℕ) (s : WhirStateT)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  FoldInv μ ℓ₀ w i P ℓ pre s [] cs ∧ ShapeOK i P ℓ cs

/-- The query group's escape (unique decoding): `((A − 1)/n)^t + t·L' / |E|`. -/
noncomputable def eQueryUd (P P' : LevelCode) (t : ℕ) : ENNReal :=
  (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t + ((t * P'.listMax : ℕ) : ENNReal) / Fintype.card E

/-- The final query group's escape: `((A − 1)/n)^t + t / |E|`. -/
noncomputable def eQueryFinal (P : LevelCode) (t : ℕ) : ENNReal :=
  (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t + (t : ENNReal) / Fintype.card E

/-- A tail round's escape: `2 / |E|`. -/
noncomputable def eTail : ENNReal := (2 : ENNReal) / Fintype.card E

/-! ## Shape lemmas -/

theorem shapeOK_word {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) : cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs i) ∧
      WellShaped (wdOf i ℓ) (wordOf cs i) := by
  obtain ⟨-, W, hW, hws⟩ := h
  rw [wordOf_eq hW]
  exact ⟨hW, hws⟩

theorem shapeOK_append {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) (x : ℕ × ℕ × Word) :
    (cs ++ [x])[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs i) := by
  rw [List.getElem?_append_left (by rw [h.1]; omega)]
  exact (shapeOK_word h).1

/-- The rows of a well-shaped leaf of commitment `i` give `2^ℓ` lanes. -/
theorem length_wordOf {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) (q : ℕ) :
    (wordOf cs i q).length = if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ :=
  (shapeOK_word h).2 q

end
end LeanVM.Protocol.Whir.Sound
