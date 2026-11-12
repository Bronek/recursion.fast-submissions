-- New for lvm (WP-11b-QL). Byte-list helpers follow FR's `FRNodeReadCore` (`toList_extract`,
-- `traceBytes_cons'`; rf-k/submissions/flock-recursive/lean@8bff272b); the plan lemmas are new.
import LvmReassemble
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Replay, part 1: bytes, the body, the plan walk

Proof-help lemmas for `LvmReplay`: byte arrays as lists (`bl`), the body as consecutive
contributions (`bodyFrom_cons`), and the walk's bookkeeping (`planItems_i`, `ok` monotone, the
plan as the walk's entries at their indices: `Al`).
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

/-! ## Byte arrays as lists -/

theorem ba_ext {a b : ByteArray} (h : bl a = bl b) : a = b :=
  ByteArray.ext (Array.ext' h)

theorem bl_append (a b : ByteArray) : bl (a ++ b) = bl a ++ bl b := by
  simp [bl, ByteArray.data_append]

theorem bl_extract (b : ByteArray) (i j : Nat) : bl (b.extract i j) = ((bl b).drop i).take (j - i) := by
  rw [bl, ByteArray.data_extract, Array.toList_extract, List.extract]; rfl

theorem bl_digestBytes (d : Digest) : bl (digestBytes d) = d.toList := by
  simp [bl, digestBytes, Vector.toList]

theorem size_bl (b : ByteArray) : b.size = (bl b).length := by
  rw [bl, Array.length_toList]; rfl

theorem get!_bl (b : ByteArray) (i : Nat) : b.get! i = (bl b).getD i 0 := by
  rw [ByteArray.get!, getElem!_def, List.getD_eq_getElem?_getD, bl, Array.getElem?_toList]
  rfl

theorem bl_mk (l : List UInt8) : bl ⟨l.toArray⟩ = l := rfl

theorem digest_ext {d e : Digest} (h : d.toList = e.toList) : d = e :=
  Vector.toList_inj.mp h

/-! ## The body -/

theorem bodyFrom_cons (tr : Trace) (P : List PE) {i : Nat} (hi : i < P.length) :
    bodyFrom tr P i = contrib tr i (P.getD i default) ++ bodyFrom tr P (i + 1) := by
  unfold bodyFrom
  rw [show P.length - i = (P.length - (i + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]

theorem bodyFrom_end (tr : Trace) (P : List PE) {i : Nat} (hi : P.length ≤ i) : bodyFrom tr P i = [] := by
  simp [bodyFrom, show P.length - i = 0 by omega]

/-! ## The walk -/

theorem planItem_i (p : Params) (w : WS) (it : Item) :
    (planItem p w it).2.i = w.i + (planItem p w it).1.length := by
  cases it with
  | read m => simp [planItem]
  | cap c r => simp [planItem]
  | sample => simp [planItem, WS.settle]
  | positions r => simp [planItem, WS.settle]
  | opening r =>
    simp only [planItem]
    split
    · simp
    · simp [openPlan, List.length_flatMap]; left; ring

theorem planItems_i (p : Params) : ∀ (w : WS) (its : List Item),
    (planItems p w its).2.i = w.i + (planItems p w its).1.length
  | w, [] => by simp [planItems]
  | w, it :: its => by
    simp only [planItems, List.length_append]
    rw [planItems_i p _ its, planItem_i]; omega

theorem planItem_ok (p : Params) (w : WS) (it : Item) (h : (planItem p w it).2.ok = true) : w.ok = true := by
  cases it with
  | read m => simpa [planItem] using h
  | cap c r => simpa [planItem] using h
  | sample => simpa [planItem, WS.settle] using h
  | positions r => simp only [planItem, WS.settle, Bool.and_eq_true] at h; exact h.1
  | opening r =>
    simp only [planItem] at h
    split at h
    · simp at h
    · simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.1

theorem planItems_ok (p : Params) : ∀ (w : WS) (its : List Item),
    (planItems p w its).2.ok = true → w.ok = true
  | w, [] => by simp [planItems]
  | w, it :: its => fun h => planItem_ok p w it (planItems_ok p _ its h)

/-- The entries `es` sit at indices `i, i + 1, …` of the plan `P`. -/
def Al (P : List PE) (i : Nat) (es : List PE) : Prop :=
  i + es.length ≤ P.length ∧ ∀ x < es.length, P.getD (i + x) default = es.getD x default

theorem Al_append {P : List PE} {i : Nat} {es₁ es₂ : List PE} :
    Al P i (es₁ ++ es₂) ↔ Al P i es₁ ∧ Al P (i + es₁.length) es₂ := by
  simp only [Al, List.length_append]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨⟨by omega, fun x hx => ?_⟩, ⟨by omega, fun x hx => ?_⟩⟩
    · rw [h x (by omega), List.getD_append _ _ _ _ hx]
    · rw [Nat.add_assoc, h _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp
  · rintro ⟨⟨hl1, h1⟩, ⟨hl2, h2⟩⟩
    refine ⟨by omega, fun x hx => ?_⟩
    by_cases hx1 : x < es₁.length
    · rw [h1 x hx1, List.getD_append _ _ _ _ hx1]
    · have := h2 (x - es₁.length) (by omega)
      rw [show i + es₁.length + (x - es₁.length) = i + x by omega] at this
      rw [this, List.getD_append_right _ _ _ _ (by omega)]

theorem Al_planItems (p : Params) {P : List PE} {w : WS} {it : Item} {its : List Item}
    (h : Al P w.i (planItems p w (it :: its)).1) :
    Al P w.i (planItem p w it).1 ∧ Al P (planItem p w it).2.i (planItems p (planItem p w it).2 its).1 := by
  simp only [planItems] at h
  rw [Al_append] at h
  rw [planItem_i]; exact h

theorem Al_head {P : List PE} {i : Nat} {e : PE} {es : List PE} (h : Al P i (e :: es)) :
    i < P.length ∧ P.getD i default = e := by
  refine ⟨by have := h.1; simp at this; omega, by simpa using h.2 0 (by simp)⟩

theorem Al_tail {P : List PE} {i : Nat} {e : PE} {es : List PE} (h : Al P i (e :: es)) :
    Al P (i + 1) es := by
  have := (Al_append (es₁ := [e]) (es₂ := es)).mp h
  simpa using this.2

end Lvm.Replay
