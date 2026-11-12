-- new for lvm (INT-2): WP-9b's `PubOk` for V's header evaluator of the public arrays (`pubArr`).
import LvmLoopMleFast
import LvmM3FidFix

/-!
# `PubOk` for the public arrays

WP-9b's `fixOk_lvmTabs` takes `PubOk arrs`: every public array's evaluator `e` is its value
column's extension. For the arrays built by `pubArr` (V evaluates `pubEval vals` from π's header
lanes `vals`) this is `pubEval_eq`; committed arrays (`pub = none`) are vacuous.

* **`pubOk_of`**: `PubOk arrs` when every array is committed or a `pubArr`.
-/

namespace Lvm.M3

/-- **`PubOk`** for arrays that are committed or built by `pubArr`. -/
theorem pubOk_of (arrs : List InArr)
    (h : ∀ a ∈ arrs, a.pub = none ∨ ∃ τ base stride val fin vals, a = pubArr τ base stride val fin vals) :
    PubOk arrs := by
  intro a ha f e he r _
  rcases h a ha with hn | ⟨τ, base, stride, val, fin, vals, rfl⟩
  · rw [hn] at he; cases he
  · simp only [pubArr, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact pubEval_eq vals r

/-- Non-vacuity: a one-lane public array's evaluator at the empty point is its lane. -/
example (v : FK) : pubEval [v] [] = FE.ofK v := rfl

end Lvm.M3
