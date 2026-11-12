-- From relay-echo (#12), `lean/FastSpecLoop.lean` (Apache-2.0), unchanged except the module names of
-- its imports.
/-
  The statements behind **L3** (`chainEndH4_toH4`, `FastSpec.lean`) for the chain loop of
  `FastDefs.lean`: `chainEndH4` runs its steps and their rounds as one loop, `chainLoop`, and
  L3's induction needs it one step at a time, as `stepH4` (`chainEndH4_succ`).

  * `chainLoop_eq`: the loop is the fold of `roundC` over the rounds left in the current step,
    then the step's last round, then `chainEndH4` for the remaining `n` steps from the four
    output lanes.
  * `chainEndH4_succ`: `chainEndH4 h (n + 1)` is `chainEndH4 (stepH4 h) n`.
-/
import WlFastDefs
import WlFastSpecPerm

namespace RecursionFast.FastCheck
open RecursionFast Keccak

/-- **The chain loop**: the rounds `cs` folded, the last round, then the remaining `n` steps from
the four output lanes. -/
theorem chainLoop_eq (n : ℕ) (cs : List UInt64) (s : S25) :
    chainLoop n cs s.a0 s.a1 s.a2 s.a3 s.a4 s.a5 s.a6 s.a7 s.a8 s.a9 s.a10 s.a11 s.a12 s.a13 s.a14
      s.a15 s.a16 s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24 =
      chainEndH4 ⟨(complL (roundC (cs.foldl roundC s) 0x8000000080008008)).a0,
        (complL (roundC (cs.foldl roundC s) 0x8000000080008008)).a1,
        (complL (roundC (cs.foldl roundC s) 0x8000000080008008)).a2,
        (complL (roundC (cs.foldl roundC s) 0x8000000080008008)).a3⟩ n := by
  have S25_eta (t : S25) :
      (⟨t.a0, t.a1, t.a2, t.a3, t.a4, t.a5, t.a6, t.a7, t.a8, t.a9, t.a10, t.a11, t.a12,
        t.a13, t.a14, t.a15, t.a16, t.a17, t.a18, t.a19, t.a20, t.a21, t.a22, t.a23,
        t.a24⟩ : S25) = t := rfl
  cases s
  dsimp only
  fun_induction chainLoop
  case case1 => rfl
  case case2 => rfl
  all_goals
    rename_i ih
    rw [ih]
    simp +zetaDelta only [List.foldl_cons, S25_eta]

/-- **The chain in lanes, one step at a time**: `chainEndH4` takes `stepH4` first. -/
theorem chainEndH4_succ (h : H4) (n : ℕ) : chainEndH4 h (n + 1) = chainEndH4 (stepH4 h) n := by
  simp only [chainEndH4.eq_2]
  rw [chainLoop_eq]
  simp only [stepH4, permF, roundsC_foldl]

end RecursionFast.FastCheck
