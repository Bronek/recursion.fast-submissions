import LvmQWhirWeight
import LvmQSelf

/-!
# QA2: non-vacuity of the gadget specs (one toy program)

A small program made of QA2 gadgets (a level-0 row fold, a column weight, the self-evaluation),
built by `toProgram`, passes WP-10's program check (`qa2toy_wf`, kernel `decide`) and has no
computed-address read, and its glue fits the self-evaluation (`qa2toy_fits`). So the interpreter's memory satisfies every segment (`qa2toy_holds`, from
WP-10's `interp_holds` and QL's `toProgram_holds`) on every input: the `SegsHold` hypotheses of
`rowFold0_spec`, `colWeight_spec`, `selfEval_spec` are satisfiable, and `qa2toy_fold` instantiates
the row-fold spec on the interpreter's run.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-- The toy: 8 input lanes, 6 input `E` cells (cell 0 zero, cell 1 one, 2–3 `e[k]`, 4–5 point). -/
def qa2toy : BM Nat := do
  let _ ← rowFold0 1 1 0 2 2
  let _ ← colWeight 1 2 [1] 4 0 0 2 0 0 0
  selfEval 4 1 (fun i => ec (4 + i)) (ec 1) (ec 0)

/-- The toy program. -/
def qa2toyP : Program := toProgram 8 6 qa2toy

theorem qa2toy_wf : qa2toyP.wf = true := by decide +kernel

theorem qa2toy_noReadd : qa2toyP.noReadd = true := by decide +kernel

/-- **The fixed point closes on the toy**: its glue (the straight-line rows of every gadget,
including the self-evaluation's own) has at most `2^4` columns, each of a piece of at most `2^1`
rows, so `selfEval 4 1` evaluates all of it. -/
theorem qa2toy_fits : glueFits qa2toyP 4 1 = true := by decide +kernel

/-- **Non-vacuity**: on every input, the interpreter's memory satisfies every segment of the toy. -/
theorem qa2toy_holds (inK : Array FK) (inE : Array FE) (hK : inK.size = 8) (hE : inE.size = 6) :
    SegsHold (ctxOf qa2toyP) (qa2toyP.interpMem inK inE) ⟨8, 6⟩ (qa2toy ⟨8, 6⟩).2 :=
  (toProgram_holds 8 6 qa2toy _).mp
    (qa2toyP.interp_holds qa2toy_wf inK inE ⟨hK, hE⟩ (inb_of_noReadd _ qa2toy_noReadd _ _)).1

/-- The row-fold spec instantiated on the interpreter's run of the toy. -/
theorem qa2toy_fold (inK : Array FK) (inE : Array FE) (hK : inK.size = 8) (hE : inE.size = 6)
    {q : Nat} (hq : q < 2) :
    ((rowFold0 1 1 0 2 2 ⟨8, 6⟩).1 q).val (qa2toyP.interpMem inK inE) =
      ∑ k ∈ Finset.range 2, FE.ofK ((qa2toyP.interpMem inK inE).k (0 + k + 2 * q)) *
        (qa2toyP.interpMem inK inE).e (2 + k) := by
  have h := qa2toy_holds inK inE hK hE
  simp only [qa2toy, bind_apply] at h
  rw [segsHold_append] at h
  exact rowFold0_spec h.1 (by decide) (by simpa using hq)

end Lvm.Loop.Build
