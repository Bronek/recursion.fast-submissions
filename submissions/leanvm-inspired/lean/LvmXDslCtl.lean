-- Ported verbatim from `flock-recursive` `FRXDslCtl.lean` (rf-k kk/base 8bff272b) for lvm (WP-3): the
-- controls of `LvmXDsl`, kept off `Solution`'s import closure.
import LvmXDsl

namespace Lvm.X

open RecursionFast RecursionFast.XStmt
variable {I : Array Word}

/-! ## Controls (kernel-checked)

A toy program on the tape `[3, 5, 7, 9]` (a count, then the words): for each word, read it,
store it to the heap and load it back, `xor` it into an accumulator and output it; then output
the accumulator. Memory `260` words, no memory per tape word.

* Positive: the contract's interpreter outputs `[5, 7, 9, 11]` within `260 + 80` fuel
  (`toy_run`), as `semXIR` says (`toy_sem`), and `80 = steps + 8` is exact (`toy_run_short`);
  `run_toProg`'s hypotheses hold on it (`toy_wf`, `toy_bounds`, `toy_run_thm`); `cost` is
  above the exact count (`toy_steps_le`); `size_compile` (`toy_size`).
* Negative (**an under-declared cost**): the same loop declared with the constant cap `1`
  (`toyBad`) has `cost toyBad 4 = 34`, but the program does not halt within `260 + 34 + 8`
  (`toyBad_short`): the bounds hypothesis of `run_toProg` fails (`toyBad_not_bounds`) and
  cannot be dropped.
* The clamp of `loopK`: with `K = 2` the loop runs twice on the same tape (`toyK_run`), and the
  cost bound holds with no hypothesis (`toyK_steps`).
* The store guard: a store to register `1` (`cBase`) is dropped (`toyG_run`).
-/

namespace Controls

/-- The loop body: next tape word, stored and loaded back, accumulated, output. -/
def body : XIR := .seq (.blk [.op .add 64 64 65]) (.seq (.input 70 64) (.seq (.store 67 70)
  (.seq (.load 71 67) (.seq (.blk [.op .xor 66 66 71, .op .add 67 67 65]) (.out 71)))))

/-- The toy around a loop. -/
def toyWith (L : XIR → XIR) : XIR :=
  .seq (.blk [.const 64 0, .const 65 1, .const 66 0, .const 67 256])
    (.seq (.input 68 64) (.seq (L body) (.out 66)))

/-- The toy, its loop capped by `t`. -/
def toy : XIR := toyWith (.loopT 69 68 ⟨0, 1, 1⟩)
/-- The toy, its loop declared with the cap `1`. -/
def toyBad : XIR := toyWith (.loopT 69 68 ⟨1, 0, 1⟩)
/-- The toy, its loop clamped to `2` iterations. -/
def toyK : XIR := toyWith (.loopK 69 68 2)

/-- The tape. -/
def tape : List Word := [3, 5, 7, 9]

theorem toy_run : (toProg 260 0 toy).run tape 340 = some [5, 7, 9, 11] := by decide +kernel

theorem toy_sem : (semXIR tape.toArray toy (initSt 260)).o.toList = [5, 7, 9, 11] := by
  decide +kernel

theorem toy_run_short : (toProg 260 0 toy).run tape 339 = none := by decide +kernel

theorem toy_steps_le : steps tape.toArray toy (initSt 260) = 72 ∧ cost toy 4 = 91 := by
  decide +kernel

theorem toy_wf : WF toy := by simp [toy, toyWith, body, WF, Writes, Prim.dst, regs, cTmp]

theorem toy_bounds : BoundsOk tape.toArray tape.length toy (initSt (260 + 0 * tape.length)) := by
  simp only [toy, toyWith, BoundsOk, body, and_true, true_and]
  exact ⟨by decide +kernel, fun _ _ => trivial⟩

theorem toy_run_thm : (toProg 260 0 toy).run tape (260 + 0 * 4 + cost toy 4 + 8) =
    some (semXIR tape.toArray toy (initSt (260 + 0 * tape.length))).o.toList :=
  run_toProg (by decide) toy_wf toy_bounds (le_refl _)

theorem toy_size : (compile (.seq (.blk initPs) toy)).size = 42 := by
  rw [size_compile]; rfl

theorem toyBad_short : cost toyBad 4 = 34 ∧ (toProg 260 0 toyBad).run tape (260 + 34 + 8) = none
    := by
  decide +kernel

theorem toyBad_not_bounds :
    ¬ BoundsOk tape.toArray tape.length toyBad (initSt (260 + 0 * tape.length)) := by
  simp only [toyBad, toyWith, BoundsOk]
  intro h
  exact absurd h.2.2.1.1 (by decide +kernel)

theorem toyK_run : (toProg 260 0 toyK).run tape 326 = some [5, 7, 2] := by decide +kernel

theorem toyK_steps : steps tape.toArray toyK (initSt 260) = 58 ∧ cost toyK 4 = 58 := by
  decide +kernel

/-- Stores to register `1` and to heap cell `257`, then outputs cell `1` and the heap cell. -/
def toyG : XIR := .seq (.blk [.const 64 1, .const 65 7, .const 66 257]) (.seq (.store 64 65)
  (.seq (.store 66 65) (.seq (.out 1) (.seq (.load 67 66) (.out 67)))))

theorem toyG_run : (toProg 260 0 toyG).run tape 360 = some [256, 7] := by decide +kernel

end Controls

end Lvm.X
