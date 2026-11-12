-- Adapted from the leanvm-inspired entry (#11): `upd`, `Lo` and `hframe` from `LvmXSort.lean`,
-- `NoLoopT` from `LvmXLog.lean`, unchanged; `boundsOk_of_noLoopT` is new.
import WlXComputes

/-!
# Helpers for the extractor's straight-line code

* `upd`: a register file with one cell changed;
* `Lo`, `hframe`: store-free, loop-free code whose destinations are registers leaves every heap cell
  alone;
* `NoLoopT`: a program with no `loopT`; its loop bounds hold from every state
  (`safe_of_noLoopT`).
-/

namespace WsLeaf.X

open RecursionFast

/-- `f` with `v` at `k`. -/
def upd (f : ℕ → Word) (k : ℕ) (v : Word) : ℕ → Word := fun a => if a = k then v else f a

/-- No store, no loop, every destination a register. -/
def Lo : XIR → Prop
  | .blk ps => ∀ p ∈ ps, p.dst < regs
  | .load d _ => d < regs
  | .input d _ => d < regs
  | .out _ => True
  | .seq p q => Lo p ∧ Lo q
  | .ite _ p q => Lo p ∧ Lo q
  | _ => False

/-- **Heap frame**: such code leaves every cell `≥ regs` alone. -/
theorem hframe (I : Array Word) : ∀ (P : XIR) (s : St), Lo P → ∀ x, regs ≤ x →
    rd (semXIR I P s).M x = rd s.M x
  | .blk _, _, h, _, hx => rd_runPrims_of_not_writes (fun p hp he => by have := h p hp; omega) _
  | .load _ _, _, h, _, hx => rd_set_ne (by simp only [Lo] at h; omega)
  | .input _ _, _, h, _, hx => rd_set_ne (by simp only [Lo] at h; omega)
  | .out _, _, _, _, _ => rfl
  | .seq p q, s, h, x, hx => (hframe I q _ h.2 x hx).trans (hframe I p s h.1 x hx)
  | .ite _ p q, s, h, x, hx => by
    simp only [semXIR]; split
    · exact hframe I q s h.2 x hx
    · exact hframe I p s h.1 x hx
  | .store .., _, h, _, _ => h.elim
  | .loopK .., _, h, _, _ => h.elim
  | .loopT .., _, h, _, _ => h.elim

/-- A program with no `loopT`. -/
def NoLoopT : XIR → Prop
  | .seq p q | .ite _ p q => NoLoopT p ∧ NoLoopT q
  | .loopK _ _ _ b => NoLoopT b
  | .loopT .. => False
  | _ => True

/-- A program with no `loopT` has its loop bounds from every state. -/
theorem safe_of_noLoopT {I : Array Word} {t : ℕ} : ∀ {P : XIR}, NoLoopT P → Safe I t P
  | .blk _, _ => .blk _
  | .load .., _ => .load _ _
  | .store .., _ => .store _ _
  | .input .., _ => .input _ _
  | .out _, _ => .out _
  | .seq _ _, h => .seq (safe_of_noLoopT h.1) (safe_of_noLoopT h.2)
  | .ite _ _ _, h => .ite (safe_of_noLoopT h.1) (safe_of_noLoopT h.2)
  | .loopK .., h => .loopK (safe_of_noLoopT h)

end WsLeaf.X
