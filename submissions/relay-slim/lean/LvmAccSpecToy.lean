-- new for lvm (AC-S): a toy instance of phase 3b (A1 §4: 2 columns, D = 3), the non-vacuity check
-- of `accSpecG`/`accBadSpec`/`AccHyp`. Uses WP-10's `mle_pow`/`mle_const`.
import LvmAccSpecPhi

/-!
# A toy instance: two fixed columns of height 4, `D = 3`

`toyCols`: column 0 is the power column `x ↦ g^x` (closed form `powEval`, an input array's address
column), column 1 the constant column `1`; `τs = 2`, `dk = 1`, `D = τs + dk = 3`.

* `toy_ev`: the closed forms are the cells' extensions (`FixOk`'s content); `toy_mle`: `Φ̃` is
  `eval₂Mle` of `Φ`'s 8 cells;
* **`toy_hyp`**: `AccHyp 1 3` holds for every `acc_in.pt`, table point and claim values (the
  hypotheses of `accSpecG` are satisfiable); **`toySpec`**: `accSpecG` on it;
* **`toy_good`**, **`toy_complete`**: with the true claims and a true incoming claim, `AccGood`
  holds and the honest line polynomial passes every check for every `t` (the phase can return);
* **`toy_bad`**: a wrong claim on column 1 (or a false `acc_in.y`) leaves `AccGood`, so
  `accBadSpec` applies (the phase then returns in doom with probability at most
  `1/|E| + 3/|E|`).
-/

namespace Lvm.Acc.Toy

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (FixCol)
open Lvm.Loop (mle)
open scoped ENNReal

/-- The two columns: powers of `g` and the constant `1`, both of height `2^2`. -/
def toyCols : List FixCol := [⟨0, 2, 0, fun r ↦ Lvm.Loop.powEval r FK.x⟩, ⟨0, 2, 1, fun _ ↦ 1⟩]

/-- Their cells. -/
def toyCell (c : FixCol) (x : ℕ) : FK := if c.col = 0 then FK.x ^ x else 1

theorem toy_τ : ∀ c ∈ toyCols, c.τ ≤ 2 := by simp [toyCols]

/-- The closed forms are the cells' extensions. -/
theorem toy_ev : ∀ c ∈ toyCols, ∀ r : List FE, r.length = c.τ →
    c.ev r = mle r fun x ↦ FE.ofK (toyCell c x) := by
  intro c hc r _
  simp only [toyCols, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp only [toyCell, if_true]
    exact (Lvm.Loop.mle_pow r FK.x).symm
  · simp only [toyCell, show (1 : ℕ) ≠ 0 from one_ne_zero, if_false]
    rw [Lvm.Loop.mle_const, Lvm.Loop.ofK_one']

theorem toy_n : toyCols.length ≤ 2 ^ 1 := by simp [toyCols]

/-- **`Φ̃` of the toy is the multilinear extension of its 8 cells.** -/
theorem toy_mle (pt : List E) (hpt : pt.length = 3) :
    phiE toyCols 2 pt = eval₂Mle (phiCol toyCols toyCell 2 1).values (algebraMap K E) (vecOf 3 pt) :=
  phiE_eq_eval₂Mle toyCols toyCell 2 1 toy_τ toy_ev toy_n pt hpt

/-- **`AccHyp` holds** for the toy, at every incoming point, table point and claim values. -/
theorem toy_hyp (a r vs : List E) (ha : a.length = 3) (hr : r.length = 2) (hvs : vs.length = 2) :
    AccHyp 1 3 a (fun κ ↦ Verifier.dot (Verifier.eqKernel κ) vs) (fun κ ↦ r ++ κ) (phiE toyCols 2)
      (deltaOf toyCols vs r) :=
  accHyp_phi toyCols toyCell 2 1 toy_τ toy_ev toy_n a r vs ha hr hvs

/-- **`accSpecG` on the toy** (for any follower predicate `M` the phase keeps). -/
noncomputable def toySpec (a r vs : List E) (ha : a.length = 3) (hr : r.length = 2)
    (hvs : vs.length = 2) (ok : Bool) (yIn : E) (M : List Ev → Prop)
    (hM : ∀ h₀ l, (accProg 1 3 ok yIn a (fun κ ↦ Verifier.dot (Verifier.eqKernel κ) vs)
      (fun κ ↦ r ++ κ) (phiE toyCols 2)).Reach h₀ l → M h₀ → M (h₀ ++ l))
    {εmax T : ℝ≥0∞} (hD : errE 3 ≤ εmax) (hT : T ≤ εmax) :
    Spec (accProg 1 3 ok yIn a (fun κ ↦ Verifier.dot (Verifier.eqKernel κ) vs) (fun κ ↦ r ++ κ)
        (phiE toyCols 2))
      (fun h ↦ ¬ AccGood 1 ok yIn a (phiE toyCols 2) (deltaOf toyCols vs r) ∨ M h)
      (fun _ h ↦ M h) εmax (max ((1 : ℕ) * errE 1) T) T :=
  accSpecG (toy_hyp a r vs ha hr hvs) M hM hD hT

/-- The true claim values at the table point `r`. -/
def trueVs (r : List E) : List E :=
  toyCols.map fun c ↦ FE.toExt3 (c.ev ((r.map FE.ofExt3).take c.τ))

theorem length_trueVs (r : List E) : (trueVs r).length = 2 := by simp [trueVs, toyCols]

/-- **The honest case**: true claims and a true incoming claim give `AccGood`. -/
theorem toy_good (a r : List E) :
    AccGood 1 true (phiE toyCols 2 a) a (phiE toyCols 2) (deltaOf toyCols (trueVs r) r) := by
  refine ⟨rfl, rfl, fun w hw ↦ ?_⟩
  unfold deltaOf
  split_ifs with h
  · rw [trueVs, List.getD_eq_getElem _ _ (by simpa [toyCols] using h), List.getElem_map, sub_self]
  · rfl

/-- **The phase can return**: the honest line polynomial passes every check, for every `κ`, `t`. -/
theorem toy_complete (a r κ : List E) (ha : a.length = 3) (hr : r.length = 2) (hκ : κ.length = 1) :
    ∃ hs : List E, hs.length = 4 ∧ ∀ t : E,
      true = true ∧ hEval hs 0 = phiE toyCols 2 a ∧
        hEval hs 1 = Verifier.dot (Verifier.eqKernel κ) (trueVs r) ∧ (0 : E) = 0 ∧
        phiE toyCols 2 (line a (r ++ κ) t) = hEval hs t :=
  accProg_complete (toy_hyp a r (trueVs r) ha hr (length_trueVs r)) (toy_good a r) κ hκ

/-- **A wrong claim** (column 1's value off by one) is outside `AccGood`: `accBadSpec` applies. -/
theorem toy_bad (a r : List E) (ok : Bool) (yIn : E) :
    ¬ AccGood 1 ok yIn a (phiE toyCols 2)
      (deltaOf toyCols [(trueVs r).getD 0 0, (trueVs r).getD 1 0 + 1] r) := by
  rintro ⟨-, -, h⟩
  have h1 := h 1 (by norm_num)
  simp only [deltaOf, toyCols, List.length_cons, List.length_nil, show 1 < 0 + 1 + 1 by norm_num,
    dif_pos, List.getD_cons_succ, List.getD_cons_zero, trueVs, List.map_cons, List.map_nil,
    List.getElem_cons_succ, List.getElem_cons_zero] at h1
  rw [add_sub_cancel_left] at h1
  exact one_ne_zero h1

/-- **A false incoming claim** is outside `AccGood` whatever the claims. -/
theorem toy_bad_acc (a r vs : List E) (ok : Bool) (yIn : E) (hy : yIn ≠ phiE toyCols 2 a) :
    ¬ AccGood 1 ok yIn a (phiE toyCols 2) (deltaOf toyCols vs r) :=
  fun h ↦ hy h.2.1.symm

end Lvm.Acc.Toy
