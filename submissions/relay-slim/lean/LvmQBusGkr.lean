-- New for lvm (WP-11b-QA2, H2): the grand-product GKR step's final arithmetic as straight-line
-- gadgets (QL's builder). Searched leanerVM `Protocol/Bus.lean` (`prod_sideLeaves`, a Fin-product
-- statement) and FR's GKR-free verifier: nothing at the row level to adapt.
import LvmQBusBase

/-!
# The GKR step's finals (`F`'s `gkrStep`, after its sumcheck)

`F`'s `gkrStep step` (`LvmDecideSumcheck`): the claim `polyEval values combiner` (3 values), an
equality-mode sumcheck (`LvmQBusRound`), the children (3 × `2^step` scalars), the check
`claim == polyEval (children.map prodE) combiner`, and the next values
`children.map (multilinearEval · y)`. Straight-line gadgets, generic in the list lengths:

* `hornerG z γ xs`: `polyEval xs γ` (Horner; `|xs| − 1` `E·E+E` rows);
* `prodCells z o xs`: `prodE xs` (`|xs| − 1` rows);
* `mlG z y xs`: `multilinearEval xs y` (per fold pair one `lin` and one `E·E+E` row);
* `gkrFinals`: the products, the gated check (`assertEq`), the three values.

Inputs are `E` cells (the children and challenges loaded by the caller), `z` a zero cell, `o` a one
cell, `gate` the node flag. Theorems: `hornerG_spec`, `prodCells_spec`, `mlG_spec`,
**`gkrFinals_spec`** (values = `F`'s, assertion ↔ `gate · (polyEval products γ + claim) = 0`) and
**`gkrFinals_check`** (gate on: assertion ↔ `F`'s check `claim == polyEval products γ`).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build.QB

open Lvm.Loop Lvm.QB

/-- The values of a list of cells. -/
def vals (M : Mem) (xs : List Cell) : List FE := xs.map (·.val M)

/-! ## `polyEval`, `prodE`, `multilinearEval` -/

/-- `polyEval xs γ` by Horner from the top coefficient (`z` for no coefficient). -/
def hornerG (z γ : Cell) : List Cell → BM Cell
  | [] => pure z
  | [a] => pure a
  | a :: b :: rest => do
    let h ← hornerG z γ (b :: rest)
    mulAdd .E h γ a

/-- The running product `acc · x₀ · x₁ ⋯` (`z` a zero cell for the addend). -/
def prodG (z : Cell) : Cell → List Cell → BM Cell
  | acc, [] => pure acc
  | acc, x :: xs => do
    let a ← mulAdd .E acc x z
    prodG z a xs

/-- `prodE xs` (`o` a one cell for the empty product). -/
def prodCells (z o : Cell) : List Cell → BM Cell
  | [] => pure o
  | x :: xs => prodG z x xs

/-- One fold of `multilinearEval` at `r`: pairs `(a, b)` become `r·(a + b) + a`. -/
def foldPairsG (r : Cell) : List Cell → BM (List Cell)
  | a :: b :: rest => do
    let d ← lin .E 1 0 a b
    let v ← mulAdd .E r d a
    let vs ← foldPairsG r rest
    pure (v :: vs)
  | _ => pure []

/-- `multilinearEval xs y`: one fold per coordinate of `y` (`z` for an empty result). -/
def mlG (z : Cell) : List Cell → List Cell → BM Cell
  | [], xs => pure (xs.headD z)
  | r :: rs, xs => do
    let xs' ← foldPairsG r xs
    mlG z rs xs'

section
variable {c : Ctx} {M : Mem}

theorem hornerG_spec {z γ : Cell} (hz : z.val M = 0) : ∀ xs : List Cell,
    ASpec c M (hornerG z γ xs) (fun r => r.val M = polyEval (vals M xs) (γ.val M)) True
  | [] => aspec_pure (by simp [vals, polyEval, hz])
  | [a] => aspec_pure (by simp [vals, polyEval])
  | a :: b :: rest => by
    show ASpec c M (hornerG z γ (b :: rest) >>= fun h => mulAdd .E h γ a) _ _
    refine aspec_congr (aspec_bind (hornerG_spec (γ := γ) hz (b :: rest)) fun h hh =>
      aspec_congr (aspec_mulAdd (c := c) (M := M) .E h γ a)
        (Q := fun r => r.val M = polyEval (vals M (a :: b :: rest)) (γ.val M))
        (fun r hr => by rw [hr, hh]; simp [vals, polyEval]) Iff.rfl) (fun _ h => h) (true_and _).to_iff

theorem prodG_spec {z : Cell} (hz : z.val M = 0) : ∀ (xs : List Cell) (acc : Cell),
    ASpec c M (prodG z acc xs) (fun r => r.val M = (vals M xs).foldl (· * ·) (acc.val M)) True
  | [], acc => aspec_pure (by simp [vals])
  | x :: xs, acc => by
    show ASpec c M (mulAdd .E acc x z >>= fun a => prodG z a xs) _ _
    refine aspec_congr (aspec_bind (aspec_mulAdd (c := c) (M := M) .E acc x z) fun a ha =>
      aspec_congr (prodG_spec hz xs a)
        (Q := fun r => r.val M = (vals M (x :: xs)).foldl (· * ·) (acc.val M))
        (fun r hr => by rw [hr, ha, hz, add_zero]; simp [vals]) Iff.rfl) (fun _ h => h)
      (true_and _).to_iff

theorem prodCells_spec {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (xs : List Cell) :
    ASpec c M (prodCells z o xs) (fun r => r.val M = prodE (vals M xs)) True := by
  cases xs with
  | nil => exact aspec_pure (by simp [vals, prodE, ho])
  | cons x xs =>
    exact aspec_congr (prodG_spec hz xs x) (fun r hr => by rw [hr]; simp [vals, prodE]) Iff.rfl

theorem foldPairsG_spec {r : Cell} : ∀ xs : List Cell,
    ASpec c M (foldPairsG r xs) (fun out => vals M out = foldPairs (r.val M) (vals M xs)) True
  | a :: b :: rest => by
    show ASpec c M (lin .E 1 0 a b >>= fun d => mulAdd .E r d a >>= fun v =>
      foldPairsG r rest >>= fun vs => pure (v :: vs)) _ _
    refine aspec_congr (aspec_bind (aspec_lin (c := c) (M := M) .E 1 0 a b) fun d hd =>
      aspec_bind (aspec_mulAdd (c := c) (M := M) .E r d a) fun v hv =>
        aspec_bind (foldPairsG_spec (r := r) rest) fun vs hvs =>
          aspec_pure (x := v :: vs)
            (P := fun out => vals M out = foldPairs (r.val M) (vals M (a :: b :: rest)))
            (by
              simp only [vals, List.map_cons, foldPairs] at hvs ⊢
              rw [hvs, hv, hd, ofK_one, ofK_zero, one_mul, add_zero]
              congr 1
              ring)) (fun _ h => h) (by simp)
  | [] => aspec_pure (by simp [vals, foldPairs])
  | [a] => aspec_pure (by simp [vals, foldPairs])

theorem mlG_spec {z : Cell} (hz : z.val M = 0) : ∀ (y xs : List Cell),
    ASpec c M (mlG z y xs) (fun r => r.val M = multilinearEval (vals M xs) (vals M y)) True
  | [], xs => aspec_pure (by cases xs <;> simp [vals, multilinearEval, hz])
  | r :: rs, xs => by
    show ASpec c M (foldPairsG r xs >>= fun xs' => mlG z rs xs') _ _
    refine aspec_congr (aspec_bind (foldPairsG_spec (c := c) (M := M) (r := r) xs) fun xs' hxs' =>
      aspec_congr (mlG_spec hz rs xs')
        (Q := fun out => out.val M = multilinearEval (vals M xs) (vals M (r :: rs)))
        (fun out hout => by
          rw [hout, hxs']
          simp [multilinearEval, vals]) Iff.rfl) (fun _ h => h) (true_and _).to_iff

end

/-! ## The step's finals -/

/-- **A GKR step's finals**: the children's products, the gated check
`claim = polyEval [P₀, P₁, P₂] γ`, and the children's values at `y`. -/
def gkrFinals (z o gate γ claim : Cell) (c₀ c₁ c₂ y : List Cell) : BM (List Cell) := do
  let p₀ ← prodCells z o c₀
  let p₁ ← prodCells z o c₁
  let p₂ ← prodCells z o c₂
  let q ← hornerG z γ [p₀, p₁, p₂]
  assertEq q claim gate
  let v₀ ← mlG z y c₀
  let v₁ ← mlG z y c₁
  let v₂ ← mlG z y c₂
  pure [v₀, v₁, v₂]

/-- The products `F` checks: `children.map prodE`. -/
def gkrProducts (M : Mem) (c₀ c₁ c₂ : List Cell) : List FE := [c₀, c₁, c₂].map fun ch => prodE (vals M ch)

/-- The values `F` passes on: `children.map (multilinearEval · y)`. -/
def gkrValues (M : Mem) (c₀ c₁ c₂ y : List Cell) : List FE :=
  [c₀, c₁, c₂].map fun ch => multilinearEval (vals M ch) (vals M y)

section
variable {c : Ctx} {M : Mem}

/-- **The step's finals**: the outputs are `F`'s next values, and the assertion is
`gate · (polyEval products γ + claim) = 0`. -/
theorem gkrFinals_spec {z o gate γ claim : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (c₀ c₁ c₂ y : List Cell) :
    ASpec c M (gkrFinals z o gate γ claim c₀ c₁ c₂ y)
      (fun out => vals M out = gkrValues M c₀ c₁ c₂ y)
      (gate.val M * (polyEval (gkrProducts M c₀ c₁ c₂) (γ.val M) + claim.val M) = 0) := by
  have := aspec_bind (prodCells_spec (c := c) hz ho c₀) fun p₀ h₀ =>
    aspec_bind (prodCells_spec (c := c) hz ho c₁) fun p₁ h₁ =>
      aspec_bind (prodCells_spec (c := c) hz ho c₂) fun p₂ h₂ =>
        aspec_bind (hornerG_spec (c := c) (γ := γ) hz [p₀, p₁, p₂]) fun q hq =>
          aspec_bind (aspec_congr (aspec_assertEq (c := c) (M := M) q claim gate) (fun _ _ => trivial)
            (B := gate.val M * (polyEval (gkrProducts M c₀ c₁ c₂) (γ.val M) + claim.val M) = 0)
            (by rw [hq]; simp only [vals, List.map_cons, List.map_nil, gkrProducts, h₀, h₁, h₂]))
            fun _ _ =>
            aspec_bind (mlG_spec (c := c) hz y c₀) fun v₀ hv₀ =>
              aspec_bind (mlG_spec (c := c) hz y c₁) fun v₁ hv₁ =>
                aspec_bind (mlG_spec (c := c) hz y c₂) fun v₂ hv₂ =>
                  aspec_pure (x := [v₀, v₁, v₂]) (P := fun out => vals M out = gkrValues M c₀ c₁ c₂ y)
                    (by simp only [vals, List.map_cons, List.map_nil, gkrValues] at hv₀ hv₁ hv₂ ⊢
                        rw [hv₀, hv₁, hv₂])
  exact aspec_congr this (fun _ h => h) (by simp only [true_and, and_true])

/-- **Q_arith_eq, the GKR step's check**: with the gate on, the gadget's assertion holds iff `F`'s
`require (claim == polyEval products combiner)` passes. -/
theorem gkrFinals_check {z o gate γ claim : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hg : gate.val M = 1) (c₀ c₁ c₂ y : List Cell) (p : Ptr)
    (h : SegsHold c M p (gkrFinals z o gate γ claim c₀ c₁ c₂ y p).2) :
    vals M (gkrFinals z o gate γ claim c₀ c₁ c₂ y p).1 = gkrValues M c₀ c₁ c₂ y ∧
      (SegsAssert M p (gkrFinals z o gate γ claim c₀ c₁ c₂ y p).2 ↔
        (claim.val M == polyEval (gkrProducts M c₀ c₁ c₂) (γ.val M)) = true) := by
  obtain ⟨h1, h2⟩ := gkrFinals_spec (c := c) hz ho c₀ c₁ c₂ y p h
  refine ⟨h1, ?_⟩
  rw [h2, gate_eq_iff hg, FE.beq_iff, eq_comm]

/-- The step's first claim, `polyEval values combiner` (`F`: `polyEval state.values combiner`). -/
theorem gkrClaim_spec {z γ : Cell} (hz : z.val M = 0) (vs : List Cell) :
    ASpec c M (hornerG z γ vs) (fun r => r.val M = polyEval (vals M vs) (γ.val M)) True :=
  hornerG_spec hz vs

end

/-- Non-vacuity: a one-level step's finals pass the program check. -/
theorem gkrFinals_segsOk :
    segsOk ⟨1, 20⟩ (gkrFinals (ec 0) (ec 1) (kc 0) (ec 2) (ec 3) [ec 4, ec 5] [ec 6, ec 7] [ec 8, ec 9]
      [ec 10] ⟨1, 20⟩).2 = true := by decide

end Lvm.Loop.Build.QB
