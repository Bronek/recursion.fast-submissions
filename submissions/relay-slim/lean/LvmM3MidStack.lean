-- new for lvm (WP-9b): the instance's stack of the two commitments, and a committed column's claim
-- as a claim on its commitment (WP-9's `LayOk`, `liftAt`/`readWith_liftAt` of `LvmM3Inst`, the
-- slice lemmas of WP-2's `LvmCpMultilinear`).
import LvmM3Inst
import LvmSpineSeams

/-!
# The stack of `C_main` and `C_rec`, and committed columns as blocks of them

* **`stackOf L qm qr`**: the instance's stack of `nuMain + 1` variables, `C_main`'s word `qm` in the
  low half and `C_rec`'s `qr` at `2^nuMain`, zero above it.
* **`column_stackOf`**: under `LayOk`, committed column `(rec, off)` of table `j`, read off
  `stackOf qm qr`, is the block of `2^τ` cells of its commitment at `off` (`comBlock`).
* **`colClaim_iff`**: so a claim on it holds iff the block's extension at the claim's point is the
  value; **`eval_comBlock`**: that extension is the commitment's at `z ++ bits(off / 2^τ)`, the
  stack point of the placement `⟨τ, off⟩` (the native `BlockClaim.point ⟨τ, off⟩ z v`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

variable (L : Lay)

/-- **The stack of the two commitments**: `qm` in the low half, `qr` at `2^nuMain`, zero above. -/
def stackOf (qm : Column L.nuMain) (qr : Column L.nuRec) : Column L.μ :=
  ⟨Vector.ofFn fun x ↦ if h : x.val < 2 ^ L.nuMain then qm.values[x.val] else
    if h' : x.val - 2 ^ L.nuMain < 2 ^ L.nuRec then qr.values[x.val - 2 ^ L.nuMain] else 0⟩

/-- Cell `n` of commitment `rec` (`C_rec` if `rec`, else `C_main`; `0` past it). -/
def comCell (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) (n : ℕ) : K :=
  if rec then (if h : n < 2 ^ L.nuRec then qr.values[n] else 0)
  else (if h : n < 2 ^ L.nuMain then qm.values[n] else 0)

/-- The block of `2^τ` cells of commitment `rec` from `off`. -/
def comBlock (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) (τ off : ℕ) : Column τ :=
  ⟨Vector.ofFn fun x ↦ comCell L qm qr rec (off + x.val)⟩

/-- A cell of the stack: `C_main`'s below `2^nuMain`, `C_rec`'s above. -/
theorem stackOf_getElem (qm : Column L.nuMain) (qr : Column L.nuRec) (n : ℕ) (hn : n < 2 ^ L.μ) :
    (stackOf L qm qr).values[n] = if n < 2 ^ L.nuMain then comCell L qm qr false n
      else comCell L qm qr true (n - 2 ^ L.nuMain) := by
  simp only [stackOf, Vector.getElem_ofFn, comCell]
  by_cases h : n < 2 ^ L.nuMain
  · simp [h]
  · simp [h]

variable (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **A committed column read off the stack of the commitments is its block** (under `LayOk`). -/
theorem column_stackOf (hlay : LayOk L tabs) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (j : Fin tabs.length) (i : Fin (tabs.get j).w) {rec : Bool} {off : ℕ}
    (hcol : (tabs.get j).cols[i.val]? = some (.com rec off)) :
    (inst L tabs hτ).column (stackOf L qm qr) ⟨j, i⟩ = comBlock L qm qr rec (tabs.get j).τ off := by
  have hal := hlay (tabs.get j) (List.get_mem _ _) i.val i.isLt
  unfold Aligned at hal
  rw [hcol] at hal
  obtain ⟨hdvd, hfit, hnu⟩ := hal
  have hder : (inst L tabs hτ).derived ⟨j, i⟩ = none := by
    simp only [inst, Tab.fixedOf, hcol, Option.map_none]
  have hτμ : (tabs.get j).τ ≤ L.μ := hτ _ (List.get_mem _ _)
  have hso : stackOff L (tabs.get j) i.val = off + if rec then 2 ^ L.nuMain else 0 := by
    simp only [stackOff, hcol]
  have hτm : (tabs.get j).τ ≤ L.nuMain := by
    have h1 : 2 ^ (tabs.get j).τ ≤ 2 ^ (if rec then L.nuRec else L.nuMain) := by omega
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    cases rec
    · simpa using h2
    · exact le_trans (by simpa using h2) hnu
  have hdvd' : 2 ^ (tabs.get j).τ ∣ stackOff L (tabs.get j) i.val := by
    rw [hso]
    refine Nat.dvd_add hdvd ?_
    split
    · exact Nat.pow_dvd_pow 2 hτm
    · exact Nat.dvd_zero _
  have hfit' : stackOff L (tabs.get j) i.val + 2 ^ (tabs.get j).τ ≤ 2 ^ L.μ := by
    rw [hso, Lay.μ, pow_succ]
    have : 2 ^ L.nuRec ≤ 2 ^ L.nuMain := Nat.pow_le_pow_right (by norm_num) hnu
    cases rec <;> simp at hfit ⊢ <;> omega
  have hsel : (selOf L (tabs.get j) hτμ i.val).val = stackOff L (tabs.get j) i.val / 2 ^ (tabs.get j).τ := by
    simp only [selOf, dif_pos (And.intro hdvd' hfit')]
  have hread := readWith_liftAt (fun c : (inst L tabs hτ).ColumnId ↦ hτ _ (List.get_mem _ c.1))
    (fun c ↦ selOf L (tabs.get c.1) (hτ _ (List.get_mem _ c.1)) c.2) (stackOf L qm qr) ⟨j, i⟩
  have hcolv : (inst L tabs hτ).column (stackOf L qm qr) ⟨j, i⟩ =
      (inst L tabs hτ).layout.read (stackOf L qm qr) ⟨j, i⟩ := by
    unfold M3Instance.column; rw [hder]; rfl
  rw [hcolv]
  show (⟨((inst L tabs hτ).layout.read (stackOf L qm qr) ⟨j, i⟩).values⟩ : Column _) =
    ⟨(comBlock L qm qr rec (tabs.get j).τ off).values⟩
  congr 1
  change (Layout.readWith (fun c : (inst L tabs hτ).ColumnId ↦ liftAt (hτ _ (List.get_mem _ c.1))
    (selOf L (tabs.get c.1) (hτ _ (List.get_mem _ c.1)) c.2)) (stackOf L qm qr) ⟨j, i⟩).values = _
  rw [hread]
  apply Vector.ext
  intro x hx
  have hxl : x < 2 ^ (tabs.get j).τ := hx
  rw [slice_getElem_nat _ _ hxl, Vector.getElem_cast, stackOf_getElem]
  simp only [comBlock, Vector.getElem_ofFn]
  have key : ∀ n, n = off + x + (if rec then 2 ^ L.nuMain else 0) →
      (if n < 2 ^ L.nuMain then comCell L qm qr false n else comCell L qm qr true (n - 2 ^ L.nuMain)) =
        comCell L qm qr rec (off + x) := by
    intro n hn
    subst hn
    cases rec
    · have h1 : off + x < 2 ^ L.nuMain := by simp only [Bool.false_eq_true, ite_false] at hfit; omega
      simp [h1]
    · have h2 : ¬ off + x + 2 ^ L.nuMain < 2 ^ L.nuMain := by omega
      simp [h2]
  refine key _ ?_
  show x + 2 ^ (tabs.get j).τ * (selOf L (tabs.get j) hτμ i.val).val = _
  rw [hsel, Nat.mul_div_cancel' hdvd', hso]; omega

/-- **A committed column's claim on the stack of the commitments is a claim on its block.** -/
theorem colClaim_iff (hlay : LayOk L tabs) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (c : ColumnClaim (inst L tabs hτ)) {rec : Bool} {off : ℕ}
    (hcol : (tabs.get c.col.1).cols[c.col.2.val]? = some (ColSrc.com rec off)) :
    c.Holds (stackOf L qm qr) ↔
      eval₂Mle (comBlock L qm qr rec (tabs.get c.col.1).τ off).values (algebraMap K E) c.point =
        c.value := by
  unfold ColumnClaim.Holds
  rw [column_stackOf L tabs hτ hlay qm qr c.col.1 c.col.2 hcol]

/-- **A block's extension is its commitment's at the placement's stack point**: for a block of
`2^τ` cells at `off = 2^τ·s` of a commitment of `ν ≥ τ` variables, its extension at `z` is the
commitment's at `z ++ bits(s)`. -/
theorem eval_block {ν τ : ℕ} (h : τ ≤ ν) (w : CMlPolynomialEval K ν) (s : ℕ)
    (hs : s < 2 ^ (ν - τ)) (z : Vector E τ) :
    eval₂Mle (Vector.ofFn fun x : Fin (2 ^ τ) ↦ w[2 ^ τ * s + x.val]'(by
        have := x.isLt
        calc 2 ^ τ * s + x.val < 2 ^ τ * s + 2 ^ τ := by omega
          _ = 2 ^ τ * (s + 1) := by ring
          _ ≤ 2 ^ τ * 2 ^ (ν - τ) := Nat.mul_le_mul_left _ hs
          _ = 2 ^ ν := by rw [← pow_add, Nat.add_sub_cancel' h])) (algebraMap K E) z =
      eval₂Mle w (algebraMap K E)
        (Vector.cast (Nat.add_sub_cancel' h) (z ++ (boolVec ⟨s, hs⟩ : Vector E (ν - τ)))) := by
  have e := Nat.add_sub_cancel' h
  have key := eval₂Mle_cast (algebraMap K E) e (Vector.cast (congrArg (2 ^ ·) e.symm) w)
    (z ++ (boolVec ⟨s, hs⟩ : Vector E (ν - τ)))
  rw [Vector.cast_cast, Vector.cast_rfl] at key
  rw [key, eval₂Mle, eval₂Mle, evalMle_append_boolVec, ← slice_map]
  congr 2
  apply Vector.ext
  intro x hx
  rw [slice_getElem_nat _ _ hx, Vector.getElem_ofFn, Vector.getElem_cast]
  simp only [Nat.add_comm (2 ^ τ * s) x]

/-- **`C_main`'s block**: the extension of a committed `C_main` column (block at `off`, aligned,
inside `C_main`) at `z` is `C_main`'s at the placement's stack point. -/
theorem eval_comBlock_main (qm : Column L.nuMain) (qr : Column L.nuRec) {τ off : ℕ}
    (hτ' : τ ≤ L.nuMain) (hdvd : 2 ^ τ ∣ off) (hfit : off + 2 ^ τ ≤ 2 ^ L.nuMain) (z : Vector E τ) :
    eval₂Mle (comBlock L qm qr false τ off).values (algebraMap K E) z =
      eval₂Mle qm.values (algebraMap K E) (Vector.cast (Nat.add_sub_cancel' hτ')
        (z ++ (boolVec ⟨off / 2 ^ τ, by
          have := Nat.div_mul_cancel hdvd
          have h2 : 2 ^ L.nuMain = 2 ^ τ * 2 ^ (L.nuMain - τ) := by rw [← pow_add, Nat.add_sub_cancel' hτ']
          have hp : 0 < 2 ^ τ := Nat.two_pow_pos _
          rw [h2] at hfit
          have : 2 ^ τ * (off / 2 ^ τ + 1) ≤ 2 ^ τ * 2 ^ (L.nuMain - τ) := by
            rw [mul_add, mul_one, Nat.mul_div_cancel' hdvd]; exact hfit
          exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_left this hp)⟩ : Vector E (L.nuMain - τ)))) := by
  rw [← eval_block hτ' qm.values]
  congr 1
  apply Vector.ext
  intro x hx
  simp only [comBlock, comCell, Vector.getElem_ofFn, Bool.false_eq_true, ite_false,
    Nat.mul_div_cancel' hdvd]
  rw [dif_pos (by omega)]

/-- **`C_rec`'s block**, as `eval_comBlock_main`. -/
theorem eval_comBlock_rec (qm : Column L.nuMain) (qr : Column L.nuRec) {τ off : ℕ}
    (hτ' : τ ≤ L.nuRec) (hdvd : 2 ^ τ ∣ off) (hfit : off + 2 ^ τ ≤ 2 ^ L.nuRec) (z : Vector E τ) :
    eval₂Mle (comBlock L qm qr true τ off).values (algebraMap K E) z =
      eval₂Mle qr.values (algebraMap K E) (Vector.cast (Nat.add_sub_cancel' hτ')
        (z ++ (boolVec ⟨off / 2 ^ τ, by
          have h2 : 2 ^ L.nuRec = 2 ^ τ * 2 ^ (L.nuRec - τ) := by rw [← pow_add, Nat.add_sub_cancel' hτ']
          have hp : 0 < 2 ^ τ := Nat.two_pow_pos _
          rw [h2] at hfit
          have : 2 ^ τ * (off / 2 ^ τ + 1) ≤ 2 ^ τ * 2 ^ (L.nuRec - τ) := by
            rw [mul_add, mul_one, Nat.mul_div_cancel' hdvd]; exact hfit
          exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_left this hp)⟩ : Vector E (L.nuRec - τ)))) := by
  rw [← eval_block hτ' qr.values]
  congr 1
  apply Vector.ext
  intro x hx
  simp only [comBlock, comCell, Vector.getElem_ofFn, ite_true, Nat.mul_div_cancel' hdvd]
  rw [dif_pos (by omega)]

end Lvm.M3
