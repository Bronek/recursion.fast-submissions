-- WP-14c (NodeSound, O10). New for lvm, adapted from WP-9's `inKOf_pub` (LvmM3Loop): a committed
-- input array's cell is its commitment's word (with WP-9b's `column_stackOf`, LvmM3MidStack).
import LvmM3Loop
import LvmM3MidStack

/-!
# Committed input arrays on the stack of the two commitments

**`inKOf_com`**: under `InOk` and `LayOk`, the `K` input cell `base + stride·x` of a committed `K`
array whose value column is placed at `(rec, off)` holds, on the stack `stackOf L qm qr`, word
`off + x` of commitment `rec` (`C_rec` if `rec`, else `C_main`). This turns the input arrays of
A19 (the stream, `σ'`, the `KS` `X` messages and `Y` digests) into words of the candidate pair.
-/

set_option autoImplicit false

namespace Lvm.NS

open LeanVM.Parameters LeanVM.Protocol Lvm.M3 Lvm.Loop

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **A committed `K` array's input cell is its commitment's word.** -/
theorem inKOf_com (hok : InOk Q arrs) (hlay : LayOk L (lvmTabs Q pl groups arrs aux))
    (qm : Column L.nuMain) (qr : Column L.nuRec) {k : ℕ} (hk : k < arrs.length)
    (hty : arrs[k].ty = .K) (hpub : arrs[k].pub = none) {rec : Bool} {off : ℕ}
    (hval : arrs[k].val = [(rec, off)]) {x : ℕ} (hx : x < 2 ^ arrs[k].τ) :
    (inKOf Q pl groups arrs aux L hτ (stackOf L qm qr)).getD (arrs[k].base + arrs[k].stride * x) 0 =
      FK.ofBF64 (comCell L qm qr rec (off + x)) := by
  have hmem : arrs[k] ∈ arrs := List.getElem_mem hk
  have hlt : arrs[k].base + arrs[k].stride * x < Q.nInK := by
    have := hok.lt _ hmem x hx; rwa [hty] at this
  have hfind := findIn_eq Q arrs hok hk hx
  rw [hty] at hfind
  have hj : groups.length + k < (lvmTabs Q pl groups arrs aux).length := by
    rw [lvmTabs_length]; omega
  have hget := get_arr Q pl groups arrs aux hk hj
  have hτeq : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ = arrs[k].τ := by rw [hget]; rfl
  have hxt : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ := by rw [hτeq]; exact hx
  have hw : 0 < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by
    rw [hget]; simp [InArr.tab, Tab.w]
  have hcol : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).cols[0]? = some (.com rec off) := by
    rw [hget]; simp [InArr.tab, InArr.vcols, hpub, hval]
  have hc := column_stackOf L (lvmTabs Q pl groups arrs aux) hτ hlay qm qr ⟨_, hj⟩ ⟨0, hw⟩ hcol
  simp only [inKOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hlt, Option.getD_some,
    hfind, inVal, dif_pos hj, dif_pos hxt, dif_pos hw]
  congr 1
  simp only [M3Instance.row]
  rw [hc]
  simp [comBlock, Vector.get]
  rfl

end Lvm.NS
