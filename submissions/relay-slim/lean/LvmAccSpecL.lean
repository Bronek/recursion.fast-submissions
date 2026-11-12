-- new for lvm (AC-S): phase 3b of the lvm instance on the wire (AC-N's proposed DSL instance, its
-- bodies), and why its pass means the table seam's fixed claims hold. The proof pattern of the
-- last step is WP-9b's `derived_holds` (`LvmM3FidFixC`).
import LvmAccSpecRet
import LvmM3FidNative

/-!
# Phase 3b of the lvm instance

Over `E` (native forms through `FE.toExt3`/`FE.ofExt3`, as WP-9b's `fixedEvalV`), on the claims `cl`
the table phase returned, for the sumcheck tables `T`:

* `claimAt cl n`: the first claim on global column `n`; `gcol T c`: a `fixCols` column's number;
* `pubOkV`: `PUB`'s value column (table `pubTab`, column 0) has `pubEval` of the header lanes;
* `yOwnV`: `dot (eqKernel κ) (v_fix)`; `tablePointV`: the longest claim point (AC-V's `tablePoint`);
* `PhiV P tabs pub = toExt3 ∘ PhiC ∘ ofExt3` (`= phiE (fixColsR T pubTab) tableRounds`, rfl);
* **`accProgV P tabs pub cl`**: `accProg` with these (what AC-N's `midS` runs after the table phase);
* `claimAt_eq` (one claim per column), `tablePointV_eq` (the longest point is the sumcheck point);
* **`holds_of_good`**: if the phase's checks can all pass (`AccGood`: the `PUB` check, and every
  fixed claim's error `δ_k` zero), every fixed column's claim of the table seam holds of every stack.
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
open Lvm.M3 (Tab ColSrc FixCol fixColsR sumcheckTabs vTables Lay inst colOfL FixOk pubEval)
open LeanVM.Protocol.Compile (VerifierProgram)

/-! ## The definitions (AC-N's proposal, relayed 2026-11-10) -/

/-- The first claim on global column `n` (the default claim if none). -/
def claimAt (cl : List ColumnClaim) (n : ℕ) : ColumnClaim := (cl.find? (·.column == n)).getD default

/-- A `fixCols` column's global number. -/
def gcol (T : List Tab) (c : FixCol) : ℕ := (globalColumnBases (vTables T)).getD c.tab 0 + c.col

/-- **`PUB`'s check**: the claim on table `pubTab`'s column 0 has the header lanes' extension at
its point (AC-V's `pubCheckR` over `E`). -/
def pubOkV (T : List Tab) (pubTab : ℕ) (pub : Pub) (cl : List ColumnClaim) : Bool :=
  let c := claimAt cl ((globalColumnBases (vTables T)).getD pubTab 0 + 0)
  decide (c.value = FE.toExt3 (pubEval pub.hdrLanes (c.point.map FE.ofExt3)))

/-- **`y_own(κ)`**: `dot (eqKernel κ)` of the claims on the `fixCols` columns. -/
def yOwnV (T : List Tab) (pubTab : ℕ) (cl : List ColumnClaim) (κ : List E) : E :=
  Verifier.dot (Verifier.eqKernel κ) ((fixColsR T pubTab).map fun c ↦ (claimAt cl (gcol T c)).value)

/-- **The table point**: the longest claim point (AC-V's `tablePoint`). -/
def tablePointV (cl : List ColumnClaim) : List E :=
  cl.foldl (fun r c ↦ if r.length < c.point.length then c.point else r) []

/-- **`Φ̃` over `E`**: the native `PhiC` of the real instance through `toExt3`. -/
def PhiV (P : Params) (tabs : Pub → List Tab) (pub : Pub) (p : List E) : E :=
  FE.toExt3 (PhiC P (M3.real P tabs) pub (p.map FE.ofExt3))

/-- **Phase 3b of the lvm instance** on the claims `cl` of the table phase. -/
def accProgV (P : Params) (tabs : Pub → List Tab) (pub : Pub) (cl : List ColumnClaim) :
    VerifierProgram Unit :=
  let T := sumcheckTabs (tabs pub)
  accProg P.accLog accVars (pubOkV T P.pubTab pub cl) (FE.toExt3 pub.accIn.y)
    (pub.accIn.pt.map FE.toExt3) (yOwnV T P.pubTab cl) (fun κ ↦ tablePointV cl ++ κ) (PhiV P tabs pub)

theorem phiV_eq (P : Params) (tabs : Pub → List Tab) (pub : Pub) :
    PhiV P tabs pub = phiE (fixColsR (sumcheckTabs (tabs pub)) P.pubTab) P.tableRounds := rfl

/-- **`AccOk acc_in` over `E`** is the native one. -/
theorem accOk_iff (P : Params) (tabs : Pub → List Tab) (pub : Pub) :
    AccOk P (M3.real P tabs) pub pub.accIn = true ↔
      PhiV P tabs pub (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y := by
  have hb : ∀ x y : FE, (x == y) = true ↔ x = y := fun x y ↦ ⟨Lvm.M3.FE_eq_of_beq, fun h ↦ by
    subst h; change (x.c₀ == x.c₀ && x.c₁ == x.c₁ && x.c₂ == x.c₂) = true; simp⟩
  rw [AccOk, hb, PhiV, List.map_map]
  simp only [Function.comp_def, FE.ofExt3_toExt3, List.map_id']
  exact FE.toExt3_inj.symm

/-! ## Reading the claims -/

/-- **One claim per column**: in a list with strictly increasing columns, the first claim on a
member's column is the member. -/
theorem claimAt_eq : ∀ {cl : List ColumnClaim}, (cl.map (·.column)).Pairwise (· < ·) →
    ∀ {c : ColumnClaim}, c ∈ cl → claimAt cl c.column = c
  | [], _, _, h => by simp at h
  | d :: cl, hp, c, hc => by
    rw [List.map_cons, List.pairwise_cons] at hp
    unfold claimAt
    rw [List.find?_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · have hlt := hp.1 c.column (List.mem_map_of_mem hc)
      rw [show (d.column == c.column) = false by simp; omega]
      exact claimAt_eq hp.2 hc

/-- The longest point of claims that are prefixes of `pt`, one of them `pt` itself, is `pt`. -/
theorem tablePointV_eq {cl : List ColumnClaim} {pt : List E}
    (hpre : ∀ c ∈ cl, ∃ m, c.point = pt.take m) (hfull : ∃ c ∈ cl, c.point = pt) :
    tablePointV cl = pt := by
  suffices h : ∀ (l : List ColumnClaim) (r : List E), (∀ c ∈ l, ∃ m, c.point = pt.take m) →
      (∃ m, r = pt.take m) →
      (∃ m, l.foldl (fun r c ↦ if r.length < c.point.length then c.point else r) r = pt.take m) ∧
        (∀ c ∈ l, c.point.length ≤
          (l.foldl (fun r c ↦ if r.length < c.point.length then c.point else r) r).length) ∧
        r.length ≤ (l.foldl (fun r c ↦ if r.length < c.point.length then c.point else r) r).length by
    obtain ⟨⟨m, hm⟩, hle, -⟩ := h cl [] hpre ⟨0, by simp⟩
    obtain ⟨c, hc, hcp⟩ := hfull
    have := hle c hc
    rw [hcp, hm] at this
    rw [tablePointV, hm]
    exact List.take_of_length_le (by simpa using this)
  intro l
  induction l with
  | nil => intro r _ hr; exact ⟨hr, by simp, le_rfl⟩
  | cons c l ih =>
    intro r hl hr
    have hc := hl c List.mem_cons_self
    have hl' := fun d hd ↦ hl d (List.mem_cons_of_mem _ hd)
    simp only [List.foldl_cons]
    split_ifs with hlt
    · obtain ⟨h1, h2, h3⟩ := ih c.point hl' hc
      exact ⟨h1, fun d hd ↦ (List.mem_cons.mp hd).elim (fun h ↦ h ▸ h3) (h2 d), by omega⟩
    · obtain ⟨h1, h2, h3⟩ := ih r hl' hr
      exact ⟨h1, fun d hd ↦ (List.mem_cons.mp hd).elim (fun h ↦ by subst h; omega) (h2 d), h3⟩

/-- A fixed column outside `PUB`'s value column is listed in `fixCols`. -/
theorem mem_fixColsR_of {T : List Tab} {pubTab j i : ℕ} {t : Tab} {f : ℕ → FK} {ev : List FE → FE}
    (ht : T[j]? = some t) (hc : t.cols[i]? = some (.fix f ev)) (hn : ¬ (j = pubTab ∧ i = 0)) :
    (⟨j, t.τ, i, ev⟩ : FixCol) ∈ fixColsR T pubTab := by
  unfold fixColsR
  refine List.mem_flatMap.mpr ⟨(t, j), List.mem_zipIdx_iff_getElem?.mpr ht, ?_⟩
  refine List.mem_filterMap.mpr ⟨(.fix f ev, i), List.mem_zipIdx_iff_getElem?.mpr hc, ?_⟩
  simp only
  rw [ite_eq_right_iff.mpr (by simp at hn ⊢; omega)]

end Lvm.Acc
