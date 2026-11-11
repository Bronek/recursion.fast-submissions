-- New for lvm (WP-14a): the record's fit to the tables (`M3.fitsR`, INT-2) gives the facts the
-- phase specifications of WP-9/9b are stated with (the lvm instance `inst L T hτ` on
-- `L = ⟨nuMain, nuRec⟩`): the bus depth, the table rounds and evaluations, the heights, the
-- layout (`LayOk`), every constrained table reading or seeding.
import LvmVEqMid
import LvmM3Check

/-!
# `fitsR → inst` (INT-2's open item)

For `T = sumcheckTabs tabs` and `fitsR p tabs = true`:

* `μBus_eq`: `(inst L T hτ).μBus = p.busDepth` (leanVM's `μBus = ⌈log₂ pushLeaves⌉`, the record's
  `busDepth = log2Ceil (pushLeavesR tabs)`; `log2Ceil = Nat.clog 2`);
* `leafdecReads_eq`, `tableRounds_eq`, `tableEvals_eq`;
* `τ_le` (every height at most `L.μ = nuMain + 1`, `inst`'s `hτ`), `layOk_fit` (`colsFitB` gives
  WP-9b's `layOkB`, hence `LayOk`), `hcon_fit` (`inst_conditions`'s hypothesis).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm.M3 LeanVM.Protocol

/-- The layout of a parameter record: `C_main`, `C_rec`. -/
def layOf (p : Params) : Lay := ⟨p.nuMain, p.nuRec⟩

theorem layOf_P20 : layOf P20 = ⟨24, 19⟩ := rfl

/-- `log2Ceil` is `Nat.clog 2`. -/
theorem log2Ceil_eq_clog (n : ℕ) : log2Ceil n = Nat.clog 2 n := by
  unfold log2Ceil bitLength
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h0 : n - 1 = 0 := by omega
    simp only [h0, ↓reduceIte]
    exact (Nat.clog_of_right_le_one (by omega) _).symm
  · have h0 : n - 1 ≠ 0 := by omega
    simp only [h0, ↓reduceIte]
    apply le_antisymm
    · exact Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr
        (lt_of_le_of_lt (Nat.log2_self_le h0) (by omega)))
    · exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by have := Nat.lt_log2_self (n := n - 1); omega)

section Fit

variable (p : Params) (tabs : List Tab)

/-- The push leaves of the lvm instance, table by table. -/
theorem pushLeaves_inst (L : Lay) (T : List Tab) (hτ : ∀ t ∈ T, t.τ ≤ L.μ) :
    (inst L T hτ).pushLeaves = (T.map fun t ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ).sum := by
  have e : ∀ j : Fin T.length, (((inst L T hτ).flushes j).filter fun f ↦ decide (f.1 = Side.push)).length *
      2 ^ (inst L T hτ).τ j = (fun t : Tab ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ) (T.get j) :=
    fun j ↦ congrArg (· * 2 ^ (T.get j).τ) (flushes_push_length (T.get j))
  simp only [M3Instance.pushLeaves, List.filter_nil, List.map_nil, List.sum_nil, zero_add]
  rw [List.map_congr_left fun j _ ↦ e j]
  exact congrArg List.sum ((List.map_map (g := fun t : Tab ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ)
    (f := T.get) (l := List.finRange T.length)).symm.trans (by rw [List.map_get_finRange]))

/-- **The facts `fitsR` decides.** -/
structure Fit : Prop where
  leafdec : p.leafdecReads = 1
  busDepth : p.busDepth = log2Ceil (pushLeavesR tabs)
  busPos : 1 ≤ p.busDepth
  busLe : p.busDepth ≤ 22
  rounds : p.tableRounds = ((sumcheckTabs tabs).map (·.τ)).foldl max 0
  evals : p.tableEvals = ((sumcheckTabs tabs).map (·.w)).sum
  τle : ∀ t ∈ tabs, t.τ ≤ p.nuMain + 1
  hcon : ∀ t ∈ tabs, t.cons = [] ∨ t.reads ≠ [] ∨ t.seeds ≠ []
  cols : colsFitB p tabs = true
  /-- A23: the table point fits in `Φ`'s variables. -/
  accRounds : p.tableRounds ≤ accVars
  /-- A23: `fixCols` has at most `2^accLog` columns. -/
  nFix : (fixColsR (sumcheckTabs tabs) p.pubTab).length ≤ 2 ^ p.accLog
  /-- A23: `PUB` is a sumcheck table. -/
  pubTab : p.pubTab < (sumcheckTabs tabs).length
  /-- A23: `PUB` holds the header's lanes. -/
  pubTau : pubLanes ≤ 2 ^ (((sumcheckTabs tabs).map (·.τ)).getD p.pubTab 0)
  /-- A23: `PUB`'s column 0 is fixed. -/
  pubFix : ((sumcheckTabs tabs).map col0Fix).getD p.pubTab false = true

theorem fit_of (h : fitsR p tabs = true) : Fit p tabs := by
  simp only [fitsR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun t ht ↦ by
    rcases h8 t ht with (h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h), h9, h10, h11, h12, h13, h14⟩

variable {p tabs}

theorem mem_sumcheckTabs {t : Tab} (ht : t ∈ sumcheckTabs tabs) : t ∈ tabs :=
  (List.mem_filter.mp ht).1

/-- Every sumcheck table is at most `L.μ = nuMain + 1` high. -/
theorem Fit.hτ (F : Fit p tabs) : ∀ t ∈ sumcheckTabs tabs, t.τ ≤ (layOf p).μ :=
  fun t ht ↦ F.τle t (mem_sumcheckTabs ht)

/-- Every sumcheck table reads or seeds (WP-9b's `AllSc`). -/
theorem Fit.allSc (F : Fit p tabs) : AllSc (sumcheckTabs tabs) := by
  intro t ht
  have hf := (List.mem_filter.mp ht).2
  rcases F.hcon t (mem_sumcheckTabs ht) with h | h
  · simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, h] at hf
    simpa using hf
  · exact h

/-- `inst_conditions`'s hypothesis on the sumcheck tables. -/
theorem Fit.hcon' (F : Fit p tabs) :
    ∀ t ∈ sumcheckTabs tabs, t.cons ≠ [] → t.reads ≠ [] ∨ t.seeds ≠ [] :=
  fun t ht _ ↦ F.allSc t ht

/-- **The bus depth** of the lvm instance on the sumcheck tables is the record's. -/
theorem Fit.μBus_eq (F : Fit p tabs) (hτ : ∀ t ∈ sumcheckTabs tabs, t.τ ≤ (layOf p).μ) :
    (inst (layOf p) (sumcheckTabs tabs) hτ).μBus = p.busDepth := by
  rw [M3Instance.μBus, pushLeaves_inst, F.busDepth, log2Ceil_eq_clog]
  rfl

/-- The layout facts (`LayOk`) of the sumcheck tables. -/
theorem Fit.layOk (F : Fit p tabs) : LayOk (layOf p) (sumcheckTabs tabs) := by
  apply layOk_of_B
  have h := F.cols
  simp only [colsFitB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  simp only [layOkB, List.all_eq_true]
  intro t ht c hc
  have := h.2 t (mem_sumcheckTabs ht) c hc
  cases c with
  | com rec off =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    simp only [colOkB, layOf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨this.1, decide_eq_true this.2⟩, decide_eq_true h.1⟩
  | fix f ev => rfl

/-- **`μBus` at `P20`** (WP-14's request): the bus depth of `midS`'s tables. -/
theorem μBus_P20 (h : fitsR P20 tabs = true) (hτ : ∀ t ∈ sumcheckTabs tabs, t.τ ≤ (⟨24, 19⟩ : Lay).μ) :
    (inst ⟨24, 19⟩ (sumcheckTabs tabs) hτ).μBus = P20.busDepth :=
  (fit_of P20 tabs h).μBus_eq hτ

end Fit

end Lvm.VEq
