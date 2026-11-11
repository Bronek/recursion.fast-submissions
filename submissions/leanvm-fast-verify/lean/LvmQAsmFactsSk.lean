-- New for lvm (WP-16a2, FIN-TF): the table-level static facts of the `P20` node program, generic
-- part (no decision on the placement record or on `P20`'s numbers).
-- adapted from rf-lvm-QFX/submissions/leanvm-inspired/lean/LvmQAsmFactsSk.lean (uncommitted, WP-16a-QFX)
-- and LvmQAsmFactsStatic.lean (`arrs_pub`); A23's new `fitsR` conjuncts and V-PERF's `M3.Q20` added.
import LvmQAsmFacts
import LvmQAsmInb
import LvmM3Check
import LvmM3CheckIn

/-!
# The tables' structural checks, generic part

* **`tabSk`**: a table with its fixed columns' closures dropped; `tabsP20_sk`: the skeletons of
  `M3.tabsP20 P` do not depend on `P` (only `PUB`'s closures do).
* **`chkB`**: the read counts inside the widths (`AuxStatic.cnt`), the read count bound (`len`), the
  committed columns aligned (`LayOk`), `KeysOk`, positive widths, the constraint count, every table
  with a constraint, read or seed (`sumcheckTabs = id`); invariant under `tabSk` (`chkB_sk`).
* **`fitsR_sk`**: `fitsR p` reads only the skeletons (A23's `fixCols` count, `PUB`'s height and fixed
  column 0 included), so `fitsR P20 (M3.tabsP20 P)` is one decision at `default` (`fit20_of`).
* `chk20_of`: `chkB` at every public input from `chkB` at `default`.
* **`posCellsLt_of`**: INB's `PosCellsLt` from the Boolean `posCellsB`.
* **`inOk_congr`**: `InOk` reads no public value (`arrSk`).
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits Lvm.NS
open Lvm.VEq

/-! ## Skeletons -/

/-- A column without its closures. -/
def colSk : ColSrc → ColSrc
  | .com rec off => .com rec off
  | .fix _ _ => .fix (fun _ => 0) (fun _ => 0)

/-- A table without its fixed columns' closures. -/
def tabSk (t : Tab) : Tab := ⟨t.τ, t.cols.map colSk, t.cons, t.reads, t.seeds, t.deg⟩

theorem tabSk_pubArr (τ b s : ℕ) (v f : Bool × ℕ) (vals vals' : List FK) :
    tabSk (pubArr τ b s v f vals).tab = tabSk (pubArr τ b s v f vals').tab := rfl

theorem arrs_sk (C : QCfg) (D : QData) (P P' : Pub) :
    (arrs C D P).map (tabSk ∘ InArr.tab) = (arrs C D P').map (tabSk ∘ InArr.tab) := by
  simp only [arrs, List.map_append, List.map_cons, List.map_nil, Function.comp_apply]
  rw [tabSk_pubArr _ _ _ _ _ (hdrOfPub P) (hdrOfPub P')]

theorem lvmTabsC_sk (G : PG) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) {as as' : List InArr}
    (aux : List Tab) (h : as.map (tabSk ∘ InArr.tab) = as'.map (tabSk ∘ InArr.tab)) :
    (lvmTabsC G pl groups as aux).map tabSk = (lvmTabsC G pl groups as' aux).map tabSk := by
  simp only [lvmTabsC, List.map_append, List.map_map, h]

/-- **The tables' skeletons do not depend on the public input.** -/
theorem tabsP20_sk (P P' : Pub) : (M3.tabsP20 P).map tabSk = (M3.tabsP20 P').map tabSk :=
  lvmTabsC_sk _ _ _ _ (arrs_sk cfg20 data20 P P')

/-- `M3.tabsP20` are WP-9's tables of the node program (`nodeSound_layout`'s form; through
`M3.Q20_eq`, V-PERF's `M3.Q20 = VF.QF cfg20`). -/
theorem tabsP20_eq (P : Pub) :
    M3.tabsP20 P = lvmTabs Q20n (plOf data20) data20.groups (arrs cfg20 data20 P) (aux cfg20 data20) := by
  rw [Q20n_eq, ← M3.Q20_eq, M3.tabsP20, tabs, M3.G20_eq]
  exact lvmTabsC_eq M3.Q20 _ _ _ _

/-! ## The structural checks -/

/-- The tables' structural checks (none reads a fixed column's closures). -/
def chkB (L : Lay) (ts : List Tab) : Bool :=
  ts.all (fun t => t.reads.all fun r => decide (r.2 < t.w)) &&
  decide (nReads ts < 2 ^ 64 - 1) &&
  layOkB L ts &&
  ts.all (fun t => (t.reads.all fun r => decide (r.1.val.length ≤ 13)) &&
    t.seeds.all fun s => decide (s.1.val.length ≤ 13)) &&
  ts.all (fun t => decide (0 < t.w)) &&
  decide ((ts.map fun t => t.cons.length).sum ≤ 2 ^ 60) &&
  ts.all (fun t => !t.cons.isEmpty || !t.reads.isEmpty || !t.seeds.isEmpty)

theorem colOkB_sk (L : Lay) (τ : ℕ) (c : ColSrc) : colOkB L τ (colSk c) = colOkB L τ c := by
  cases c <;> rfl

theorem chkB_sk (L : Lay) (ts : List Tab) : chkB L (ts.map tabSk) = chkB L ts := by
  have hl : layOkB L (ts.map tabSk) = layOkB L ts := by
    unfold layOkB
    rw [List.all_map]
    refine List.all_congr rfl fun t => ?_
    simp only [Function.comp_apply, tabSk, List.all_map]
    exact List.all_congr rfl fun c => colOkB_sk L t.τ c
  have hn : nReads (ts.map tabSk) = nReads ts := by simp only [nReads, List.map_map]; rfl
  rw [chkB, chkB, hl, hn]
  simp only [List.all_map, List.map_map, Function.comp_def, tabSk, Tab.w, List.length_map]

theorem sumcheckTabs_sk (ts : List Tab) : sumcheckTabs (ts.map tabSk) = (sumcheckTabs ts).map tabSk := by
  simp only [sumcheckTabs, List.filter_map]
  rfl

theorem colsFitB_sk (p : Params) (ts : List Tab) : colsFitB p (ts.map tabSk) = colsFitB p ts := by
  unfold colsFitB
  rw [List.all_map]
  congr 1
  refine List.all_congr rfl fun t => ?_
  simp only [Function.comp_apply, tabSk, List.all_map]
  exact List.all_congr rfl fun c => by cases c <;> rfl

/-- A23: the number of `fixCols` reads only the skeletons. -/
theorem fixColsR_sk (ts : List Tab) (k : ℕ) :
    (fixColsR (ts.map tabSk) k).length = (fixColsR ts k).length := by
  unfold fixColsR
  rw [List.zipIdx_map, List.flatMap_map, List.length_flatMap, List.length_flatMap]
  refine congrArg List.sum (List.map_congr_left fun tj _ => ?_)
  obtain ⟨t, j⟩ := tj
  simp only [Prod.map, id, tabSk]
  rw [List.zipIdx_map, List.filterMap_map, List.length_filterMap_eq_countP,
    List.length_filterMap_eq_countP]
  refine List.countP_congr fun ci _ => ?_
  obtain ⟨c, i⟩ := ci
  cases c with
  | com => simp only [Function.comp_apply, Prod.map, id, colSk]
  | fix =>
    simp only [Function.comp_apply, Prod.map, id, colSk]
    by_cases h : (j == k && i == 0) = true <;>
      simp only [h, ite_true, ite_false, Option.isSome_none, Option.isSome_some, Bool.false_eq_true]

/-- A23: `PUB`'s column 0 is fixed in the skeleton iff in the table. -/
theorem col0Fix_sk (t : Tab) : col0Fix (tabSk t) = col0Fix t := by
  unfold col0Fix tabSk
  dsimp only
  rcases t.cols with _ | ⟨c, cs⟩
  · rfl
  · cases c <;> rfl

/-- **`fitsR` reads only the skeletons.** -/
theorem fitsR_sk (p : Params) (ts : List Tab) : fitsR p (ts.map tabSk) = fitsR p ts := by
  have hpl : pushLeavesR (ts.map tabSk) = pushLeavesR ts := by
    simp only [pushLeavesR, sumcheckTabs_sk, List.map_map]; rfl
  unfold fitsR
  dsimp only
  rw [hpl, sumcheckTabs_sk, colsFitB_sk, fixColsR_sk]
  simp only [List.map_map, Function.comp_def, col0Fix_sk]
  simp only [List.all_map, Function.comp_def, tabSk, Tab.w, List.length_map]
  rfl

/-! ## Consequences of `chkB` -/

section Chk

variable {L : Lay} {ts : List Tab} (h : chkB L ts = true)
include h

theorem chkB_cnt : ∀ t ∈ ts, ∀ r ∈ t.reads, r.2 < t.w := by
  simp only [chkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1

theorem chkB_len : nReads ts < 2 ^ 64 - 1 := by
  simp only [chkB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

theorem chkB_lay : LayOk L ts := by
  simp only [chkB, Bool.and_eq_true] at h
  exact layOk_of_B h.1.1.1.1.2

theorem chkB_keys : KeysOk ts := by
  simp only [chkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun t ht => h.1.1.1.2 t ht

theorem chkB_width : ∀ t ∈ ts, 0 < t.w := by
  simp only [chkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem chkB_cons : (ts.map fun t => t.cons.length).sum ≤ 2 ^ 60 := by
  simp only [chkB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem chkB_sumcheck : sumcheckTabs ts = ts := by
  simp only [chkB, Bool.and_eq_true, List.all_eq_true] at h
  exact List.filter_eq_self.mpr h.2

end Chk

/-- **The structural checks for every public input**, from the one at `default`. -/
theorem chk20_of (h : chkB lay26 (M3.tabsP20 default) = true) (P : Pub) : chkB lay26 (M3.tabsP20 P) = true := by
  rw [← chkB_sk, tabsP20_sk P default, chkB_sk]
  exact h

/-- **`MidHyp.fit` from one decision at `default`.** -/
theorem fit20_of (h : fitsR P20 (M3.tabsP20 default) = true) (P : Pub) : fitsR P20 (M3.tabsP20 P) = true := by
  rw [← fitsR_sk, tabsP20_sk P default, fitsR_sk]
  exact h

/-! ## The position classes' cells (INB's `PosCellsLt`) -/

/-- Every answer lane lies in the hashed stream (entries past the plan read its end). -/
theorem ansLane_le {p : Params} (hS : StreamOk p) (i : ℕ) : ansLane p i ≤ hashedLen p / 8 + 1 := by
  unfold ansLane
  split
  · have := hashedLen_ge hS; omega
  · rcases Nat.lt_or_ge i (plan p).length with hi | hi
    · have := lanes_in hS (by omega) hi; omega
    · rw [List.getD_eq_default _ _ hi]
      have e : eLane p i = hashedLen p / 8 := by
        unfold eLane bOff
        rw [List.take_of_length_le (by simpa [lens] using hi), hS.2]
      rw [e]
      show _ + 1 + 0 / 8 ≤ _
      omega

/-- `PosCellsLt`'s output-cell bounds below `N`, as a Boolean (the word cells by `ansLane_le`). -/
def posCellsB (C : QCfg) (N : ℕ) : Bool :=
  (List.range (opens C.p).length).all fun k =>
    let o := (opens C.p).getD k default
    decide (nLanes o.L.height ≤ 4) &&
    (List.range (nLanes o.L.height)).all fun l =>
      (List.range (nRows o)).all fun x =>
        (List.range (laneOuts o.L.height l).length).all fun jo =>
          decide (posCell C k o x ((laneOuts o.L.height l).getD jo (.bit 0, 0, 0)) < N)

theorem posCellsLt_of {Q : Program} {C : QCfg} {N : ℕ} (h : posCellsB C N = true) (hS : StreamOk C.p)
    (hL : hashedLen C.p / 8 + 5 ≤ N) (hN : N ≤ Q.cells .K) : PosCellsLt Q C := by
  intro k hk l hl x hx
  simp only [posCellsB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h4, h2⟩ := h k hk
  have ha := ansLane_le hS (((opens C.p).getD k default).pe + x)
  exact ⟨by omega, fun jo hjo => by have := h2 l hl x hx jo hjo; omega⟩

/-! ## The input arrays' check, for every public input -/

/-- An input array without its public values' closures. -/
def arrSk (a : InArr) : InArr :=
  ⟨a.ty, a.τ, a.base, a.stride, a.val, a.fin, a.pub.map fun _ => (fun _ => 0, fun _ => 0)⟩

theorem arrs_arrSk (C : QCfg) (D : QData) (P P' : Pub) :
    (arrs C D P).map arrSk = (arrs C D P').map arrSk := by
  simp only [arrs, List.map_append, List.map_cons, List.map_nil]
  rw [show arrSk (pubArr 10 (pbB C) 1 (false, 0) (fin D 43) (hdrOfPub P)) =
    arrSk (pubArr 10 (pbB C) 1 (false, 0) (fin D 43) (hdrOfPub P')) from rfl]

theorem arrSk_fields {a a' : InArr} (he : arrSk a = arrSk a') :
    a.ty = a'.ty ∧ a.τ = a'.τ ∧ a.base = a'.base ∧ a.stride = a'.stride ∧ a.val = a'.val := by
  simp only [arrSk, InArr.mk.injEq] at he
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1⟩

/-- **`InOk` reads no public value.** -/
theorem inOk_congr {Q : Program} {as as' : List InArr} (h : as.map arrSk = as'.map arrSk)
    (H : InOk Q as) : InOk Q as' := by
  have hlen : as.length = as'.length := by simpa using congrArg List.length h
  have hget : ∀ i (hi : i < as.length) (hi' : i < as'.length), arrSk as[i] = arrSk as'[i] := by
    intro i hi hi'
    have := congrArg (fun l => l[i]?) h
    simpa [List.getElem?_map, hi, hi'] using this
  have hmem : ∀ {l l' : List InArr}, l.map arrSk = l'.map arrSk → ∀ a' ∈ l', ∃ a ∈ l, arrSk a = arrSk a' :=
    fun {l l'} h a' ha' => by
      have : arrSk a' ∈ l.map arrSk := h ▸ List.mem_map_of_mem ha'
      obtain ⟨a, ha, he⟩ := List.mem_map.mp this
      exact ⟨a, ha, he⟩
  refine ⟨fun a' ha' => ?_, fun a' ha' x hx => ?_, fun i i' x x' hx hx' hty heq => ?_, fun τ e he => ?_⟩
  · obtain ⟨a, ha, he⟩ := hmem h a' ha'
    obtain ⟨h1, -, -, -, h5⟩ := arrSk_fields he
    rw [← h1, ← h5]; exact H.limbs a ha
  · obtain ⟨a, ha, he⟩ := hmem h a' ha'
    obtain ⟨h1, h2, h3, h4, -⟩ := arrSk_fields he
    rw [← h2] at hx; rw [← h1, ← h3, ← h4]; exact H.lt a ha x hx
  · simp only [List.get_eq_getElem] at hx hx' hty heq
    obtain ⟨a1, a2, a3, a4, -⟩ := arrSk_fields (hget i.1 (by omega) i.2)
    obtain ⟨b1, b2, b3, b4, -⟩ := arrSk_fields (hget i'.1 (by omega) i'.2)
    have := H.inj ⟨i.1, by omega⟩ ⟨i'.1, by omega⟩ x x'
      (by simp only [List.get_eq_getElem]; rw [a2]; exact hx)
      (by simp only [List.get_eq_getElem]; rw [b2]; exact hx')
      (by simp only [List.get_eq_getElem]; rw [a1, b1]; exact hty)
      (by simp only [List.get_eq_getElem]; rw [a3, a4, b3, b4]; exact heq)
    exact ⟨Fin.ext (by simpa using congrArg Fin.val this.1), this.2⟩
  · obtain ⟨a, ha, hτ, x, hx, hc⟩ := H.cover τ e he
    obtain ⟨a', ha', he'⟩ := hmem h.symm a ha
    obtain ⟨h1, h2, h3, h4, -⟩ := arrSk_fields he'
    exact ⟨a', ha', by rw [h1]; exact hτ, x, by rw [h2]; exact hx, by rw [h3, h4]; exact hc⟩

/-! ## The arrays -/

theorem mem_arrs_qlt (P : Pub) :
    pubArr cfg20.aQT (qtB cfg20) 1 (false, 0) (fin data20 44) (qltData cfg20.p (lay cfg20)) ∈
      arrs cfg20 data20 P :=
  List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Every input array is committed or a `pubArr` (`PubOk`'s premise). -/
theorem arrs_pub (C : QCfg) (D : QData) (P : Pub) : ∀ a ∈ arrs C D P, a.pub = none ∨
    ∃ τ base stride val fin vals, a = pubArr τ base stride val fin vals := by
  intro a ha
  simp only [arrs, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with ((((⟨l, -, rfl⟩ | rfl) | ⟨l, -, rfl⟩) | ⟨l, -, rfl⟩) | ⟨l, -, rfl⟩) | rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, _, _, _, _, rfl⟩

end Lvm.QAsm
