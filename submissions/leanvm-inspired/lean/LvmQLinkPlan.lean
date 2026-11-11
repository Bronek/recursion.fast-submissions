-- New for lvm (WP-11b-QL): the openings of the plan, and the lanes of their entries.
import LvmQLinkBridge

/-!
# The openings of the plan

`opens p` lists the schedule's openings (`OpenInfo`: first entry, level, positions entry, cap
entry and offset), by the same walk as the plan. `open_of_entry`: every leaf or node entry of the
plan lies in an opening, as the corresponding entry of its `openPlan`; `openPlan_getD` reads that
entry; `eLane_open`: inside an opening the lanes are affine in the position and the level.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay

/-- An opening of the plan. -/
structure OpenInfo where
  /-- Its first entry. -/
  i0 : Nat
  /-- Its level. -/
  L : Level
  /-- The first positions entry. -/
  pe : Nat
  /-- The cap's entry. -/
  ce : Nat
  /-- The cap's byte offset in that entry's query. -/
  co : Nat
  deriving Repr, Inhabited

/-- The opening an item makes (the walk's `planItem`). -/
def openItem (p : Params) (w : WS) : Item → List OpenInfo
  | .opening r =>
    match w.caps.find? (·.1 == r) with
    | none => []
    | some (_, ce, co, _) => [⟨w.i, p.level r, w.pe, ce, co⟩]
  | _ => []

/-- The openings of a list of items. -/
def openItems (p : Params) : WS → List Item → List OpenInfo
  | _, [] => []
  | w, it :: its => openItem p w it ++ openItems p (planItem p w it).2 its

/-- **The openings of the plan.** -/
def opens (p : Params) : List OpenInfo := openItems p w0 (schedule p)

/-- An entry is a leaf or a node. -/
def _root_.Lvm.Replay.EK.isOpen : EK → Bool
  | .leaf => true
  | .node .. => true
  | _ => false

theorem planItem_open (p : Params) (w : WS) (it : Item) {x : Nat} (hx : x < (planItem p w it).1.length)
    (he : ((planItem p w it).1.getD x default).k.isOpen = true) :
    ∃ o ∈ openItem p w it, o.i0 = w.i ∧ (planItem p w it).1 = openPlan o.L o.pe o.ce o.co := by
  cases it with
  | read m => simp [planItem] at hx
  | cap c r => simp [planItem] at hx
  | sample =>
    simp only [planItem, List.length_singleton, Nat.lt_one_iff] at hx
    subst hx; simp [planItem, EK.isOpen] at he
  | positions r =>
    simp only [planItem, List.length_map, List.length_range] at hx
    simp only [planItem, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx,
      Option.map_some, Option.getD_some] at he
    split_ifs at he <;> simp [EK.isOpen] at he
  | opening r =>
    rcases hf : w.caps.find? (·.1 == r) with _ | ⟨r', ce, co, nb⟩
    · simp [planItem, hf] at hx
    · refine ⟨⟨w.i, p.level r, w.pe, ce, co⟩, by simp [openItem, hf], rfl, by simp [planItem, hf]⟩

theorem openItems_open (p : Params) : ∀ (its : List Item) (w : WS) {x : Nat},
    x < (planItems p w its).1.length → ((planItems p w its).1.getD x default).k.isOpen = true →
    ∃ o ∈ openItems p w its, o.i0 ≤ w.i + x ∧ w.i + x < o.i0 + (openPlan o.L o.pe o.ce o.co).length ∧
      (planItems p w its).1.getD x default = (openPlan o.L o.pe o.ce o.co).getD (w.i + x - o.i0) default
  | [], _, _, hx, _ => by simp [planItems] at hx
  | it :: its, w, x, hx, he => by
    simp only [planItems, List.length_append] at hx he ⊢
    by_cases h1 : x < (planItem p w it).1.length
    · rw [List.getD_append _ _ _ _ h1] at he ⊢
      obtain ⟨o, ho, hi, hp⟩ := planItem_open p w it h1 he
      refine ⟨o, by simp [openItems, ho], by omega, by rw [← hp, hi]; omega, ?_⟩
      rw [hi, show w.i + x - w.i = x by omega, hp]
    · rw [List.getD_append_right _ _ _ _ (by omega)] at he ⊢
      obtain ⟨o, ho, h2, h3, h4⟩ := openItems_open p its (planItem p w it).2 (x := x - (planItem p w it).1.length)
        (by omega) he
      rw [planItem_i] at h2 h3 h4
      refine ⟨o, by simp [openItems, ho], by omega, by omega, ?_⟩
      rw [h4]; congr 1; omega

/-- **Every leaf or node entry lies in an opening.** -/
theorem open_of_entry (p : Params) {i : Nat} (hi : i < (plan p).length)
    (he : ((plan p).getD i default).k.isOpen = true) :
    ∃ o ∈ opens p, o.i0 ≤ i ∧ i < o.i0 + (openPlan o.L o.pe o.ce o.co).length ∧
      (plan p).getD i default = (openPlan o.L o.pe o.ce o.co).getD (i - o.i0) default := by
  have h2 : 2 ≤ i := by
    rcases i with _ | _ | i
    · rw [plan_zero] at he; simp [EK.isOpen] at he
    · rw [plan_one] at he; simp [EK.isOpen] at he
    · omega
  have hpl : (plan p).getD i default = (planAll p).1.getD (i - 2) default := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    simp [plan, List.getD_eq_getElem?_getD]
  rw [hpl] at he ⊢
  have := openItems_open p (schedule p) w0 (x := i - 2) (by rw [plan_length] at hi; simp [planAll] at hi ⊢; omega) he
  simp only [w0] at this
  rw [show 2 + (i - 2) = i by omega] at this
  exact this

/-! ## Inside an opening -/

theorem openPlan_length (L : Level) (pe ce co : Nat) :
    (openPlan L pe ce co).length = L.t * (1 + L.path) := by
  simp [openPlan, List.length_flatMap]; left; ring

/-- The entry at position `j`, slot `y` (`0` the leaf, `1 + lvl` the nodes) of an opening. -/
theorem openPlan_getD (L : Level) (pe ce co : Nat) {j y : Nat} (hj : j < L.t) (hy : y < 1 + L.path) :
    (openPlan L pe ce co).getD (j * (1 + L.path) + y) default =
      if y = 0 then ⟨.leaf, L.row⟩
      else ⟨.node pe L.height j (y - 1) (if y = L.path then some (ce, co, L.path) else none), 64⟩ := by
  suffices h : ∀ (n k : Nat) (j : Nat), j < n →
      ((List.range' k n).flatMap fun j => (⟨.leaf, L.row⟩ : PE) :: (List.range L.path).map fun lvl =>
        ⟨.node pe L.height j lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩).getD
          (j * (1 + L.path) + y) default =
      if y = 0 then ⟨.leaf, L.row⟩
      else ⟨.node pe L.height (k + j) (y - 1) (if y = L.path then some (ce, co, L.path) else none), 64⟩ by
    simpa [openPlan, List.range_eq_range'] using h L.t 0 j hj
  intro n
  induction n with
  | zero => intro k j hj; omega
  | succ n ih =>
    intro k j hj
    rw [List.range'_succ, List.flatMap_cons]
    rcases j with _ | j
    · simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      rcases y with _ | y
      · simp
      · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp [Nat.add_one_inj]
    · rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
      have := ih (k + 1) j (by omega)
      rw [show k + (j + 1) = k + 1 + j by omega]
      rw [← this]
      congr 1
      simp only [Nat.succ_mul, List.length_cons, List.length_map, List.length_range]
      ring_nf; omega

theorem openItems_al (p : Params) {P : List PE} : ∀ (its : List Item) (w : WS),
    Al P w.i (planItems p w its).1 → ∀ o ∈ openItems p w its, Al P o.i0 (openPlan o.L o.pe o.ce o.co)
  | [], _, _, o, ho => by simp [openItems] at ho
  | it :: its, w, hal, o, ho => by
    obtain ⟨h1, h2⟩ := Al_planItems p hal
    simp only [openItems, List.mem_append] at ho
    rcases ho with ho | ho
    · cases it with
      | opening r =>
        rcases hf : w.caps.find? (·.1 == r) with _ | ⟨r', ce, co, nb⟩
        · simp [openItem, hf] at ho
        · simp only [openItem, hf, List.mem_singleton] at ho
          subst ho
          simpa [planItem, hf] using h1
      | _ => simp [openItem] at ho
    · exact openItems_al p its _ h2 o ho

/-- Every opening sits in the plan at its first entry. -/
theorem opens_al (p : Params) {o : OpenInfo} (ho : o ∈ opens p) : Al (plan p) o.i0 (openPlan o.L o.pe o.ce o.co) := by
  refine openItems_al p (schedule p) w0 ⟨by simp [w0, plan_length, planAll], fun x hx => ?_⟩ o ho
  show (plan p).getD (2 + x) default = _
  simp only [plan, planAll, List.getD_eq_getElem?_getD]
  rw [show 2 + x = x + 1 + 1 by omega]
  simp

theorem opens_i0 (p : Params) {o : OpenInfo} (ho : o ∈ opens p) : 2 ≤ o.i0 := by
  suffices h : ∀ (its : List Item) (w : WS), 2 ≤ w.i → ∀ o ∈ openItems p w its, 2 ≤ o.i0 from
    h _ _ (by simp [w0]) o ho
  intro its
  induction its with
  | nil => intro w _ o ho; simp [openItems] at ho
  | cons it its ih =>
    intro w hw o ho
    simp only [openItems, List.mem_append] at ho
    rcases ho with ho | ho
    · cases it with
      | opening r =>
        rcases hf : w.caps.find? (·.1 == r) with _ | ⟨r', ce, co, nb⟩
        · simp [openItem, hf] at ho
        · simp only [openItem, hf, List.mem_singleton] at ho; subst ho; exact hw
      | _ => simp [openItem] at ho
    · exact ih _ (by rw [planItem_i]; omega) o ho

/-- The lane offset of slot `y` (`0` the leaf, `1 + lvl` the nodes) from its position's leaf. -/
def slotOff (L : Level) (y : Nat) : Nat := if y = 0 then 0 else 5 + L.row / 8 + 13 * (y - 1)

/-- The lanes of one position of an opening. -/
def posStride (L : Level) : Nat := 5 + L.row / 8 + 13 * L.path

/-- **The lanes inside an opening are affine.** -/
theorem eLane_open {p : Params} (hS : StreamOk p) {o : OpenInfo} (ho : o ∈ opens p) {j y : Nat}
    (hj : j < o.L.t) (hy : y ≤ o.L.path) :
    eLane p (o.i0 + j * (1 + o.L.path) + y) = eLane p o.i0 + j * posStride o.L + slotOff o.L y := by
  have hal := opens_al p ho
  have h2 := opens_i0 p ho
  have hlen := hal.1
  rw [openPlan_length] at hlen
  have entry : ∀ j' < o.L.t, ∀ y' < 1 + o.L.path, ((plan p).getD (o.i0 + j' * (1 + o.L.path) + y') default).len =
      if y' = 0 then o.L.row else 64 := by
    intro j' hj' y' hy'
    rw [Nat.add_assoc, hal.2 _ (by rw [openPlan_length]; nlinarith), openPlan_getD _ _ _ _ hj' hy']
    split <;> rfl
  have hrow8 : o.L.row % 8 = 0 := by
    have := streamOk_len hS.1 (i := o.i0) (by omega) (by nlinarith)
    have e := entry 0 (by omega) 0 (by omega)
    simp only [Nat.zero_mul, Nat.add_zero, ite_true] at e
    rw [e] at this; exact this
  -- within a position
  have within : ∀ j' < o.L.t, ∀ y' ≤ o.L.path, eLane p (o.i0 + j' * (1 + o.L.path) + y') =
      eLane p (o.i0 + j' * (1 + o.L.path)) + slotOff o.L y' := by
    intro j' hj' y'
    induction y' with
    | zero => intro _; simp [slotOff]
    | succ y' ih =>
      intro hy'
      rw [← Nat.add_assoc, eLane_succ hS.1 (by omega) (by nlinarith), ih (by omega), entry j' hj' y' (by omega)]
      simp only [slotOff, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      split
      · next h => subst h; simp; omega
      · next h => omega
  have leaf : ∀ j' < o.L.t, eLane p (o.i0 + j' * (1 + o.L.path)) = eLane p o.i0 + j' * posStride o.L := by
    intro j'
    induction j' with
    | zero => intro _; simp
    | succ j' ih =>
      intro hj'
      have hstep : o.i0 + (j' + 1) * (1 + o.L.path) = o.i0 + j' * (1 + o.L.path) + o.L.path + 1 := by ring
      rw [hstep, eLane_succ hS.1 (by omega) (by nlinarith), within j' (by omega) o.L.path le_rfl,
        ih (by omega), entry j' (by omega) o.L.path (by omega)]
      simp only [slotOff, posStride]
      split
      · next h => rw [h]; ring_nf
      · next h =>
        have : 13 * o.L.path = 13 * (o.L.path - 1) + 13 := by omega
        rw [Nat.add_mul, this]; ring_nf
  rw [within j hj y hy, leaf j hj]

end Lvm.QLink
