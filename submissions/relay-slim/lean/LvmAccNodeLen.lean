-- New for lvm (AC-N, A23): the folded accumulator V_S computes has `accVars` coordinates on every
-- stream (for tables fitting P20), so Q_arith's `accOutOf Σ' = acc_in` (`harith`) reduces to
-- coordinate-wise equalities (`acc_eq_of`), which is what Q_acc's cells give (review of AC-N).
import LvmVEqTop

/-!
# The folded accumulator's length

* **`acc_eq_of`**: two accumulators with `accVars` coordinates are equal when every coordinate and
  the value are;
* `valP_sumcheck`, `valP_samples`, `valP_tableSumcheckPt`, `length_tablePoint`: native value facts
  (`ValP`): the table sumcheck's point has `tableRounds` coordinates, the tables' points are its
  prefixes, so `tablePoint` has `min rounds (max τ)` of them;
* **`length_accOutOf`**: `(accOutOf P20 (M3.real P20 tabs) vk c Σ).pt.length = accVars` when every
  `tabs pub` fits `P20`; **`accOutOf_eq_of`**: `harith`'s `accOutOf Σ' = (pubX x).accIn` from
  coordinate-wise equalities (with `LvmAccNodePub.accIn_pt_lanes`/`accIn_y_lanes` on the `PUB` cells).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM

/-! ## Accumulators -/

/-- **Accumulators are equal coordinate-wise** (both of `accVars` coordinates). -/
theorem acc_eq_of {a b : Acc} (ha : a.pt.length = accVars) (hb : b.pt.length = accVars)
    (hpt : ∀ i < accVars, a.pt.getD i 0 = b.pt.getD i 0) (hy : a.y = b.y) : a = b := by
  obtain ⟨pa, ya⟩ := a
  obtain ⟨pb, yb⟩ := b
  simp only at ha hb hpt hy
  subst hy
  congr
  refine List.ext_getElem (by rw [ha, hb]) fun i h1 h2 ↦ ?_
  have := hpt i (by omega)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-! ## Native value facts -/

theorem valP_samples : ∀ n, ValP (DM.samples n) fun l ↦ l.length = n
  | 0 => ValP.pure rfl
  | n + 1 => ValP.any fun _ ↦ (valP_samples n).bind fun _ h ↦ ValP.pure (by simp [h])

theorem valP_sumcheck (count : ℕ) : ∀ (eqs : List (Option FE)) (claim : FE),
    ValP (Lvm.sumcheck claim count eqs) fun r ↦ r.1.length = eqs.length
  | [], _ => ValP.pure rfl
  | _ :: eqs, _ => ValP.any fun _ ↦ ValP.any fun _ ↦ (valP_sumcheck count eqs _).bind fun r h ↦ by
      obtain ⟨pt, fin⟩ := r
      exact ValP.pure (by simpa using h)

/-- The rows' points of `tableTerms` are prefixes of `point`, one per row, of the rows' heights. -/
theorem valP_tableTermsPt (cp fp point : List FE) :
    ∀ (rows : List (TableSpec × List Lvm.Form × FE)) (cursor : ℕ) (final : FE),
      ValP (Lvm.tableTerms cp fp point rows cursor final) fun x ↦
        x.2.map (·.1) = rows.map fun r ↦ point.take r.1.logHeight
  | [], _, _ => ValP.pure rfl
  | (t, fs, w) :: rows, cursor, final => by
    unfold Lvm.tableTerms
    refine ValP.any fun ev ↦ (valP_tableTermsPt cp fp point rows _ _).bind fun x hx ↦ ?_
    obtain ⟨f, rs⟩ := x
    exact ValP.pure (by simpa using hx)

theorem length_lstep {β : Type} (r p : List β) : (lstep r p).length = max r.length p.length := by
  unfold lstep; split_ifs <;> omega

/-- The longest-so-far fold's length is the largest length. -/
theorem length_foldl_lstep {β : Type} : ∀ (l : List (List β)) (r : List β),
    (l.foldl lstep r).length = (l.map List.length).foldl max r.length
  | [], _ => rfl
  | p :: l, r => by rw [List.foldl_cons, length_foldl_lstep l, length_lstep]; rfl

theorem foldl_max_min (c : ℕ) : ∀ (l : List ℕ) (a : ℕ),
    (l.map (min c)).foldl max (min c a) = min c (l.foldl max a)
  | [], _ => rfl
  | x :: l, a => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, show max (min c a) (min c x) = min c (max a x) by omega,
      foldl_max_min c l]

/-- **The table point of the native table sumcheck** has `min rounds (max τ)` coordinates. -/
theorem valP_tablePoint (rounds : ℕ) (tables : List TableSpec) (fs : List (List Lvm.Form))
    (cp fp eqp : List FE) (target : FE) (hfs : tables.length ≤ fs.length) :
    ValP (Lvm.tableSumcheck rounds tables fs cp fp eqp target) fun evs ↦
      (tablePoint evs).length = min rounds ((tables.map (·.logHeight)).foldl max 0) := by
  unfold Lvm.tableSumcheck
  refine (valP_sumcheck 4 _ _).bind fun x hx ↦ ?_
  obtain ⟨ch, claim⟩ := x
  simp only [List.length_replicate] at hx
  refine (valP_tableTermsPt _ _ _ _ _ _).bind fun y hy ↦ ?_
  obtain ⟨fin, evs⟩ := y
  refine ValP.any fun _ ↦ ValP.pure ?_
  simp only at hy
  have hrows : (List.zip tables (List.zip fs (Lvm.tableWeights (tables.map (·.logHeight)) eqp
      ch.reverse))).map (fun r ↦ r.1) = tables := by
    rw [List.map_fst_zip]
    simp [length_tableWeightsN]; omega
  unfold tablePoint
  rw [show evs.foldl (fun r e ↦ if r.length < e.1.length then e.1 else r) [] =
      (evs.map (·.1)).foldl lstep [] by rw [List.foldl_map]; rfl, length_foldl_lstep, hy,
    List.map_map]
  have e : ((List.zip tables (List.zip fs (Lvm.tableWeights (tables.map (·.logHeight)) eqp
      ch.reverse))).map (List.length ∘ fun r ↦ ch.reverse.take r.1.logHeight)) =
      (tables.map (·.logHeight)).map (min rounds) := by
    have e1 : ((List.zip tables (List.zip fs (Lvm.tableWeights (tables.map (·.logHeight)) eqp
        ch.reverse))).map (List.length ∘ fun r ↦ ch.reverse.take r.1.logHeight)) =
        ((List.zip tables (List.zip fs (Lvm.tableWeights (tables.map (·.logHeight)) eqp
          ch.reverse))).map (fun r ↦ r.1)).map (fun t ↦ min rounds t.logHeight) := by
      rw [List.map_map]
      exact List.map_congr_left fun r _ ↦ by simp [hx, Nat.min_comm]
    rw [e1, hrows, List.map_map]
    rfl
  rw [e, show (List.length ([] : List FE)) = min rounds 0 by simp, foldl_max_min]

theorem valP_dTabPt (tabs : Pub → List M3.Tab) (pub : Pub) (F : Fit P20 (tabs pub)) (pb : List FE × BusOut)
    (hpb : pb.2.forms.length = (M3.sumcheckTabs (tabs pub)).length) :
    ValP (dTab P20 (M3.real P20 tabs) pub pb.1 pb.2) fun ev ↦ (tablePoint ev).length = P20.tableRounds := by
  unfold dTab
  refine ValP.any fun _ ↦ ?_
  have h := valP_tablePoint P20.tableRounds ((M3.real P20 tabs).tables pub) pb.2.forms
  simp only [real_tables, List.length_map] at h ⊢
  have hr := F.rounds
  have e : ((M3.sumcheckTabs (tabs pub)).map Lvm.M3.nativeTable).map (·.logHeight) =
      (M3.sumcheckTabs (tabs pub)).map (·.τ) := by rw [List.map_map]; rfl
  rw [e, ← hr, Nat.min_self] at h
  exact h _ _ _ _ (by rw [hpb])

theorem valP_accFold (m : M3) (pub : Pub) (evs : List (List FE × List FE))
    (hbt : (tablePoint evs).length = P20.tableRounds) (hpub : pub.accIn.pt.length = accVars)
    (hr : P20.tableRounds ≤ accVars) :
    ValP (accFold P20 m pub evs) fun a ↦ a.pt.length = accVars := by
  unfold accFold
  refine ValP.any fun _ ↦ (valP_samples _).bind fun κ hκ ↦ ValP.any fun _ ↦ ValP.any fun _ ↦
    ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.pure ?_
  simp only [length_accLine, List.length_append, hbt, hκ, hpub, Params.accLog]
  omega

theorem valP_dBusTabAcc (tabs : Pub → List M3.Tab) (pub : Pub) (F : Fit P20 (tabs pub))
    (hpub : pub.accIn.pt.length = accVars) :
    ValP (dBusTab P20 (M3.real P20 tabs) pub) fun bta ↦ bta.2.pt.length = accVars := by
  unfold dBusTab
  refine ValP.bind (P := fun (bt : (List FE × BusOut) × List (List FE × List FE)) ↦
    (tablePoint bt.2).length = P20.tableRounds) ?_ ?_
  · exact (valP_dBus P20 tabs pub).bind fun pb hpb ↦
      (valP_dTabPt tabs pub F pb hpb).bind fun ev hev ↦ ValP.pure hev
  · intro bt hbt
    exact (valP_accFold (M3.real P20 tabs) pub bt.2 hbt hpub F.accRounds).bind fun acc h ↦ ValP.pure h

theorem length_pubOf_accIn (vk c : RecursionFast.Digest) (sig : ByteArray) :
    (pubOf vk c sig).accIn.pt.length = accVars := by
  simp [pubOf]

/-- `accOutOf` is the run's value from the start. -/
theorem accOutOf_eq (p : Params) (m : M3) (vk c : RecursionFast.Digest) (sig : ByteArray) :
    accOutOf p m vk c sig = (runD (decideProg p m vk c) sig RS.start).1 := by
  unfold accOutOf DM.runOn
  have e : (decideProg p m vk c sig).run RS.start = runD (decideProg p m vk c) sig RS.start := rfl
  rw [e]

/-- **The folded accumulator has `accVars` coordinates** on every stream, for tables fitting
`P20`. -/
theorem length_accOutOf (tabs : Pub → List M3.Tab) (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (vk c : RecursionFast.Digest) (sig : ByteArray) :
    (accOutOf P20 (M3.real P20 tabs) vk c sig).pt.length = accVars := by
  have hv : ValP (decideProg P20 (M3.real P20 tabs) vk c) fun a ↦ a.pt.length = accVars := by
    rw [decideProg_dTop]
    unfold dTop
    refine ValP.any fun sig' ↦ ValP.any fun _ ↦ ValP.any fun _ ↦ ?_
    unfold dMid
    refine ValP.bind (P := fun (r : List (Com × BlockClaim) × Acc) ↦ r.2.pt.length = accVars) ?_
      fun r hr ↦ ValP.any fun _ ↦ ValP.pure hr
    exact (valP_dBusTabAcc tabs _ (fit_of P20 _ (hfit (pubOf vk c sig'))) (length_pubOf_accIn vk c sig')).bind
      fun bta h ↦ ValP.any fun _ ↦ ValP.pure h
  rw [accOutOf_eq]
  exact hv sig RS.start

/-- **`harith`'s accumulator half, coordinate-wise** (what Q_acc's cells give): the folded
accumulator of the child's stream is the statement's `acc_in` when every coordinate and the value
agree. -/
theorem accOutOf_eq_of (tabs : Pub → List M3.Tab) (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (vk c : RecursionFast.Digest) (sig : ByteArray) (x : List UInt8)
    (hpt : ∀ i < accVars, (accOutOf P20 (M3.real P20 tabs) vk c sig).pt.getD i 0 = (pubX x).accIn.pt.getD i 0)
    (hy : (accOutOf P20 (M3.real P20 tabs) vk c sig).y = (pubX x).accIn.y) :
    accOutOf P20 (M3.real P20 tabs) vk c sig = (pubX x).accIn :=
  acc_eq_of (length_accOutOf tabs hfit vk c sig) (length_pubOf_accIn _ _ _) hpt hy

end Lvm.VEq
