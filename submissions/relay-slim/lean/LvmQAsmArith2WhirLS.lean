-- New for lvm (HAR-WH): the soundness of one stacked opening's levels: the circuit's `levelsG`
-- replays `F`'s `whirLevels` (`levels_run`), level by level (`lvPre_spec`, `whirLevels_step`,
-- `whirLevels_final`).
import LvmQAsmArith2WhirGS
import LvmQAsmArith2WhirF
import LvmQAsmArith2WhirL

/-!
# The levels of a stacked opening replay `F`'s `whirLevels`

* `lvPre_spec`: one level's prefix gadget (`lvPre`) computes `F`'s running quadratic after the
  glue, `λ`, and the level's column weight `inducedWeight κ qs (powers λ t) (point.drop F_i)`.
* **`levels_run`**: wherever `levelsG` holds and asserts (gate on), `F`'s `whirLevels` from any
  state at position `8V` keeps `ok`, ends at `8 · stackEndL`, `msg = 0`. Invariants: `ChOk` (the
  challenge cells hold `F`'s challenges), `PosOk` (the position cells hold `F`'s positions), `GlOk`
  (the glued claims are the `(λ, W)` cells), the folds so far are a prefix of the point.
-/

set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build DM
variable {c : Ctx} {M : Mem}


theorem okb {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr} (h : Lvm.QSig.Ok c M (m >>= f) p) :
    Lvm.QSig.Ok c M m p ∧ Lvm.QSig.Ok c M (f (m p).1) (p.adv (m p).2) := by
  obtain ⟨h1, h2⟩ := h
  rw [hold_bind] at h1; rw [assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

theorem val_E {x : Cell} (hx : x.ty = .E) : x.val M = M.e x.n := by
  obtain ⟨ty, n⟩ := x; cases hx; rfl

theorem ptv_getD (pc ν n k : Nat) (h : n + k < ν) :
    ((ptv M pc ν).drop n).getD k 0 = M.e (pc + n + k) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ptv, List.getElem?_map,
    List.getElem?_range h, Option.map_some, Option.getD_some, Nat.add_assoc]

theorem ptv_length (pc ν : Nat) : (ptv M pc ν).length = ν := by simp [ptv]

theorem frC_getD (sig : ByteArray) (P n j : Nat) (h : j < n) :
    (frC sig P n).getD j 0 = feAt sig (P + 120 * j + 40) := by
  rw [frC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl

theorem dot_map_range (lam : FE) (t : Nat) (φ : Nat → FE) :
    Lvm.dot (powers lam t) ((List.range t).map φ) = ∑ q ∈ Finset.range t, lam ^ q * φ q := by
  have := dot_powers lam ((List.range t).map φ)
  simp only [List.length_map, List.length_range] at this
  rw [this]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp hq)]
  rfl

theorem lvLanes_facts (g : Nat) (ood : Bool) (L : Level) (nxt : Option Level) (V : Nat) :
    (lvLanes g ood L nxt V).V1 = V + 15 * L.fold ∧ (lvLanes g ood L nxt V).V1 ≤ (lvLanes g ood L nxt V).Vc ∧
    (lvLanes g ood L nxt V).V2 ≤ (lvLanes g ood L nxt V).V3 ∧ (lvLanes g ood L nxt V).V4 = (lvLanes g ood L nxt V).V3 + 9 ∧
    (lvLanes g ood L nxt V).V5 = (lvLanes g ood L nxt V).V4 + oStr L * L.t ∧
    (lvLanes g ood L nxt V).V6 = (lvLanes g ood L nxt V).V5 + 6 ∧
    (lvLanes g ood L nxt V).Vc ≤ (lvLanes g ood L nxt V).Vo ∧
    (lvLanes g ood L nxt V).Vo = (if ood && nxt.isSome then (lvLanes g ood L nxt V).Vc + 9 * L.kappa + 9
      else (lvLanes g ood L nxt V).Vc) ∧
    (lvLanes g ood L nxt V).V2 = (if g = 0 then (lvLanes g ood L nxt V).Vo else (lvLanes g ood L nxt V).Vo + 21) ∧
    (lvLanes g ood L nxt V).Vo ≤ (lvLanes g ood L nxt V).V2 := by
  cases nxt <;> cases ood <;> by_cases hg : g = 0 <;> simp [lvLanes, hg] <;> omega

/-! ## The OOD weight and the PoW check -/

theorem eqZG_spec {zc : Cell} : ∀ (ab : List (Cell × Cell)) (acc : Cell) (p : Ptr),
    SegsHold c M p (eqZG zc ab acc p).2 → zc.val M = 0 →
    (eqZG zc ab acc p).1.val M = acc.val M * (ab.map fun x => 1 + x.1.val M + x.2.val M).prod
  | [], acc, p, _, _ => by simp [eqZG, pure_apply]
  | (a, b) :: ab, acc, p, h, hz => by
    simp only [eqZG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    obtain ⟨h1, h⟩ := h
    rw [segsHold_append] at h
    obtain ⟨h2, h⟩ := h
    rw [eqZG_spec ab _ _ h hz, mulAdd_spec h2, lin_spec h1, hz, ofK_one, one_mul, add_zero]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem eqEval_range (κ : Nat) (zf xf : Nat → FE) :
    eqEval ((List.range κ).map zf) ((List.range κ).map xf) =
      ((List.range κ).map fun j => 1 + zf j + xf j).prod := by
  rw [eqEval, List.zipWith_map, List.zipWith_self, ← List.prod_eq_foldl]

theorem eqZG_range {zc acc : Cell} {κ : Nat} {cz cx : Nat → Cell} {p : Ptr}
    (h : SegsHold c M p (eqZG zc ((List.range κ).map fun j => (cz j, cx j)) acc p).2) (hz : zc.val M = 0)
    (hacc : acc.val M = 1) :
    (eqZG zc ((List.range κ).map fun j => (cz j, cx j)) acc p).1.val M =
      eqEval ((List.range κ).map fun j => (cz j).val M) ((List.range κ).map fun j => (cx j).val M) := by
  rw [eqZG_spec _ _ _ h hz, hacc, one_mul, eqEval_range, List.map_map]
  rfl

/-- **The PoW check from the lane bound** (PI-GRIND): lane 2 of the answer below `2^(64−g)` makes
`eToNat c < 2^(192−g)`. -/
theorem powOKR_of {g : Nat} (hg : g ≤ 64) (sig : ByteArray) (o : Nat)
    (h : (kAt sig (o + 16)).val.toNat < 2 ^ (64 - g)) : powOKR g (feAt sig o) = true := by
  unfold powOKR eToNat feAt kToNat
  apply decide_eq_true
  dsimp only
  have h0 := (kAt sig o).val.toNat_lt
  have h1 := (kAt sig (o + 8)).val.toNat_lt
  have e : 2 ^ (192 - g) = 2 ^ 128 * 2 ^ (64 - g) := by rw [← pow_add]; congr 1; omega
  rw [e]
  have h2 : (kAt sig (o + 16)).val.toNat + 1 ≤ 2 ^ (64 - g) := h
  have h3 : 2 ^ 128 * ((kAt sig (o + 16)).val.toNat + 1) ≤ 2 ^ 128 * 2 ^ (64 - g) := Nat.mul_le_mul_left _ h2
  have : (kAt sig o).val.toNat + 2 ^ 64 * (kAt sig (o + 8)).val.toNat < 2 ^ 128 := by
    have : 2 ^ 64 * (kAt sig (o + 8)).val.toNat ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    norm_num at this ⊢; omega
  nlinarith

/-- If `z` holds zero, the sequence of `n` zero rows in `lvPre` forces the `n` consecutive
`E` cells from its incoming pointer to hold zero. -/
theorem seqZeros_hold (z : Cell) (hz : z.val M = 0) : ∀ (n : Nat) (p : Ptr),
    SegsHold c M p (seqAll ((List.range n).map fun _ => lin .E 0 0 z z) p).2 →
      ∀ k < n, M.e (p.e + k) = 0
  | 0, _, _, _, hk => by omega
  | n + 1, p, h, k, hk => by
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      seqAll, bind_apply, pure_apply, List.append_nil] at h
    rw [segsHold_append] at h
    have hzero := lin_spec h.1
    have hadv : p.adv (lin .E 0 0 z z p).2 = ⟨p.k, p.e + 1⟩ := by
      simp [lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
    rw [hadv] at h
    cases k with
    | zero => simpa [lin, rowRes, Ptr.at, hz, ofK_zero] using hzero
    | succ k =>
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using seqZeros_hold z hz n ⟨p.k, p.e + 1⟩ h.2 k (by omega)

/-- Factor a shared builder continuation out of an `if`, whose true branch first runs `m`
and whose branches return `a` and `b`, respectively. -/
theorem ite_bind_eq_bind_ite {α β γ : Type} (P : Prop) [Decidable P] (m : BM α) (a b : β) (f : β → BM γ) :
    (if P then m >>= fun _ => pure a >>= f else pure b >>= f) =
      ((if P then m >>= fun _ => pure a else pure b) >>= f) := by
  funext p
  by_cases h : P <;>
    simp only [h, ite_true, ite_false, bind_apply, pure_apply, List.append_nil,
      List.nil_append, Ptr.adv_nil]

theorem lvPre_spec (C : SCfg) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (pc : Nat)
    (zc oc g : Cell) (zk : Nat) (hz : zc.val M = 0) (ho : oc.val M = 1) (hzE : zc.ty = .E)
    (hoE : oc.ty = .E) (hgK : g.ty = .K) (hg : g.val M = 1) (hzk : M.k zk = 0)
    (L : Level) (nxt : Option Level) (i f V : Nat) (q : Cell × Cell × Cell) (p : Ptr) (hp : 1 ≤ p.e)
    (hν : f + L.fold + L.kappa = C.nu) (hw0 : L.level ≠ 0 ∨ (0 < L.fold ∧ L.row / 8 ≤ 2 ^ L.fold))
    (htc : L.t ≤ pw (C.pch i))
    (hch : ∀ k < (C.pch i).length, pw ((C.pch i).take k) < L.t) (hcs : csum (C.cch i) = L.kappa)
    (hT1 : (lvLanes C.g C.ood L nxt V).V4 + 1 + oStr L * (L.t - 1) + 3 * 2 ^ L.fold + 2 < T)
    (hT2 : (lvLanes C.g C.ood L nxt V).V6 + 8 < T) (hg64 : C.g ≤ 64)
    (hfold : ∀ j < L.fold, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40))
    (hpos : ∀ j < L.t, FE.ofK (M.k (C.pb i + j)) =
      eOfNat ((qsAt sig (8 * (lvLanes C.g C.ood L nxt V).V2) L).getD j 0))
    (hpw : C.g ≠ 0 → (M.k (C.pw i)).val.toNat < 2 ^ (64 - C.g))
    (h : Lvm.QSig.Ok c M (lvPre C pc zc oc g zk L nxt i f V q) p) :
    qv M (lvPre C pc zc oc g zk L nxt i f V q p).1.1 =
      (if C.ood && nxt.isSome then
        List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) *
            feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) * b)
          (List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) * b)
            (frQ sig (8 * V) L.fold (qv M q))
            ((oodF sig true L.kappa (8 * (lvLanes C.g C.ood L nxt V).Vc)).headD ([], fun _ => 0)).1)
      else
        List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) * b)
          (frQ sig (8 * V) L.fold (qv M q)))
        [feAt sig (8 * (lvLanes C.g C.ood L nxt V).V5 + 40),
          Lvm.dot (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40)) L.t) ((List.range L.t).map fun j =>
            if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold))
              (8 * ((lvLanes C.g C.ood L nxt V).V4 + 1 + oStr L * j)) (L.row / 8)
            else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold))
              (8 * ((lvLanes C.g C.ood L nxt V).V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
            feAt sig (8 * (lvLanes C.g C.ood L nxt V).V5 + 64),
          feAt sig (8 * (lvLanes C.g C.ood L nxt V).V5 + 64)] ∧
    (lvPre C pc zc oc g zk L nxt i f V q p).1.2.map (fun x => (x.1.val M, x.2.val M)) =
      (if C.ood && nxt.isSome then
        [(1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40),
            eqEval (oodZ sig (8 * (lvLanes C.g C.ood L nxt V).Vc) L.kappa) ((ptv M pc C.nu).drop (f + L.fold))),
          (1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40),
            inducedWeight L.kappa (qsAt sig (8 * (lvLanes C.g C.ood L nxt V).V2) L)
              (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40)) L.t) ((ptv M pc C.nu).drop (f + L.fold)))]
      else
        [(1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40),
          inducedWeight L.kappa (qsAt sig (8 * (lvLanes C.g C.ood L nxt V).V2) L)
            (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40)) L.t) ((ptv M pc C.nu).drop (f + L.fold)))]) ∧
    powF sig C.g (8 * (lvLanes C.g C.ood L nxt V).Vo) = true := by
  have lf := lvLanes_facts C.g C.ood L nxt V
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lf
  simp only [lvPre] at h ⊢
  generalize (lvLanes C.g C.ood L nxt V).V1 = V1 at *
  generalize (lvLanes C.g C.ood L nxt V).V2 = V2 at *
  generalize (lvLanes C.g C.ood L nxt V).V3 = V3 at *
  generalize (lvLanes C.g C.ood L nxt V).V4 = V4 at *
  generalize (lvLanes C.g C.ood L nxt V).V5 = V5 at *
  generalize (lvLanes C.g C.ood L nxt V).V6 = V6 at *
  generalize (lvLanes C.g C.ood L nxt V).Vc = Vc at *
  generalize (lvLanes C.g C.ood L nxt V).Vo = Vo at *
  have hpw2 : L.t ≤ 2 ^ Nat.clog 2 (pw (C.pch i)) := le_trans htc (Nat.le_pow_clog (by norm_num) _)
  -- 1. fold rounds
  obtain ⟨h1, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e1 := roundsG_spec hS L.fold f V q p (by omega) hfold h1.1
  have hp1 := le_trans hp (adv_e_le p (roundsG pc f V L.fold q p).2)
  generalize (roundsG pc f V L.fold q p).1 = q1 at h e1 ⊢
  generalize p.adv (roundsG pc f V L.fold q p).2 = p1 at h hp1 ⊢
  -- 2. λ
  obtain ⟨h2, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e2 := ldE_spec hS (by omega) h2.1
  rw [ldE_out] at e2 h ⊢
  rw [ldEW_adv] at h ⊢
  have e2' : M.e p1.e = feAt sig (8 * V3 + 40) := by
    rw [show 8 * V3 + 40 = 8 * (V3 + 5) by ring]; exact e2
  -- 3. powers of λ
  obtain ⟨h3, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e3 := pows_spec h3.1 hz ho hoE
  have hlp : ∀ k < L.t, M.e ((pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 + k) =
      feAt sig (8 * V3 + 40) ^ k := fun k hk => by rw [e3 k (by omega), Cell.val_E, e2']
  have hp3 : 1 ≤ ((⟨p1.k, p1.e + 1⟩ : Ptr).adv
      (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2).e :=
    le_trans (by simp) (adv_e_le _ _)
  generalize (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 = lp at h hlp ⊢
  generalize (⟨p1.k, p1.e + 1⟩ : Ptr).adv
    (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2 = p3 at h hp3 ⊢
  -- 4. the fold `eq` table
  obtain ⟨h4, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hlen := frC_length sig (8 * V) L.fold
  have h4' := h4.1
  rw [← hlen] at h4'
  have e4 := eqTab_eq (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) (frC sig (8 * V) L.fold)
    h4' hz (fun _ => rfl) (by rw [← val_E hoE]; exact ho)
    (fun j hj => by rw [Cell.val_E, frC_getD _ _ _ _ (by omega), hfold j (by omega)])
  simp only [hlen] at e4
  have hp4 := le_trans hp3 (adv_e_le p3
    (eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).2)
  have hend := fun (hn : 0 < L.fold) =>
    eqTab_end (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) hn p3
  generalize (eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).1 = er0
    at h e4 hend ⊢
  generalize p3.adv (eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).2 = p4
    at h hp4 hend ⊢
  rw [ite_bind_eq_bind_ite] at h ⊢
  let win : BM Nat := if L.level = 0 ∧ L.row / 8 < 2 ^ L.fold then do
      let _ ← seqAll ((List.range (2 ^ L.fold - L.row / 8)).map fun _ => lin .E 0 0 zc zc)
      pure (er0 + (2 ^ L.fold - L.row / 8))
    else pure er0
  obtain ⟨hwin, h⟩ := okb h
  rw [bind_apply]; dsimp only
  change Lvm.QSig.Ok c M win p4 at hwin
  have hww : decide (L.level = 0) = true → L.row / 8 ≤ 2 ^ L.fold := by
    intro hl
    have hl' : L.level = 0 := of_decide_eq_true hl
    exact (hw0.resolve_left (by simp [hl'])).2
  have e4w : ∀ k < 2 ^ L.fold, M.e ((win p4).1 + k) =
      if decide (L.level = 0) then
        if k < L.row / 8 then (eqKernelA (frC sig (8 * V) L.fold)).getD (L.row / 8 - 1 - k) 0 else 0
      else (eqKernelA (frC sig (8 * V) L.fold)).getD k 0 := by
    intro k hk
    by_cases hnwin : L.level = 0 ∧ L.row / 8 < 2 ^ L.fold
    · have hpositive := (hw0.resolve_left (by simp [hnwin.1])).1
      have heEnd := hend hpositive
      have hzwin := hwin
      simp only [win, if_pos hnwin] at hzwin
      have hzeros := seqZeros_hold zc hz (2 ^ L.fold - L.row / 8) p4 (okb hzwin).1.1
      simp only [win, if_pos hnwin, bind_apply, pure_apply, hnwin.1, decide_true, ite_true]
      by_cases hkw : k < L.row / 8
      · rw [if_pos hkw]
        have he := e4 (2 ^ L.fold - L.row / 8 + k) (by omega)
        simpa only [hnwin.1, decide_true, ite_true,
          show 2 ^ L.fold - 1 - (2 ^ L.fold - L.row / 8 + k) = L.row / 8 - 1 - k by omega,
          Nat.add_assoc] using he
      · rw [if_neg hkw, show er0 + (2 ^ L.fold - L.row / 8) + k = p4.e + (k - L.row / 8) by omega]
        exact hzeros (k - L.row / 8) (by omega)
    · simp only [win, if_neg hnwin, pure_apply]
      by_cases hl : L.level = 0
      · have hw : L.row / 8 = 2 ^ L.fold := by
          have := (hw0.resolve_left (by simp [hl])).2
          omega
        simpa [hl, hw, hk] using e4 k hk
      · simpa [hl] using e4 k hk
  have hp4w := le_trans hp4 (adv_e_le p4 (win p4).2)
  generalize (win p4).1 = er at h e4w ⊢
  generalize p4.adv (win p4).2 = p4w at h hp4w ⊢
  -- 5. row folds and the enforced sum
  obtain ⟨h5, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e5 := foldsG_window_spec hS hz (eqKernelA (frC sig (8 * V) L.fold)) (feAt sig (8 * V3 + 40)) hww e4w hlp
    (fun k hk => by
      have : oStr L * k ≤ oStr L * (L.t - 1) := Nat.mul_le_mul_left _ (by omega)
      omega)
    (C.pch i) 0 p4w hp4w (by simpa [pw] using htc) (fun k hk => by simpa [pw] using hch k hk) h5.1
  have hp5 := le_trans hp4w (adv_e_le p4w (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp
    L.t zc 0 (C.pch i) p4w).2)
  generalize (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i) p4w).1 = enf
    at h e5 ⊢
  generalize p4w.adv (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i)
    p4w).2 = p5 at h hp5 ⊢
  -- 6. the intro polynomial
  obtain ⟨h6, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e6 := rdQ_spec hS (by omega) h6.1
  have hp6 := le_trans hp5 (adv_e_le p5 (rdQ V5 enf p5).2)
  generalize (rdQ V5 enf p5).1 = it at h e6 ⊢
  generalize p5.adv (rdQ V5 enf p5).2 = p6 at h hp6 ⊢
  -- 7. pointer, 8. roots and inverses
  obtain ⟨-, h⟩ := okb h
  rw [bind_apply]; dsimp only [getPtr] at h ⊢
  rw [Ptr.adv_nil] at h ⊢
  obtain ⟨h8, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e8 := iwConsts_spec L.kappa hgK h8.1
  have hp8 := le_trans hp6 (adv_e_le p6 (iwConsts L.kappa g p6).2)
  generalize p6.adv (iwConsts L.kappa g p6).2 = p8 at h hp8 ⊢
  -- 9. the column weight
  obtain ⟨h9, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hptl : ((ptv M pc C.nu).drop (f + L.fold)).length = L.kappa := by
    rw [List.length_drop, ptv_length]; omega
  have e9 := colWG_spec hzE hz hzk L.kappa (qsAt sig (8 * V2) L) (feAt sig (8 * V3 + 40))
    ((ptv M pc C.nu).drop (f + L.fold)) (by rw [hptl, hcs])
    (fun k hk => by rw [ptv_getD _ _ _ _ (by omega)])
    (fun k hk => by rw [hptl] at hk; exact (e8 k hk).2)
    (fun k hk => by rw [hptl] at hk; exact (e8 k hk).1) hlp hpos (C.pch i) 0 p8
    hp8 (by simpa [pw] using htc) (fun k hk => by simpa [pw] using hch k hk) h9.1
  have eW : (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0 (C.pch i)
      p8).1.val M = inducedWeight L.kappa (qsAt sig (8 * V2) L) (powers (feAt sig (8 * V3 + 40)) L.t)
        ((ptv M pc C.nu).drop (f + L.fold)) := by
    rw [e9, ← Finset.range_eq_Ico, ← qsAt_length sig (8 * V2) L, inducedWeight_pow]
  have hp9 := le_trans hp8 (adv_e_le p8 (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp
    (C.pb i) L.t zc zk 0 (C.pch i) p8).2)
  generalize (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0 (C.pch i)
    p8).1 = W at h eW ⊢
  generalize p8.adv (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0
    (C.pch i) p8).2 = p9 at h hp9 ⊢
  -- 10. the PoW check
  obtain ⟨h10, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hpow : powF sig C.g (8 * Vo) = true := by
    unfold powF
    split_ifs with hg0
    · rfl
    · obtain ⟨gt, gn⟩ := g
      cases hgK
      have hV2 : V2 = Vo + 21 := by rw [l9]; simp [hg0]
      simp only [powG, hg0, ↓reduceIte] at h10
      have e := assertEqKK_spec h10.1 h10.2 (ofK_inj (hg.trans ofK_one.symm))
      have hl := hS (V2 - 2) (by omega)
      rw [hl] at e
      apply powOKR_of hg64
      rw [show 8 * Vo + 136 + 16 = 8 * (V2 - 2) by omega, e]
      exact hpw hg0
  have hp10 := le_trans hp9 (adv_e_le p9 (powG C V2 i g p9).2)
  generalize p9.adv (powG C V2 i g p9).2 = p10 at h hp10 ⊢
  -- 11. the OOD items and the glue
  by_cases hod : (C.ood && nxt.isSome) = true
  · simp only [hod, ↓reduceIte] at h ⊢
    have hVo : Vo = Vc + 9 * L.kappa + 9 := by rw [l8]; simp [hod]
    obtain ⟨g1, h⟩ := okb h
    rw [bind_apply]; dsimp only
    obtain ⟨ezb, ez⟩ := preloadG_spec hS (fun v hv => by
      simp only [List.mem_map, List.mem_range] at hv; obtain ⟨j, hj, rfl⟩ := hv; omega) g1.1
    rw [ezb] at h ⊢
    rw [preloadG_adv] at h ⊢
    obtain ⟨g2, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have ey := ldE_spec hS (by omega) g2.1
    rw [ldE_out] at ey h ⊢
    rw [ldEW_adv] at h ⊢
    obtain ⟨g3, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eio := rdQ_spec hS (by omega) g3.1
    rw [rdQ_adv] at h ⊢
    obtain ⟨g4, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have el2 := mulAdd_spec g4.1
    obtain ⟨g5, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg1 := glueG_spec g5.1
    obtain ⟨g6, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg2 := glueG_spec g6.1
    obtain ⟨g7, -⟩ := okb h
    rw [bind_apply]; dsimp only
    have eo := eqZG_range g7.1 hz ho
    simp only [pure_apply]
    refine ⟨?_, ?_, hpow⟩
    · rw [eg2, eg1, eio, e1, e6, e5, el2, ey, hz, add_zero, Cell.val_E, e2']
      simp only [oodF, ↓reduceIte, List.headD_cons]
      rw [show 8 * (Vc + 9 * L.kappa + 3) + 40 = 8 * Vc + 72 * L.kappa + 24 + 40 by ring,
        show 8 * (Vc + 9 * L.kappa + 3) + 64 = 8 * Vc + 72 * L.kappa + 24 + 64 by ring,
        show 8 * (Vc + 9 * L.kappa + 5) = 8 * Vc + 72 * L.kappa + 40 by ring, dot_map_range,
        Finset.range_eq_Ico]
      simp only [decide_eq_true_eq, mul_one, one_mul, mul_assoc]
    · simp only [List.map_cons, List.map_nil, el2, Cell.val_E, e2', hz, add_zero, eW, eo, one_mul]
      refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
      congr 1
      congr 1
      · simp only [oodZ]
        refine List.map_congr_left fun j hj => ?_
        rw [ez j (by simpa using hj)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.mp hj),
          Option.map_some, Option.getD_some]
        congr 1; ring
      · apply List.ext_getElem (by simp [ptv_length]; omega)
        intro k h1 h2
        simp only [List.length_map, List.length_range] at h1
        rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0,
          ptv_getD _ _ _ _ (by omega)]
  · simp only [hod, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨g5, -⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg1 := glueG_spec g5.1
    simp only [pure_apply]
    refine ⟨?_, ?_, hpow⟩
    · rw [eg1, e1, e6, e5, Cell.val_E, e2', dot_map_range, Finset.range_eq_Ico]
      simp only [decide_eq_true_eq]
    · simp only [List.map_cons, List.map_nil, Cell.val_E, e2', eW, one_mul]


/-! ## Invariants of the level induction -/

/-- The challenge cells from `pc + f` hold `F`'s challenges of the levels `Ls` from lane `V`. -/
def ChOk (g : Nat) (ood : Bool) (M : Mem) (sig : ByteArray) (pc f : Nat) (Ls : List Level) (V : Nat) : Prop :=
  ∀ j < (chLanes g ood Ls V).length, M.e (pc + f + j) = feAt sig (8 * (chLanes g ood Ls V).getD j 0)

/-- The position cells of the levels `Ls` (level `i` first) hold `F`'s positions. -/
def PosOk (C : SCfg) (M : Mem) (sig : ByteArray) (i : Nat) (Ls : List Level) (V : Nat) : Prop :=
  ∀ i' < Ls.length, ∀ j < (Ls.getD i' default).t, FE.ofK (M.k (C.pb (i + i') + j)) =
    eOfNat ((qsAt sig (8 * (posLanes C.g C.ood Ls V).getD i' 0) (Ls.getD i' default)).getD j 0)

/-- The PoW fields of the levels `Ls` (level `i` first) are below `2^(64−g)` (the `BITS` class
`powSpec`'s `fld 0 (64−g) 0` outputs). -/
def PwOk (C : SCfg) (M : Mem) (i : Nat) (Ls : List Level) : Prop :=
  ∀ i' < Ls.length, C.g ≠ 0 → (M.k (C.pw (i + i'))).val.toNat < 2 ^ (64 - C.g)

theorem pwOk_head {C : SCfg} {M : Mem} {i : Nat} {L : Level} {rest : List Level} (h : PwOk C M i (L :: rest)) :
    C.g ≠ 0 → (M.k (C.pw i)).val.toNat < 2 ^ (64 - C.g) := by
  have := h 0 (by simp); simpa using this

theorem pwOk_next {C : SCfg} {M : Mem} {i : Nat} {L : Level} {rest : List Level} (h : PwOk C M i (L :: rest)) :
    PwOk C M (i + 1) rest := by
  intro i' hi' hg
  have := h (i' + 1) (by simp; omega) hg
  rwa [show i + (i' + 1) = i + 1 + i' by ring] at this

/-- The glued claims are the `(λ, W)` cells (weights at the point's suffix). -/
def GlOk (M : Mem) (pc ν f : Nat) (st : WhirState) (gl : List (Cell × Cell)) : Prop :=
  st.glued.map (fun gc => (gc.scalar, gc.weightAt ((ptv M pc ν).drop gc.foldStart))) =
    gl.map (fun x => (x.1.val M, x.2.val M)) ∧ ∀ gc ∈ st.glued, gc.foldStart ≤ f

theorem getD_app_left (a b : List Nat) (j : Nat) (h : j < a.length) : (a ++ b).getD j 0 = a.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right (a b : List Nat) (j : Nat) : (a ++ b).getD (a.length + j) 0 = b.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_map_range {α : Type} (n j : Nat) (φ : Nat → α) (d : α) (h : j < n) :
    ((List.range n).map φ).getD j d = φ j := by
  simp [List.getD_eq_getElem?_getD, h]

theorem chOk_fold {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L : Level} {rest : List Level} {V : Nat}
    (h : ChOk g ood M sig pc f (L :: rest) V) : ∀ j < L.fold, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40) := by
  intro j hj
  have hl : j < (chLanes g ood (L :: rest) V).length := by
    cases rest <;> simp [chLanes] <;> omega
  rw [h j hl]
  have : (chLanes g ood (L :: rest) V).getD j 0 = V + 15 * j + 5 := by
    cases rest <;> (simp only [chLanes]; rw [getD_app_left _ _ _ (by simpa using hj), getD_map_range _ _ _ _ hj])
  rw [this]; congr 1; ring

theorem chOk_next {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L N : Level} {rest : List Level} {V : Nat}
    (h : ChOk g ood M sig pc f (L :: N :: rest) V) :
    ChOk g ood M sig pc (f + L.fold) (N :: rest) (lvLanes g ood L (some N) V).V6 := by
  intro j hj
  have e := h (L.fold + j) (by simp only [chLanes] at hj ⊢; simp; omega)
  simp only [chLanes] at e ⊢
  have hlen : ((List.range L.fold).map (fun j => V + 15 * j + 5)).length = L.fold := by simp
  have ga := getD_app_right ((List.range L.fold).map (fun j => V + 15 * j + 5))
    (chLanes g ood (N :: rest) (lvLanes g ood L (some N) V).V6) j
  rw [hlen] at ga
  rw [ga] at e
  rw [show pc + (f + L.fold) + j = pc + f + (L.fold + j) by ring]; exact e

theorem chOk_tail {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L : Level} {V : Nat}
    (h : ChOk g ood M sig pc f [L] V) :
    ∀ j < L.kappa, M.e (pc + (f + L.fold) + j) = feAt sig (8 * (lvLanes g ood L none V).V6 + 120 * j + 40) := by
  intro j hj
  have e := h (L.fold + j) (by simp [chLanes]; omega)
  simp only [chLanes] at e
  have hlen : ((List.range L.fold).map (fun j => V + 15 * j + 5)).length = L.fold := by simp
  have ga := getD_app_right ((List.range L.fold).map (fun j => V + 15 * j + 5))
    ((List.range L.kappa).map (fun j => (lvLanes g ood L none V).V6 + 15 * j + 5)) j
  rw [hlen] at ga
  rw [ga, getD_map_range _ _ _ _ hj] at e
  rw [show pc + (f + L.fold) + j = pc + f + (L.fold + j) by ring, e]; congr 1; ring

theorem posOk_head {C : SCfg} {M : Mem} {sig : ByteArray} {i : Nat} {L : Level} {rest : List Level} {V : Nat}
    (h : PosOk C M sig i (L :: rest) V) : ∀ j < L.t, FE.ofK (M.k (C.pb i + j)) =
      eOfNat ((qsAt sig (8 * (lvLanes C.g C.ood L rest.head? V).V2) L).getD j 0) := by
  intro j hj
  have e := h 0 (by simp) j (by simpa using hj)
  cases rest <;> simpa [posLanes] using e

theorem posOk_next {C : SCfg} {M : Mem} {sig : ByteArray} {i : Nat} {L N : Level} {rest : List Level} {V : Nat}
    (h : PosOk C M sig i (L :: N :: rest) V) : PosOk C M sig (i + 1) (N :: rest) (lvLanes C.g C.ood L (some N) V).V6 := by
  intro i' hi' j hj
  have e := h (i' + 1) (by simp at hi' ⊢; omega) j (by simpa using hj)
  simp only [posLanes] at e
  rw [show i + 1 + i' = i + (i' + 1) by ring]
  simpa using e

theorem glue_one (lam : FE) (st : WhirState) (i : List FE) (w : List FE → FE) :
    glue lam st [(i, w)] = ⟨List.zipWith (fun q i => q + 1 * lam * i) st.runningQuad i, st.folds,
      st.glued ++ [⟨1 * lam, st.folds.length, w⟩]⟩ := rfl

theorem glue_two (lam : FE) (st : WhirState) (i₁ i₂ : List FE) (w₁ w₂ : List FE → FE) :
    glue lam st [(i₁, w₁), (i₂, w₂)] = ⟨List.zipWith (fun q i => q + 1 * lam * lam * i)
      (List.zipWith (fun q i => q + 1 * lam * i) st.runningQuad i₁) i₂, st.folds,
      st.glued ++ [⟨1 * lam, st.folds.length, w₁⟩] ++ [⟨1 * lam * lam, st.folds.length, w₂⟩]⟩ := rfl

theorem ptv_take_append {M : Mem} {pc ν f n : Nat} {a : List FE} (ha : a.length = n) (hν : f + n ≤ ν)
    (h : ∀ j < n, M.e (pc + f + j) = a.getD j 0) : (ptv M pc ν).take f ++ a = (ptv M pc ν).take (f + n) := by
  apply List.ext_getElem
  · simp [ptv, ha]; omega
  · intro k h1 h2
    simp only [List.length_append, List.length_take, ptv_length] at h1
    by_cases hk : k < f
    · rw [List.getElem_append_left (by simp [ptv]; omega)]
      simp [ptv]
    · rw [List.getElem_append_right (by simp [ptv]; omega)]
      have hm : ((ptv M pc ν).take f).length = f := by simp [ptv]; omega
      simp only [hm]
      have e := h (k - f) (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at e
      rw [← e]
      simp only [List.getElem_take, ptv, List.getElem_map, List.getElem_range]
      congr 1; omega

theorem wh_fe_beq (x y : FE) : (x == y) = true ↔ x = y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  show ((a0 == b0 && a1 == b1) && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem glued_foldl (gs : List GluedClaim) (fl tf pt : List FE) (b : FE) (hpt : fl ++ tf = pt)
    (hfs : ∀ gc ∈ gs, gc.foldStart ≤ fl.length) :
    gs.foldl (fun w cl => w + cl.scalar * cl.weightAt (fl.drop cl.foldStart ++ tf)) b =
      (gs.map fun gc => (gc.scalar, gc.weightAt (pt.drop gc.foldStart))).foldl (fun acc x => acc + x.1 * x.2) b := by
  induction gs generalizing b with
  | nil => rfl
  | cons gc gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih _ (fun g hg => hfs g (List.mem_cons_of_mem _ hg)), ← hpt,
      List.drop_append_of_le_length (hfs gc List.mem_cons_self)]

set_option maxHeartbeats 4000000 in
theorem levels_run (C : SCfg) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (pc : Nat)
    (zc oc g : Cell) (zk : Nat) (bas : Cell) (hz : zc.val M = 0) (ho : oc.val M = 1) (hzE : zc.ty = .E)
    (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) (hzk : M.k zk = 0) (lf : Nat)
    (B : List FE → FE) (hbas : bas.val M = B ((ptv M pc C.nu).drop lf ++ (ptv M pc C.nu).take lf)) :
    ∀ (Ls : List Level) (i f V : Nat) (q : Cell × Cell × Cell) (gl : List (Cell × Cell)) (st : WhirState)
      (p : Ptr), lvOk C T Ls i f V = true → 1 ≤ p.e → qv M q = st.runningQuad →
      st.folds = (ptv M pc C.nu).take f → ChOk C.g C.ood M sig pc f Ls V → PosOk C M sig i Ls V →
      PwOk C M i Ls → GlOk M pc C.nu f st gl → Lvm.QSig.Ok c M (levelsG C pc zc oc g zk bas Ls i f V q gl) p →
      ∀ s : RS, pos s = 8 * V →
        (whirLevels C.nu lf B false C.g C.ood Ls st sig s).2.ok = s.ok ∧
        pos (whirLevels C.nu lf B false C.g C.ood Ls st sig s).2 = 8 * stackEndL C.g C.ood Ls V ∧
        (whirLevels C.nu lf B false C.g C.ood Ls st sig s).2.msg = 0 := by
  intro Ls
  induction Ls with
  | nil => intro i f V q gl st p hok; simp [lvOk] at hok
  | cons L rest ih =>
    intro i f V q gl st p hok hp hq hfo hch hpo hpw hgl h s hs
    have hA := fun (n : Nat) (hn : f + L.fold + n = C.nu) => ptv_take_append (M := M) (pc := pc) (ν := C.nu) (f := f)
      (frC_length sig (8 * V) L.fold) (by omega) (fun j hj => by rw [frC_getD _ _ _ _ hj, chOk_fold hch j hj])
    cases rest with
    | nil =>
      simp only [lvOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        and_assoc, List.head?_nil, and_true] at hok
      obtain ⟨hν, hrow, hw0, ht1, htc, hchk, hcs, hT1, hT2, hm, hg64⟩ := hok
      replace hT1 := of_decide_eq_true hT1
      replace hT2 := of_decide_eq_true hT2
      have hfl : st.folds.length = f := by rw [hfo, List.length_take, ptv_length]; omega
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lvLanes_facts C.g C.ood L none V
      simp only [levelsG, List.head?_nil] at h
      obtain ⟨hpre, h⟩ := okb h
      have e := lvPre_spec C hS pc zc oc g zk hz ho hzE hoE hgK hg hzk L none i f V q p hp hν hw0 htc
        hchk hcs hT1 (by omega) hg64 (chOk_fold hch) (posOk_head hpo) (pwOk_head hpw) hpre
      generalize (lvPre C pc zc oc g zk L none i f V q p).1 = r at h e
      generalize p.adv (lvPre C pc zc oc g zk L none i f V q p).2 = p' at h
      obtain ⟨eq, el, epw⟩ := e
      simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at eq el
      rw [hq] at eq
      obtain ⟨ht, h⟩ := okb h
      have et := tailG_spec hS L.kappa (f + L.fold) (lvLanes C.g C.ood L none V).V6 r.1 p' hm (by omega)
        (fun j hj => chOk_tail hch j hj) ht.1
      generalize (tailG pc (f + L.fold) (lvLanes C.g C.ood L none V).V6 L.kappa r.1 p').1 = tgt at h et
      generalize p'.adv (tailG pc (f + L.fold) (lvLanes C.g C.ood L none V).V6 L.kappa r.1 p').2 = p2 at h
      obtain ⟨hmf, h⟩ := okb h
      have hVc : (lvLanes C.g C.ood L none V).Vc = (lvLanes C.g C.ood L none V).V1 + 3 * 2 ^ L.kappa := by
        simp [lvLanes]
      have hVcV2 : (lvLanes C.g C.ood L none V).Vc ≤ (lvLanes C.g C.ood L none V).V2 := by
        rw [l9]; split_ifs <;> omega
      have em := mleFold_eq hmf.1 sig
        ((List.range (2 ^ L.kappa)).map fun i => feAt sig (8 * (lvLanes C.g C.ood L none V).V1 + 40 + 24 * i))
        (frC sig (8 * (lvLanes C.g C.ood L none V).V6) L.kappa) (by simp) (frC_length _ _ _)
        (fun j hj => by rw [Cell.val_E, frC_getD _ _ _ _ hj, chOk_tail hch j hj])
        (fun v hv k hk => by
          have : 3 * v < 3 * 2 ^ L.kappa := by omega
          rw [hS _ (by omega)]; rfl)
        (fun v hv => by rw [getD_map_range _ _ _ _ hv]; congr 1; ring)
      generalize (mleFold L.kappa ((lvLanes C.g C.ood L none V).V1 + 5) (fun j => ec (pc + (f + L.fold) + j)) p2).1
        = mle at h em
      generalize p2.adv (mleFold L.kappa ((lvLanes C.g C.ood L none V).V1 + 5)
        (fun j => ec (pc + (f + L.fold) + j)) p2).2 = p3 at h
      obtain ⟨hw, h⟩ := okb h
      have ew := wsumG_spec (gl ++ r.2) bas p3 hw.1
      generalize (wsumG bas (gl ++ r.2) p3).1 = w at h ew
      generalize p3.adv (wsumG bas (gl ++ r.2) p3).2 = p4 at h
      have hfin := (terminalCheck_iff h.1 hg).mp h.2
      have hF := whirLevels_final C.nu lf B C.g C.ood L st sig s V hs hrow (by omega) hm
      dsimp only at hF
      rw [hF]
      refine ⟨?_, ?_, rfl⟩
      · rw [epw, Bool.true_and, Bool.and_eq_right_iff_imp]
        intro _
        rw [wh_fe_beq, glue_one]
        dsimp only
        rw [← eq, ← et, ← em, hfo, hA L.kappa (by omega)]
        have hB := ptv_take_append (M := M) (pc := pc) (ν := C.nu) (f := f + L.fold)
          (frC_length sig (8 * (lvLanes C.g C.ood L none V).V6) L.kappa) (by omega)
          (fun j hj => by rw [frC_getD _ _ _ _ hj, chOk_tail hch j hj])
        rw [List.take_of_length_le (l := ptv M pc C.nu) (i := f + L.fold + L.kappa)
          (by rw [ptv_length]; omega)] at hB
        rw [glued_foldl _ _ _ _ _ hB (fun gc hgc => ?_), hB, ← hbas]
        · rw [List.map_append, hgl.1]
          have hnew : ([⟨1 * feAt sig (8 * (lvLanes C.g C.ood L none V).V3 + 40),
              ((ptv M pc C.nu).take (f + L.fold)).length, fun x => inducedWeight L.kappa
                (qsAt sig (8 * (lvLanes C.g C.ood L none V).V2) L)
                (powers (feAt sig (8 * (lvLanes C.g C.ood L none V).V3 + 40)) L.t) x⟩] : List GluedClaim).map
              (fun gc => (gc.scalar, gc.weightAt ((ptv M pc C.nu).drop gc.foldStart))) =
              r.2.map (fun x => (x.1.val M, x.2.val M)) := by
            rw [el]
            simp only [List.map_cons, List.map_nil, List.length_take, ptv_length]
            rw [show min (f + L.fold) C.nu = f + L.fold by omega]
          rw [hnew, ← List.map_append, List.foldl_map, ← ew]
          exact hfin
        · rw [List.length_take, ptv_length, show min (f + L.fold) C.nu = f + L.fold by omega]
          rcases List.mem_append.mp hgc with h1 | h1
          · exact le_trans (hgl.2 gc h1) (by omega)
          · simp only [List.mem_singleton] at h1; subst h1; simp [ptv_length]
      · simp only [pos, stackEndL]
        have : 1 ≤ L.kappa := hm
        omega
    | cons N rest' =>
      simp only [lvOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        and_assoc, List.head?_cons] at hok
      obtain ⟨hν, hrow, hw0, ht1, htc, hchk, hcs, hT1, hT2, hm, hg64, hrest⟩ := hok
      replace hT1 := of_decide_eq_true hT1
      replace hT2 := of_decide_eq_true hT2
      have hfl : st.folds.length = f := by rw [hfo, List.length_take, ptv_length]; omega
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lvLanes_facts C.g C.ood L (some N) V
      rw [levelsG] at h
      simp only [List.head?_cons] at h
      obtain ⟨hpre, h⟩ := okb h
      have e := lvPre_spec C hS pc zc oc g zk hz ho hzE hoE hgK hg hzk L (some N) i f V q p hp hν hw0 htc
        hchk hcs hT1 (by omega) hg64 (chOk_fold hch) (posOk_head hpo) (pwOk_head hpw) hpre
      have hpr := le_trans hp (adv_e_le p (lvPre C pc zc oc g zk L (some N) i f V q p).2)
      generalize (lvPre C pc zc oc g zk L (some N) i f V q p).1 = r at h e
      generalize p.adv (lvPre C pc zc oc g zk L (some N) i f V q p).2 = p' at h hpr
      obtain ⟨eq, el, epw⟩ := e
      simp only [Option.isSome_some, Bool.and_true] at eq el
      rw [hq] at eq
      rw [whirLevels_step C.nu lf B C.g C.ood L N rest' st sig s V hs hrow (by omega) hm, epw, Bool.true_and]
      simp only [stackEndL]
      have hfo' : st.folds ++ frC sig (8 * V) L.fold = (ptv M pc C.nu).take (f + L.fold) := by
        rw [hfo]; exact hA L.kappa (by omega)
      by_cases hod : C.ood = true
      · rw [if_pos hod] at eq el
        rw [show oodF sig C.ood = oodF sig true by rw [hod]]
        simp only [oodF, ↓reduceIte, List.headD_cons, List.cons_append, List.nil_append, glue_two] at eq ⊢
        exact ih (i + 1) (f + L.fold) (lvLanes C.g C.ood L (some N) V).V6 r.1 (gl ++ r.2) _ p' hrest hpr
          (by exact eq) (by exact hfo') (chOk_next hch) (posOk_next hpo) (pwOk_next hpw)
          (by
            dsimp only [GlOk]
            refine ⟨?_, ?_⟩
            · rw [List.map_append, List.map_append, hgl.1, List.map_append, el]
              simp only [List.map_cons, List.map_nil, List.length_append, frC_length, hfl, List.append_assoc,
                List.singleton_append]
            · intro gc hgc
              simp only [List.mem_append, List.mem_singleton] at hgc
              rcases hgc with (h1 | h1) | h1
              · exact le_trans (hgl.2 gc h1) (by omega)
              · subst h1; simp [frC_length, hfl]
              · subst h1; simp [frC_length, hfl])
          h _ (by simp only [pos]; omega)
      · rw [if_neg hod] at eq el
        rw [show oodF sig C.ood = oodF sig false by simp only [Bool.not_eq_true] at hod; rw [hod]]
        simp only [oodF, Bool.false_eq_true, ↓reduceIte, List.nil_append, glue_one]
        exact ih (i + 1) (f + L.fold) (lvLanes C.g C.ood L (some N) V).V6 r.1 (gl ++ r.2) _ p' hrest hpr
          (by exact eq) (by exact hfo') (chOk_next hch) (posOk_next hpo) (pwOk_next hpw)
          (by
            dsimp only [GlOk]
            refine ⟨?_, ?_⟩
            · rw [List.map_append, hgl.1, List.map_append, el]
              simp only [List.map_cons, List.map_nil, List.length_append, frC_length, hfl]
            · intro gc hgc
              rcases List.mem_append.mp hgc with h1 | h1
              · exact le_trans (hgl.2 gc h1) (by omega)
              · simp only [List.mem_singleton] at h1; subst h1; simp [frC_length, hfl])
          h _ (by simp only [pos]; omega)
