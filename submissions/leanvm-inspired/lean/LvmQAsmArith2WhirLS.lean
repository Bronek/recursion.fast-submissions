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

theorem lvLanes_facts (L : Level) (nxt : Option Level) (V : Nat) :
    (lvLanes L nxt V).V1 = V + 15 * L.fold ∧ (lvLanes L nxt V).V1 ≤ (lvLanes L nxt V).V2 ∧
    (lvLanes L nxt V).V2 ≤ (lvLanes L nxt V).V3 ∧ (lvLanes L nxt V).V4 = (lvLanes L nxt V).V3 + 9 ∧
    (lvLanes L nxt V).V5 = (lvLanes L nxt V).V4 + oStr L * L.t ∧
    (lvLanes L nxt V).V6 = (lvLanes L nxt V).V5 + 6 := by
  cases nxt <;> simp [lvLanes]

set_option maxHeartbeats 1000000 in
theorem lvPre_spec (C : SCfg) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (pc : Nat)
    (zc oc g : Cell) (zk : Nat) (hz : zc.val M = 0) (ho : oc.val M = 1) (hzE : zc.ty = .E)
    (hoE : oc.ty = .E) (hgK : g.ty = .K) (hzk : M.k zk = 0)
    (L : Level) (nxt : Option Level) (i f V : Nat) (q : Cell × Cell × Cell) (p : Ptr) (hp : 1 ≤ p.e)
    (hν : f + L.fold + L.kappa = C.nu) (htc : L.t ≤ pw (C.pch i))
    (hch : ∀ k < (C.pch i).length, pw ((C.pch i).take k) < L.t) (hcs : csum (C.cch i) = L.kappa)
    (hT1 : (lvLanes L nxt V).V4 + 1 + oStr L * (L.t - 1) + 3 * 2 ^ L.fold + 2 < T)
    (hT2 : (lvLanes L nxt V).V6 + 8 < T)
    (hfold : ∀ j < L.fold, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40))
    (hpos : ∀ j < L.t, FE.ofK (M.k (C.pb i + j)) =
      eOfNat ((qsAt sig (8 * (lvLanes L nxt V).V2) L).getD j 0))
    (h : Lvm.QSig.Ok c M (lvPre C pc zc oc g zk L nxt i f V q) p) :
    qv M (lvPre C pc zc oc g zk L nxt i f V q p).1.1 =
      List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes L nxt V).V3 + 40) * b)
        (frQ sig (8 * V) L.fold (qv M q))
        [feAt sig (8 * (lvLanes L nxt V).V5 + 40),
          Lvm.dot (powers (feAt sig (8 * (lvLanes L nxt V).V3 + 40)) L.t) ((List.range L.t).map fun j =>
            if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold))
              (8 * ((lvLanes L nxt V).V4 + 1 + oStr L * j)) (2 ^ L.fold)
            else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold))
              (8 * ((lvLanes L nxt V).V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
            feAt sig (8 * (lvLanes L nxt V).V5 + 64),
          feAt sig (8 * (lvLanes L nxt V).V5 + 64)] ∧
    (lvPre C pc zc oc g zk L nxt i f V q p).1.2.1.val M = feAt sig (8 * (lvLanes L nxt V).V3 + 40) ∧
    (lvPre C pc zc oc g zk L nxt i f V q p).1.2.2.val M =
      inducedWeight L.kappa (qsAt sig (8 * (lvLanes L nxt V).V2) L)
        (powers (feAt sig (8 * (lvLanes L nxt V).V3 + 40)) L.t) ((ptv M pc C.nu).drop (f + L.fold)) := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lvLanes_facts L nxt V
  simp only [lvPre] at h ⊢
  generalize (lvLanes L nxt V).V1 = V1 at *
  generalize (lvLanes L nxt V).V2 = V2 at *
  generalize (lvLanes L nxt V).V3 = V3 at *
  generalize (lvLanes L nxt V).V4 = V4 at *
  generalize (lvLanes L nxt V).V5 = V5 at *
  generalize (lvLanes L nxt V).V6 = V6 at *
  have hpw : L.t ≤ 2 ^ Nat.clog 2 (pw (C.pch i)) := le_trans htc (Nat.le_pow_clog (by norm_num) _)
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
  generalize (eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).1 = er at h e4 ⊢
  generalize p3.adv (eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).2 = p4
    at h hp4 ⊢
  -- 5. row folds and the enforced sum
  obtain ⟨h5, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e5 := foldsG_spec hS hz (eqKernelA (frC sig (8 * V) L.fold)) (feAt sig (8 * V3 + 40)) e4 hlp
    (fun k hk => by
      have : oStr L * k ≤ oStr L * (L.t - 1) := Nat.mul_le_mul_left _ (by omega)
      omega)
    (C.pch i) 0 p4 hp4 (by simpa [pw] using htc) (fun k hk => by simpa [pw] using hch k hk) h5.1
  have hp5 := le_trans hp4 (adv_e_le p4 (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp
    L.t zc 0 (C.pch i) p4).2)
  generalize (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i) p4).1 = enf
    at h e5 ⊢
  generalize p4.adv (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i)
    p4).2 = p5 at h hp5 ⊢
  -- 6. the intro polynomial
  obtain ⟨h6, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e6 := rdQ_spec hS (by omega) h6.1
  have hp6 := le_trans hp5 (adv_e_le p5 (rdQ V5 enf p5).2)
  generalize (rdQ V5 enf p5).1 = it at h e6 ⊢
  generalize p5.adv (rdQ V5 enf p5).2 = p6 at h hp6 ⊢
  -- 7. glue
  obtain ⟨h7, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e7 := glueG_spec h7.1
  have hp7 := le_trans hp6 (adv_e_le p6 (glueG (ec p1.e) q1 it p6).2)
  generalize (glueG (ec p1.e) q1 it p6).1 = q2 at h e7 ⊢
  generalize p6.adv (glueG (ec p1.e) q1 it p6).2 = p7 at h hp7 ⊢
  -- 8. pointer, 9. roots and inverses
  obtain ⟨-, h⟩ := okb h
  rw [bind_apply]; dsimp only [getPtr] at h ⊢
  rw [Ptr.adv_nil] at h ⊢
  obtain ⟨h9, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e9 := iwConsts_spec L.kappa hgK h9.1
  have hp9 := le_trans hp7 (adv_e_le p7 (iwConsts L.kappa g p7).2)
  generalize p7.adv (iwConsts L.kappa g p7).2 = p9 at h hp9 ⊢
  -- 10. the column weight
  obtain ⟨h10, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hptl : ((ptv M pc C.nu).drop (f + L.fold)).length = L.kappa := by
    rw [List.length_drop, ptv_length]; omega
  have e10 := colWG_spec hzE hz hzk L.kappa (qsAt sig (8 * V2) L) (feAt sig (8 * V3 + 40))
    ((ptv M pc C.nu).drop (f + L.fold)) (by rw [hptl, hcs])
    (fun k hk => by rw [ptv_getD _ _ _ _ (by omega)])
    (fun k hk => by rw [hptl] at hk; exact (e9 k hk).2)
    (fun k hk => by rw [hptl] at hk; exact (e9 k hk).1) hlp hpos (C.pch i) 0 p9
    hp9 (by simpa [pw] using htc) (fun k hk => by simpa [pw] using hch k hk) h10.1
  simp only [pure_apply]
  refine ⟨?_, by rw [Cell.val_E, e2'], ?_⟩
  · rw [e7, e1, e6, e5, Cell.val_E, e2', dot_map_range, Finset.range_eq_Ico]
    simp only [decide_eq_true_eq]
  · rw [e10, ← Finset.range_eq_Ico, ← qsAt_length sig (8 * V2) L, inducedWeight_pow]

/-! ## Invariants of the level induction -/

/-- The challenge cells from `pc + f` hold `F`'s challenges of the levels `Ls` from lane `V`. -/
def ChOk (M : Mem) (sig : ByteArray) (pc f : Nat) (Ls : List Level) (V : Nat) : Prop :=
  ∀ j < (chLanes Ls V).length, M.e (pc + f + j) = feAt sig (8 * (chLanes Ls V).getD j 0)

/-- The position cells of the levels `Ls` (level `i` first) hold `F`'s positions. -/
def PosOk (C : SCfg) (M : Mem) (sig : ByteArray) (i : Nat) (Ls : List Level) (V : Nat) : Prop :=
  ∀ i' < Ls.length, ∀ j < (Ls.getD i' default).t, FE.ofK (M.k (C.pb (i + i') + j)) =
    eOfNat ((qsAt sig (8 * (posLanes Ls V).getD i' 0) (Ls.getD i' default)).getD j 0)

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

theorem chOk_fold {M : Mem} {sig : ByteArray} {pc f : Nat} {L : Level} {rest : List Level} {V : Nat}
    (h : ChOk M sig pc f (L :: rest) V) : ∀ j < L.fold, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40) := by
  intro j hj
  have hl : j < (chLanes (L :: rest) V).length := by
    cases rest <;> simp [chLanes] <;> omega
  rw [h j hl]
  have : (chLanes (L :: rest) V).getD j 0 = V + 15 * j + 5 := by
    cases rest <;> (simp only [chLanes]; rw [getD_app_left _ _ _ (by simpa using hj), getD_map_range _ _ _ _ hj])
  rw [this]; congr 1; ring

theorem chOk_next {M : Mem} {sig : ByteArray} {pc f : Nat} {L N : Level} {rest : List Level} {V : Nat}
    (h : ChOk M sig pc f (L :: N :: rest) V) : ChOk M sig pc (f + L.fold) (N :: rest) (lvLanes L (some N) V).V6 := by
  intro j hj
  have e := h (L.fold + j) (by simp only [chLanes] at hj ⊢; simp; omega)
  simp only [chLanes] at e ⊢
  have hlen : ((List.range L.fold).map (fun j => V + 15 * j + 5)).length = L.fold := by simp
  have ga := getD_app_right ((List.range L.fold).map (fun j => V + 15 * j + 5))
    (chLanes (N :: rest) (lvLanes L (some N) V).V6) j
  rw [hlen] at ga
  rw [ga] at e
  rw [show pc + (f + L.fold) + j = pc + f + (L.fold + j) by ring]; exact e

theorem chOk_tail {M : Mem} {sig : ByteArray} {pc f : Nat} {L : Level} {V : Nat}
    (h : ChOk M sig pc f [L] V) :
    ∀ j < L.kappa, M.e (pc + (f + L.fold) + j) = feAt sig (8 * (lvLanes L none V).V6 + 120 * j + 40) := by
  intro j hj
  have e := h (L.fold + j) (by simp [chLanes]; omega)
  simp only [chLanes] at e
  have hlen : ((List.range L.fold).map (fun j => V + 15 * j + 5)).length = L.fold := by simp
  have ga := getD_app_right ((List.range L.fold).map (fun j => V + 15 * j + 5))
    ((List.range L.kappa).map (fun j => (lvLanes L none V).V6 + 15 * j + 5)) j
  rw [hlen] at ga
  rw [ga, getD_map_range _ _ _ _ hj] at e
  rw [show pc + (f + L.fold) + j = pc + f + (L.fold + j) by ring, e]; congr 1; ring

theorem posOk_head {C : SCfg} {M : Mem} {sig : ByteArray} {i : Nat} {L : Level} {rest : List Level} {V : Nat}
    (h : PosOk C M sig i (L :: rest) V) : ∀ j < L.t, FE.ofK (M.k (C.pb i + j)) =
      eOfNat ((qsAt sig (8 * (lvLanes L rest.head? V).V2) L).getD j 0) := by
  intro j hj
  have e := h 0 (by simp) j (by simpa using hj)
  cases rest <;> simpa [posLanes] using e

theorem posOk_next {C : SCfg} {M : Mem} {sig : ByteArray} {i : Nat} {L N : Level} {rest : List Level} {V : Nat}
    (h : PosOk C M sig i (L :: N :: rest) V) : PosOk C M sig (i + 1) (N :: rest) (lvLanes L (some N) V).V6 := by
  intro i' hi' j hj
  have e := h (i' + 1) (by simp at hi' ⊢; omega) j (by simpa using hj)
  simp only [posLanes] at e
  rw [show i + 1 + i' = i + (i' + 1) by ring]
  simpa using e

theorem glue_one (lam : FE) (st : WhirState) (i : List FE) (w : List FE → FE) :
    glue lam st [(i, w)] = ⟨List.zipWith (fun q i => q + 1 * lam * i) st.runningQuad i, st.folds,
      st.glued ++ [⟨1 * lam, st.folds.length, w⟩]⟩ := rfl

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

set_option maxHeartbeats 2000000 in
theorem levels_run (C : SCfg) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (pc : Nat)
    (zc oc g : Cell) (zk : Nat) (bas : Cell) (hz : zc.val M = 0) (ho : oc.val M = 1) (hzE : zc.ty = .E)
    (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) (hzk : M.k zk = 0) (lf : Nat)
    (B : List FE → FE) (hbas : bas.val M = B ((ptv M pc C.nu).drop lf ++ (ptv M pc C.nu).take lf)) :
    ∀ (Ls : List Level) (i f V : Nat) (q : Cell × Cell × Cell) (gl : List (Cell × Cell)) (st : WhirState)
      (p : Ptr), lvOk C T Ls i f V = true → 1 ≤ p.e → qv M q = st.runningQuad →
      st.folds = (ptv M pc C.nu).take f → ChOk M sig pc f Ls V → PosOk C M sig i Ls V →
      GlOk M pc C.nu f st gl → Lvm.QSig.Ok c M (levelsG C pc zc oc g zk bas Ls i f V q gl) p →
      ∀ s : RS, pos s = 8 * V →
        (whirLevels C.nu lf B false 0 Ls st sig s).2.ok = s.ok ∧
        pos (whirLevels C.nu lf B false 0 Ls st sig s).2 = 8 * stackEndL Ls V ∧
        (whirLevels C.nu lf B false 0 Ls st sig s).2.msg = 0 := by
  intro Ls
  induction Ls with
  | nil => intro i f V q gl st p hok; simp [lvOk] at hok
  | cons L rest ih =>
    intro i f V q gl st p hok hp hq hfo hch hpo hgl h s hs
    have hA := fun (n : Nat) (hn : f + L.fold + n = C.nu) => ptv_take_append (M := M) (pc := pc) (ν := C.nu) (f := f)
      (frC_length sig (8 * V) L.fold) (by omega) (fun j hj => by rw [frC_getD _ _ _ _ hj, chOk_fold hch j hj])
    cases rest with
    | nil =>
      simp only [lvOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        and_assoc, List.head?_nil] at hok
      obtain ⟨hν, hrow, ht1, htc, hchk, hcs, hT1, hT2, hm⟩ := hok
      replace hT1 := of_decide_eq_true hT1
      replace hT2 := of_decide_eq_true hT2
      have hfl : st.folds.length = f := by rw [hfo, List.length_take, ptv_length]; omega
      obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lvLanes_facts L none V
      have hV2 : (lvLanes L none V).V2 = (lvLanes L none V).V1 + 3 * 2 ^ L.kappa := by simp [lvLanes]
      simp only [levelsG, List.head?_nil] at h
      obtain ⟨hpre, h⟩ := okb h
      have e := lvPre_spec C hS pc zc oc g zk hz ho hzE hoE hgK hzk L none i f V q p hp hν htc
        hchk hcs hT1 (by omega) (chOk_fold hch) (posOk_head hpo) hpre
      generalize (lvPre C pc zc oc g zk L none i f V q p).1 = r at h e
      generalize p.adv (lvPre C pc zc oc g zk L none i f V q p).2 = p' at h
      obtain ⟨eq, el, eW⟩ := e
      rw [hq] at eq
      obtain ⟨ht, h⟩ := okb h
      have et := tailG_spec hS L.kappa (f + L.fold) (lvLanes L none V).V6 r.1 p' hm (by omega)
        (fun j hj => chOk_tail hch j hj) ht.1
      generalize (tailG pc (f + L.fold) (lvLanes L none V).V6 L.kappa r.1 p').1 = tgt at h et
      generalize p'.adv (tailG pc (f + L.fold) (lvLanes L none V).V6 L.kappa r.1 p').2 = p2 at h
      obtain ⟨hmf, h⟩ := okb h
      have em := mleFold_eq hmf.1 sig
        ((List.range (2 ^ L.kappa)).map fun i => feAt sig (8 * (lvLanes L none V).V1 + 40 + 24 * i))
        (frC sig (8 * (lvLanes L none V).V6) L.kappa) (by simp) (frC_length _ _ _)
        (fun j hj => by rw [Cell.val_E, frC_getD _ _ _ _ hj, chOk_tail hch j hj])
        (fun v hv k hk => by
          have : 3 * v < 3 * 2 ^ L.kappa := by omega
          rw [hS _ (by omega)]; rfl)
        (fun v hv => by rw [getD_map_range _ _ _ _ hv]; congr 1; ring)
      generalize (mleFold L.kappa ((lvLanes L none V).V1 + 5) (fun j => ec (pc + (f + L.fold) + j)) p2).1
        = mle at h em
      generalize p2.adv (mleFold L.kappa ((lvLanes L none V).V1 + 5)
        (fun j => ec (pc + (f + L.fold) + j)) p2).2 = p3 at h
      obtain ⟨hw, h⟩ := okb h
      have ew := wsumG_spec (gl ++ [(r.2.1, r.2.2)]) bas p3 hw.1
      generalize (wsumG bas (gl ++ [(r.2.1, r.2.2)]) p3).1 = w at h ew
      generalize p3.adv (wsumG bas (gl ++ [(r.2.1, r.2.2)]) p3).2 = p4 at h
      have hfin := (terminalCheck_iff h.1 hg).mp h.2
      have hF := whirLevels_final C.nu lf B L st sig s V hs hrow (by omega) hm
      dsimp only at hF
      rw [hF]
      refine ⟨?_, ?_, rfl⟩
      · rw [Bool.and_eq_right_iff_imp]
        intro _
        rw [wh_fe_beq, glue_one]
        dsimp only
        rw [← eq, ← et, ← em, hfo, hA L.kappa (by omega)]
        have hB := ptv_take_append (M := M) (pc := pc) (ν := C.nu) (f := f + L.fold)
          (frC_length sig (8 * (lvLanes L none V).V6) L.kappa) (by omega)
          (fun j hj => by rw [frC_getD _ _ _ _ hj, chOk_tail hch j hj])
        rw [List.take_of_length_le (l := ptv M pc C.nu) (i := f + L.fold + L.kappa)
          (by rw [ptv_length]; omega)] at hB
        rw [glued_foldl _ _ _ _ _ hB (fun gc hgc => ?_), hB, ← hbas]
        · rw [List.map_append, hgl.1]
          have hnew : ([⟨1 * feAt sig (8 * (lvLanes L none V).V3 + 40),
              ((ptv M pc C.nu).take (f + L.fold)).length, fun x => inducedWeight L.kappa
                (qsAt sig (8 * (lvLanes L none V).V2) L)
                (powers (feAt sig (8 * (lvLanes L none V).V3 + 40)) L.t) x⟩] : List GluedClaim).map
              (fun gc => (gc.scalar, gc.weightAt ((ptv M pc C.nu).drop gc.foldStart))) =
              [(r.2.1, r.2.2)].map (fun x => (x.1.val M, x.2.val M)) := by
            simp only [List.map_cons, List.map_nil, List.length_take, ptv_length, el, eW, one_mul]
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
      obtain ⟨hν, hrow, ht1, htc, hchk, hcs, hT1, hT2, hrest⟩ := hok
      replace hT1 := of_decide_eq_true hT1
      replace hT2 := of_decide_eq_true hT2
      have hfl : st.folds.length = f := by rw [hfo, List.length_take, ptv_length]; omega
      obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lvLanes_facts L (some N) V
      rw [levelsG] at h
      simp only [List.head?_cons] at h
      obtain ⟨hpre, h⟩ := okb h
      have e := lvPre_spec C hS pc zc oc g zk hz ho hzE hoE hgK hzk L (some N) i f V q p hp hν htc
        hchk hcs hT1 (by omega) (chOk_fold hch) (posOk_head hpo) hpre
      have hpr := le_trans hp (adv_e_le p (lvPre C pc zc oc g zk L (some N) i f V q p).2)
      generalize (lvPre C pc zc oc g zk L (some N) i f V q p).1 = r at h e
      generalize p.adv (lvPre C pc zc oc g zk L (some N) i f V q p).2 = p' at h hpr
      obtain ⟨eq, el, eW⟩ := e
      rw [hq] at eq
      rw [whirLevels_step C.nu lf B L N rest' st sig s V hs hrow, glue_one]
      simp only [stackEndL]
      exact ih (i + 1) (f + L.fold) (lvLanes L (some N) V).V6 r.1 (gl ++ [(r.2.1, r.2.2)]) _ p' hrest hpr
        (by exact eq) (by show st.folds ++ frC sig (8 * V) L.fold = _; rw [hfo]; exact hA L.kappa (by omega))
        (chOk_next hch) (posOk_next hpo)
        (by
          dsimp only [GlOk]
          refine ⟨?_, ?_⟩
          · rw [List.map_append, hgl.1, List.map_append]
            simp only [List.map_cons, List.map_nil, List.length_append, frC_length, hfl, el, eW, one_mul]
            rw [show C.nu - (f + L.fold) = L.kappa by omega]
          · intro gc hgc
            rcases List.mem_append.mp hgc with h1 | h1
            · exact le_trans (hgl.2 gc h1) (by omega)
            · simp only [List.mem_singleton] at h1; subst h1; simp [frC_length, hfl])
        h _ (by simp only [pos]; omega)
