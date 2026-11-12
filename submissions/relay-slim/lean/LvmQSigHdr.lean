import LvmQSigPre

/-!
# `Q_sig`: the child's header checks and `σ_leaf' = b'·σ_leaf`

New for lvm (WP-12). `header_spec`, `gSl_spec`: in every memory where the gadget's rows and
assertions hold, with the gate (the node flag) `1`, `Z = 0`, `O = 1`, the equations below hold on
the input cells (BLUEPRINT §11 A2, A3).
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Helpers: gadgets that hold, sequencing, `forN`, product chains -/

/-- A gadget's rows and assertions both hold at `q`. -/
def Ok (c : Ctx) (M : Mem) {α : Type} (m : BM α) (q : Ptr) : Prop :=
  SegsHold c M q (m q).2 ∧ SegsAssert M q (m q).2

theorem ok_bind {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Ok c M (m >>= f) p) : ∃ q, Ok c M m p ∧ Ok c M (f (m p).1) q := by
  obtain ⟨h1, h2⟩ := h
  rw [hold_bind] at h1; rw [assert_bind] at h2
  exact ⟨_, ⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

theorem seqAll_cons_apply {α : Type} (m : BM α) (ms : List (BM α)) (p : Ptr) :
    seqAll (m :: ms) p = ((m p).1 :: (seqAll ms (p.adv (m p).2)).1,
      (m p).2 ++ ((seqAll ms (p.adv (m p).2)).2 ++ [])) := rfl

theorem ok_seqAll {c : Ctx} {M : Mem} {α : Type} :
    ∀ (ms : List (BM α)) (p : Ptr), Ok c M (seqAll ms) p → ∀ m ∈ ms, ∃ q, Ok c M m q
  | [], _, _, _, hm => absurd hm (List.not_mem_nil)
  | m :: ms, p, h, m', hm => by
    obtain ⟨h1, h2⟩ := h
    rw [seqAll_cons_apply, segsHold_append, segsHold_append] at h1
    rw [seqAll_cons_apply, segsAssert_append, segsAssert_append] at h2
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨p, h1.1, h2.1⟩
    · exact ok_seqAll ms _ ⟨h1.2.1, h2.2.1⟩ m' hm

theorem ok_forN {c : Ctx} {M : Mem} {α : Type} {n : Nat} {f : Nat → BM α} {p : Ptr}
    (h : Ok c M (forN n f) p) : ∀ l < n, ∃ q, Ok c M (f l) q := fun l hl =>
  ok_seqAll _ p h (f l) (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)

theorem seqAll_res {c : Ctx} {M : Mem} {α : Type} {f : Nat → BM α} {P : Nat → α → Prop}
    (hf : ∀ z q, SegsHold c M q (f z q).2 → P z (f z q).1) :
    ∀ (l : List Nat) (p : Ptr), SegsHold c M p (seqAll (l.map f) p).2 →
      List.Forall₂ P l (seqAll (l.map f) p).1
  | [], _, _ => List.Forall₂.nil
  | z :: l, p, h => by
    rw [List.map_cons, seqAll_cons_apply, segsHold_append, segsHold_append] at h
    rw [List.map_cons, seqAll_cons_apply]
    exact List.Forall₂.cons (hf z p h.1) (seqAll_res hf l _ h.2.1)

theorem map_of_forall₂ {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {xs : List β}, List.Forall₂ (fun z x => g x = f z) l xs → xs.map g = l.map f
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h t => by simp [h, map_of_forall₂ t]

theorem prodChain_spec {c : Ctx} {M : Mem} {zn : Nat} (hZ : M.k zn = 0) :
    ∀ (qs : List Cell) (an : Nat) (p : Ptr), (∀ q ∈ qs, q.ty = .K) →
      SegsHold c M p (prodChain (kc zn) (kc an) qs p).2 →
      (prodChain (kc zn) (kc an) qs p).1.ty = .K ∧
        M.k (prodChain (kc zn) (kc an) qs p).1.n = M.k an * (qs.map fun q => M.k q.n).prod
  | [], an, p, _, _ => ⟨rfl, by simp [prodChain, pure_apply]⟩
  | ⟨ty, qn⟩ :: qs, an, p, hK, h => by
    have hty : ty = .K := hK _ List.mem_cons_self
    subst hty
    rw [prodChain, hold_bind] at h
    have e := mulAddK_spec (a := an) (b := qn) (d := zn) h.1
    have ih := prodChain_spec hZ qs p.k _ (fun q hq => hK q (List.mem_cons_of_mem _ hq)) h.2
    refine ⟨ih.1, ?_⟩
    show M.k (prodChain (kc zn) (kc p.k) qs _).1.n = _
    rw [ih.2, e, hZ, add_zero, List.map_cons, List.prod_cons, mul_assoc]


theorem forall₂_right {α β : Type} {P : β → Prop} {Q : α → β → Prop} :
    ∀ {l : List α} {xs : List β}, List.Forall₂ (fun z x => P x ∧ Q z x) l xs → ∀ x ∈ xs, P x
  | _, _, List.Forall₂.nil => fun _ hx => absurd hx List.not_mem_nil
  | _, _, List.Forall₂.cons h t => fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact forall₂_right t x hx

theorem ok_assert0 {c : Ctx} {M : Mem} {q : Ptr} {a : Cell} {g : Nat} (ha : a.ty = .K)
    (h : Ok c M (assert0 a (kc g)) q) : M.k g * M.k a.n = 0 := by
  obtain ⟨t, n⟩ := a
  simp only at ha; subst ha
  exact assert0K_spec h.2

theorem ok_assertEq {c : Ctx} {M : Mem} {q : Ptr} {a b g : Nat}
    (h : Ok c M (assertEq (kc a) (kc b) (kc g)) q) (hg : M.k g = 1) : M.k a = M.k b :=
  assertEqKK_spec h.1 h.2 hg

/-- The statement mux of the header: `c_L = b'·(yns + yls) + yls`. -/
theorem ok_sel {c : Ctx} {M : Mem} {q : Ptr} {I : SigIn} {l : Nat}
    (h : Ok c M (do
      let dl ← add (kc (I.yns + l)) (kc (I.yls + l))
      let sel ← mad (kc I.hd) dl (kc (I.yls + l))
      assertEq sel (kc (I.cL + l)) (kc I.flag)) q) (hg : M.k I.flag = 1) :
    M.k I.hd * (M.k (I.yns + l) + M.k (I.yls + l)) + M.k (I.yls + l) = M.k (I.cL + l) := by
  obtain ⟨q1, o1, h⟩ := ok_bind h
  obtain ⟨q2, o2, h⟩ := ok_bind h
  have e1 := linK_spec (k := 1) (k' := 0) (a := I.yns + l) (b := I.yls + l) o1.1
  have e2 := mulAddK_spec (a := I.hd) (b := q.k) (d := I.yls + l) o2.1
  have e3 := ok_assertEq (a := q1.k) (b := I.cL + l) h hg
  rw [← e3, e2, e1, one_mul, add_zero]

/-- One `slTpl` loop: lane `off + j` of `σ_leaf' = b'·σ_leaf` when the gate is on. -/
theorem sl_loop {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {d off : Nat}
    (h : SegsHold c M p (loop [d] (slTpl I off) p).2)
    (hA : SegsAssert M p (loop [d] (slTpl I off) p).2) (hg : M.k I.flag = 1) :
    ∀ j < 2 ^ d, M.k I.hd * M.k (I.sl + off + j) + M.k (I.hd + 18 + off + j) = 0 := by
  intro j hj
  have hjf : j < 2 ^ ([d] : List Nat).sum := by simpa using hj
  have hK : OpdK (loop [d] (slTpl I off) p).1 (.cur 0) := rfl
  have r := loopK_mad h hjf (t := 0) (by simp [slTpl]) rfl rfl rfl rfl
  have a := loopK_as0 hA hjf (t := 1) (by simp [slTpl]) rfl hK rfl
  rw [ov_cur M _ hjf 0 rfl, r, ov_oA, ov_oA, ov_oS M _ rfl hj, ov_oS M _ rfl hj, hg, one_mul] at a
  simpa using a

/-- **The header checks.** -/
theorem header_spec {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {Z O : Cell} (hZt : Z.ty = .K)
    (hOt : O.ty = .K) (h : SegsHold c M p (header I Z O p).2) (hA : SegsAssert M p (header I Z O p).2)
    (hg : M.k I.flag = 1) (hZ : M.k Z.n = 0) (hO : M.k O.n = 1) :
    (∀ l < 4, M.k (I.hd + 1 + l) = M.k (I.vk + l)) ∧
      (∀ l < 4, M.k (I.yc + 64 + l) = M.k (I.vk + l)) ∧
      M.k I.hd * M.k I.hd + M.k I.hd = 0 ∧
      (M.k I.hd = 0 → ∀ l < 4, M.k (I.hd + 5 + l) = 0) ∧
      M.k (I.bn + 2 + I.ln + 1) = 0 ∧
      M.k (I.bn + 2 + I.ln) * M.k (I.bn + 2 + I.ln + 2) = 0 ∧
      ((List.range (I.ln + 1)).map fun z => M.k (I.bn + 2 + z) + 1).prod = 0 ∧
      (∀ l < 4, M.k I.hd * (M.k (I.yns + l) + M.k (I.yls + l)) + M.k (I.yls + l) = M.k (I.cL + l)) := by
  obtain ⟨zt, zn⟩ := Z
  obtain ⟨ot, on⟩ := O
  simp only at hZt hOt hZ hO
  subst hZt hOt
  have H : Ok c M (header I (kc zn) (kc on)) p := ⟨h, hA⟩
  clear h hA
  simp only [header] at H
  obtain ⟨q1, o1, H⟩ := ok_bind H
  obtain ⟨q2, o2, H⟩ := ok_bind H
  obtain ⟨q3, o3, H⟩ := ok_bind H
  obtain ⟨q4, o4, H⟩ := ok_bind H
  obtain ⟨q5, o5, H⟩ := ok_bind H
  obtain ⟨q6, o6, H⟩ := ok_bind H
  obtain ⟨q7, o7, H⟩ := ok_bind H
  obtain ⟨q8, o8, H⟩ := ok_bind H
  obtain ⟨q9, o9, H⟩ := ok_bind H
  obtain ⟨q10, o10, H⟩ := ok_bind H
  obtain ⟨q11, o11, H⟩ := ok_bind H
  -- the factors `b_z + 1`
  have hF : List.Forall₂ (fun z (x : Cell) => x.ty = .K ∧ M.k x.n = M.k (I.bn + 2 + z) + 1)
      (List.range (I.ln + 1)) (forN (I.ln + 1) (fun z => addK (kc (I.bn + 2 + z)) 1) q10).1 :=
    seqAll_res (fun z q hq => ⟨rfl, by
      have := linK_spec (k := 0) (k' := 1) (a := I.bn + 2 + z) (b := I.bn + 2 + z) hq
      rw [zero_mul, add_zero] at this; exact this⟩) _ q10 o11.1
  generalize (forN (I.ln + 1) (fun z => addK (kc (I.bn + 2 + z)) 1) q10).1 = qs at hF H
  rcases qs with _ | ⟨⟨qt, qn⟩, rest⟩
  · exact absurd hF (by simp)
  have hF' := hF
  rw [List.range_succ_eq_map] at hF'
  obtain ⟨⟨hqt, -⟩, -⟩ := List.forall₂_cons.mp hF'
  simp only at hqt; subst hqt
  obtain ⟨q12, o12, H⟩ := ok_bind H
  obtain ⟨q13, o13, H⟩ := ok_bind H
  obtain ⟨q14, o14, H⟩ := ok_bind H
  have hK : ∀ x ∈ rest, x.ty = .K := forall₂_right (List.forall₂_cons.mp hF').2
  have pc := prodChain_spec hZ rest qn q11 hK o12.1
  have e3 := mulAddK_spec (a := I.hd) (b := I.hd) (d := I.hd) o3.1
  have a4 := assert0K_spec (a := q2.k) (g := I.flag) o4.2
  have e5 := linK_spec (k := 0) (k' := 1) (a := I.hd) (b := I.hd) o5.1
  have e6 := mulAddK_spec (a := q4.k) (b := I.flag) (d := zn) o6.1
  have a8 := assert0K_spec (a := I.bn + 2 + I.ln + 1) (g := I.flag) o8.2
  have e9 := mulAddK_spec (a := I.bn + 2 + I.ln) (b := I.bn + 2 + I.ln + 2) (d := zn) o9.1
  have a10 := assert0K_spec (a := q8.k) (g := I.flag) o10.2
  have a13 := ok_assert0 pc.1 o13
  have hmap := map_of_forall₂ (g := fun x : Cell => M.k x.n)
    (f := fun z => M.k (I.bn + 2 + z) + 1) (hF.imp fun _ _ h => h.2)
  refine ⟨fun l hl => ?_, fun l hl => ?_, ?_, fun h0 l hl => ?_, ?_, ?_, ?_, fun l hl => ?_⟩
  · obtain ⟨q, hq⟩ := ok_forN o1 l hl
    exact ok_assertEq hq hg
  · obtain ⟨q, hq⟩ := ok_forN o2 l hl
    exact ok_assertEq hq hg
  · rw [hg, one_mul, e3] at a4; exact a4
  · obtain ⟨q, hq⟩ := ok_forN o7 l hl
    have := assert0K_spec (a := I.hd + 5 + l) (g := q5.k) hq.2
    rwa [e6, e5, h0, hg, hZ, zero_mul, zero_add, add_zero, zero_add, one_mul, one_mul] at this
  · rwa [hg, one_mul] at a8
  · rwa [hg, one_mul, e9, hZ, add_zero] at a10
  · rw [hg, one_mul, pc.2, ← List.prod_cons] at a13
    rw [← hmap]; exact a13
  · obtain ⟨q, hq⟩ := ok_forN o14 l hl
    exact ok_sel hq hg

/-- **`σ_leaf' = b'·σ_leaf`** on all 597 lanes. -/
theorem gSl_spec {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : SegsHold c M p (gSl I p).2)
    (hA : SegsAssert M p (gSl I p).2) (hg : M.k I.flag = 1) :
    ∀ k < 597, M.k I.hd * M.k (I.sl + k) + M.k (I.hd + 18 + k) = 0 := by
  simp only [gSl, hold_bind, assert_bind] at h hA
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := h
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := hA
  have e0 := sl_loop h0 a0 hg
  have e1 := sl_loop h1 a1 hg
  have e2 := sl_loop h2 a2 hg
  have e3 := sl_loop h3 a3 hg
  have e4 := sl_loop h4 a4 hg
  intro k hk
  by_cases k0 : k < 512
  · simpa using e0 k (by norm_num; omega)
  by_cases k1 : k < 576
  · have := e1 (k - 512) (by norm_num; omega)
    rwa [show I.sl + 512 + (k - 512) = I.sl + k by omega,
      show I.hd + 18 + 512 + (k - 512) = I.hd + 18 + k by omega] at this
  by_cases k2 : k < 592
  · have := e2 (k - 576) (by norm_num; omega)
    rwa [show I.sl + 576 + (k - 576) = I.sl + k by omega,
      show I.hd + 18 + 576 + (k - 576) = I.hd + 18 + k by omega] at this
  by_cases k3 : k < 596
  · have := e3 (k - 592) (by norm_num; omega)
    rwa [show I.sl + 592 + (k - 592) = I.sl + k by omega,
      show I.hd + 18 + 592 + (k - 592) = I.hd + 18 + k by omega] at this
  · have := e4 0 (by norm_num)
    rwa [show I.sl + 596 + 0 = I.sl + k by omega,
      show I.hd + 18 + 596 + 0 = I.hd + 18 + k by omega] at this

end Lvm.QSig
