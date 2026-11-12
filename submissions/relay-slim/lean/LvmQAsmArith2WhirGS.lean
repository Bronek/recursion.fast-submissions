-- New for lvm (HAR-WH): the circuit specs of the phase 8–9 level gadgets (`LvmQAsmArith2WhirG`):
-- loads, round polynomials, fold and tail rounds, glue, row folds with the enforced sum, column
-- weights, constants, the final weight sum, copies and preloads (QA2's `LvmQWhir*` lemmas wired).
import LvmQAsmArith2WhirG

/-!
# Phases 8–9: specs of the level gadgets

Every spec has the form `SegsHold c M p (g p).2 → (g p).1 = F's value` (the frame property of QL's
builder): `ldE_spec` (= `feAt`), `pev_spec` (= `polyEval`), `rdQ_spec` (= `sumcheckRoundPoly 3`),
`roundsG_spec` (= `frQ`), `tailG_spec` (= `tlT`), `glueG_spec` (= `glue`'s update), `foldsG_spec`
(= `Σ λ^q fold_q`), `colWG_spec` (= `inducedWeight` by `inducedWeight_pow`), `iwConsts_spec`,
`wsumG_spec`, `copiesG_spec`, `preloadG_spec`; pointer lemmas `*_out`, `*_adv`, `adv_e_le`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build

variable {c : Ctx} {M : Mem}

/-- A quadratic's three cells' values. -/
def qv (M : Mem) (q : Cell × Cell × Cell) : List FE := [q.1.val M, q.2.1.val M, q.2.2.val M]

/-! ## Pointers -/

theorem adv_e_le (p : Ptr) (δ : List Seg) : p.e ≤ (p.adv δ).e := Nat.le_add_right _ _
theorem adv_k_le (p : Ptr) (δ : List Seg) : p.k ≤ (p.adv δ).k := Nat.le_add_right _ _

theorem ldE_out (v : Nat) (p : Ptr) : (ldEW v p).1 = ec p.e := rfl

theorem ldEW_adv (v : Nat) (p : Ptr) : p.adv (ldEW v p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [ldEW, loadE, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

/-! ## Loads, round polynomials -/

theorem ldE_spec {sig : ByteArray} {T v : Nat} {p : Ptr} (hS : Lvm.Q1.Streamed M sig T) (hv : v + 2 < T)
    (h : SegsHold c M p (ldEW v p).2) : (ldEW v p).1.val M = feAt sig (8 * v) := by
  rw [ldEW, loadE_spec h]
  exact Lvm.Q1.load_feAt hS hv

theorem pev_spec {q : Cell × Cell × Cell} {cc : Cell} {p : Ptr} (h : SegsHold c M p (pev q cc p).2) :
    (pev q cc p).1.val M = polyEval (qv M q) (cc.val M) := by
  simp only [pev, bind_apply] at h ⊢
  rw [segsHold_append] at h
  rw [mulAdd_spec h.2, mulAdd_spec h.1]
  simp only [qv, polyEval, List.foldr_cons, List.foldr_nil]
  ring

theorem rdQ_spec {sig : ByteArray} {T v : Nat} {cl : Cell} {p : Ptr} (hS : Lvm.Q1.Streamed M sig T)
    (hv : v + 10 < T) (h : SegsHold c M p (rdQ v cl p).2) :
    qv M (rdQ v cl p).1 = [feAt sig (8 * v + 40), cl.val M + feAt sig (8 * v + 64), feAt sig (8 * v + 64)] := by
  simp only [rdQ, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  have h0 := ldE_spec hS (by omega) h.1
  have h2 := ldE_spec hS (by omega) h.2.1
  have h1 := lin_spec h.2.2
  simp only [add] at h1 ⊢
  simp only [qv]
  rw [h1, h0, h2, ofK_one, ofK_zero, one_mul, add_zero,
    show 8 * (v + 5) = 8 * v + 40 by ring, show 8 * (v + 8) = 8 * v + 64 by ring]

theorem roundsG_spec {sig : ByteArray} {T pc : Nat} (hS : Lvm.Q1.Streamed M sig T) :
    ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr), V + 15 * n + 4 < T →
      (∀ j < n, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40)) →
      SegsHold c M p (roundsG pc f V n q p).2 → qv M (roundsG pc f V n q p).1 = frQ sig (8 * V) n (qv M q)
  | 0, f, V, q, p, _, _, _ => by simp [roundsG, pure_apply, frQ]
  | n + 1, f, V, q, p, hT, hc, h => by
    simp only [roundsG, bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    have hcl := pev_spec h.1
    have hq := rdQ_spec hS (by omega) h.2.1
    rw [roundsG_spec hS n (f + 1) (V + 15) _ _ (by omega) (fun j hj => by
      rw [show pc + (f + 1) + j = pc + f + (j + 1) by ring, hc (j + 1) (by omega)]
      congr 1; ring) h.2.2, hq, hcl]
    have h0 := hc 0 (by omega)
    simp only [Nat.add_zero, Nat.mul_zero] at h0
    simp only [frQ, Cell.val_E, h0]
    rw [show 8 * (V + 15) = 8 * V + 120 by ring, show 8 * (V + 9) + 40 = 8 * V + 112 by ring,
      show 8 * (V + 9) + 64 = 8 * V + 136 by ring]

theorem tailG_spec {sig : ByteArray} {T pc : Nat} (hS : Lvm.Q1.Streamed M sig T) :
    ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr), 1 ≤ n → V + 15 * (n - 1) + 8 < T →
      (∀ j < n, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40)) →
      SegsHold c M p (tailG pc f V n q p).2 → (tailG pc f V n q p).1.val M = tlT sig (8 * V) n (qv M q)
  | 0, _, _, _, _, h1, _, _, _ => absurd h1 (by omega)
  | 1, f, V, q, p, _, _, hc, h => by
    simp only [tailG] at h ⊢
    rw [pev_spec h]
    have h0 := hc 0 (by omega)
    simp only [Nat.add_zero, Nat.mul_zero] at h0
    simp only [tlT, Cell.val_E, h0]
  | n + 2, f, V, q, p, _, hT, hc, h => by
    simp only [tailG, bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    have hcl := pev_spec h.1
    have hq := rdQ_spec hS (by omega) h.2.1
    rw [tailG_spec hS (n + 1) (f + 1) (V + 15) _ _ (by omega) (by omega) (fun j hj => by
      rw [show pc + (f + 1) + j = pc + f + (j + 1) by ring, hc (j + 1) (by omega)]
      congr 1; ring) h.2.2, hq, hcl]
    have h0 := hc 0 (by omega)
    simp only [Nat.add_zero, Nat.mul_zero] at h0
    simp only [tlT, Cell.val_E, h0]
    rw [show 8 * (V + 15) = 8 * V + 120 by ring, show 8 * (V + 9) + 40 = 8 * V + 112 by ring,
      show 8 * (V + 9) + 64 = 8 * V + 136 by ring]

theorem glueG_spec {lam : Cell} {q i : Cell × Cell × Cell} {p : Ptr} (h : SegsHold c M p (glueG lam q i p).2) :
    qv M (glueG lam q i p).1 = List.zipWith (fun a b => a + 1 * lam.val M * b) (qv M q) (qv M i) := by
  simp only [glueG, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  simp only [qv, List.zipWith_cons_cons, List.zipWith_nil_left]
  rw [mulAdd_spec h.1, mulAdd_spec h.2.1, mulAdd_spec h.2.2]
  simp only [List.cons.injEq, and_true]
  refine ⟨by ring, by ring, by ring⟩

/-! ## Row folds and the enforced sum -/

theorem rowFold0_cell (l a lb S er : Nat) (p : Ptr) (q : Nat) :
    (rowFold0 l a lb S er p).1 q = ec (p.e + 2 ^ (l + a) + q) := by
  simp only [rowFold0, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append]
  rw [loop_adv]
  simp [LoopOut.cell, loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at]

theorem rowFoldE_cell (l a lb S er : Nat) (p : Ptr) (q : Nat) :
    (rowFoldE l a lb S er p).1 q = ec (p.e + 2 * 2 ^ (l + a) + q) := by
  simp only [rowFoldE, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append]
  rw [loop_adv]
  simp [LoopOut.cell, loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at]

/-- A chunk's row folds (`rowFold0` at level 0, else `rowFoldE`): affine cells, `F`'s folds. -/
theorem rowCh_spec {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {lvl0 : Bool}
    {l a lb S er : Nat} (eq : Array FE)
    (he : ∀ k < 2 ^ l, M.e (er + k) = eq.getD (if lvl0 then 2 ^ l - 1 - k else k) 0)
    {p : Ptr} (hp : 1 ≤ p.e)
    (h : SegsHold c M p ((if lvl0 then rowFold0 l a lb S er else rowFoldE l a lb S er) p).2) :
    (∀ i, ((if lvl0 then rowFold0 l a lb S er else rowFoldE l a lb S er) p).1 i =
        ec ((((if lvl0 then rowFold0 l a lb S er else rowFoldE l a lb S er) p).1 0).n + i)) ∧
    ∀ i < 2 ^ a, lb + S * i + 3 * 2 ^ l + 2 < T →
      (((if lvl0 then rowFold0 l a lb S er else rowFoldE l a lb S er) p).1 i).val M =
        (if lvl0 then foldRow0 sig eq (8 * (lb + S * i)) (2 ^ l)
          else foldRowE sig eq (8 * (lb + S * i)) (2 ^ l)) := by
  cases lvl0
  · simp only [Bool.false_eq_true, ite_false] at h he ⊢
    refine ⟨fun i => by rw [rowFoldE_cell, rowFoldE_cell]; simp, fun i hi hT => ?_⟩
    refine rowFoldE_eq h hp sig eq hi (fun k hk c' hc => ?_) he
    rw [hS _ (by omega)]; rfl
  · simp only [ite_true] at h he ⊢
    refine ⟨fun i => by rw [rowFold0_cell, rowFold0_cell]; simp, fun i hi hT => ?_⟩
    refine rowFold0_eq h hp sig eq hi (fun k hk => ?_) he
    rw [hS _ (by omega)]; rfl

/-- A chunk of `min A (t − q₀)` terms followed by the rest from `q₀ + A` is the sum over `[q₀, t)`. -/
theorem sum_chunk (G : Nat → FE) (q₀ A t : Nat) (h : q₀ < t) :
    ∑ i ∈ Finset.range (min A (t - q₀)), G (q₀ + i) + ∑ q ∈ Finset.Ico (q₀ + A) t, G q =
      ∑ q ∈ Finset.Ico q₀ t, G q := by
  rcases Nat.le_total A (t - q₀) with hA | hA
  · rw [min_eq_left hA, ← Finset.sum_Ico_consecutive G (Nat.le_add_right q₀ A) (by omega),
      Finset.sum_Ico_eq_sum_range G q₀ (q₀ + A), Nat.add_sub_cancel_left]
  · rw [min_eq_right hA, Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero,
      Finset.sum_Ico_eq_sum_range]

theorem chunks_tail {q₀ a t : Nat} {as : List Nat} (ht : t ≤ q₀ + ((a :: as).map (2 ^ ·)).sum)
    (hch : ∀ i < (a :: as).length, q₀ + (((a :: as).take i).map (2 ^ ·)).sum < t) :
    q₀ < t ∧ t ≤ q₀ + 2 ^ a + (as.map (2 ^ ·)).sum ∧
      ∀ i < as.length, q₀ + 2 ^ a + ((as.take i).map (2 ^ ·)).sum < t := by
  refine ⟨by simpa using hch 0 (by simp), by simp at ht; omega, fun i hi => ?_⟩
  have := hch (i + 1) (by simp; omega)
  simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this
  omega

theorem foldsG_cons (lvl0 : Bool) (l lb S er lp t : Nat) (z : Cell) (q₀ a : Nat) (as : List Nat) :
    foldsG lvl0 l lb S er lp t z q₀ (a :: as) =
      (if lvl0 then rowFold0 l a (lb + S * q₀) S er else rowFoldE l a (lb + S * q₀) S er) >>= fun fc =>
        dotG a (min (2 ^ a) (t - q₀)) (lp + q₀) 1 (fc 0).n 1 >>= fun d =>
          foldsG lvl0 l lb S er lp t z (q₀ + 2 ^ a) as >>= fun rest => add d rest := by
  cases lvl0 <;> rfl

theorem foldsG_spec {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {lvl0 : Bool}
    {l lb S er lp t : Nat} {z : Cell} (hz : z.val M = 0) (eq : Array FE) (lam : FE)
    (he : ∀ k < 2 ^ l, M.e (er + k) = eq.getD (if lvl0 then 2 ^ l - 1 - k else k) 0)
    (hlp : ∀ q < t, M.e (lp + q) = lam ^ q) (hT : ∀ q < t, lb + S * q + 3 * 2 ^ l + 2 < T) :
    ∀ (as : List Nat) (q₀ : Nat) (p : Ptr), 1 ≤ p.e → t ≤ q₀ + (as.map (2 ^ ·)).sum →
      (∀ i < as.length, q₀ + ((as.take i).map (2 ^ ·)).sum < t) →
      SegsHold c M p (foldsG lvl0 l lb S er lp t z q₀ as p).2 →
      (foldsG lvl0 l lb S er lp t z q₀ as p).1.val M = ∑ q ∈ Finset.Ico q₀ t, lam ^ q *
        (if lvl0 then foldRow0 sig eq (8 * (lb + S * q)) (2 ^ l) else foldRowE sig eq (8 * (lb + S * q)) (2 ^ l))
  | [], q₀, p, _, ht, _, _ => by
    simp only [foldsG, pure_apply, hz]
    rw [Finset.Ico_eq_empty (by simpa using ht), Finset.sum_empty]
  | a :: as, q₀, p, hp, ht, hch, h => by
    obtain ⟨hq₀, ht', hch'⟩ := chunks_tail ht hch
    rw [foldsG_cons] at h ⊢
    simp only [bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append, segsHold_append] at h
    obtain ⟨hc, hd, hr, ha⟩ := h
    have hcs := rowCh_spec (lb := lb + S * q₀) hS eq he hp hc
    have hd' := dotG_spec hd (le_trans hp (adv_e_le _ _)) (Nat.le_min.mpr ⟨Nat.one_le_two_pow, by omega⟩)
      (min_le_left _ _)
    have hr' := foldsG_spec hS hz eq lam he hlp hT as (q₀ + 2 ^ a) _
      (le_trans hp (le_trans (adv_e_le _ _) (adv_e_le _ _))) ht' hch' hr
    simp only [add] at ha ⊢
    rw [lin_spec ha, hd', hr', ofK_one, ofK_zero, one_mul, add_zero]
    rw [← sum_chunk _ q₀ (2 ^ a) t hq₀]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hit : q₀ + i < t := by have := min_le_right (2 ^ a) (t - q₀); omega
    rw [Nat.one_mul, Nat.add_assoc lp, hlp _ hit]
    congr 1
    rw [← Cell.val_E, ← (hcs.1 i), hcs.2 i (lt_of_lt_of_le hi' (min_le_left _ _))
      (by have := hT _ hit; rw [Nat.mul_add] at this; omega),
      show lb + S * q₀ + S * i = lb + S * (q₀ + i) by ring]

/-! ## Column weights -/

theorem colWG_spec {cs : List Nat} {ptb ib rb lp xb t : Nat} {z : Cell} {zk : Nat} (hzE : z.ty = .E)
    (hz : z.val M = 0) (hzk : M.k zk = 0) (m : Nat) (qs : List Nat) (lam : FE) (pt : List FE)
    (hκ : csum cs = pt.length)
    (hpt : ∀ k < pt.length, M.e (ptb + k) = pt.getD k 0)
    (hI : ∀ k < pt.length, FE.ofK (M.k (ib + k)) = (iwInvs m).getD k 0)
    (hR : ∀ k < pt.length, FE.ofK (M.k (rb + k)) = (iwRoots m).getD k 0)
    (hw : ∀ q < t, M.e (lp + q) = lam ^ q) (hx : ∀ q < t, FE.ofK (M.k (xb + q)) = eOfNat (qs.getD q 0)) :
    ∀ (as : List Nat) (q₀ : Nat) (p : Ptr), 1 ≤ p.e → t ≤ q₀ + (as.map (2 ^ ·)).sum →
      (∀ i < as.length, q₀ + ((as.take i).map (2 ^ ·)).sum < t) →
      SegsHold c M p (colWG cs ptb ib rb lp xb t z zk q₀ as p).2 →
      (colWG cs ptb ib rb lp xb t z zk q₀ as p).1.val M = ∑ q ∈ Finset.Ico q₀ t,
        (iwSeq (iwRoots m) (iwInvs m) pt (lam ^ q) (eOfNat (qs.getD q 0)) pt.length).1
  | [], q₀, p, _, ht, _, _ => by
    simp only [colWG, pure_apply, hz]
    rw [Finset.Ico_eq_empty (by simpa using ht), Finset.sum_empty]
  | a :: as, q₀, p, hp, ht, hch, h => by
    obtain ⟨hq₀, ht', hch'⟩ := chunks_tail ht hch
    simp only [colWG, bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    obtain ⟨hc, hr, ha⟩ := h
    have hzn : M.e z.n = 0 := by
      obtain ⟨zt, zn⟩ := z
      simp only at hzE
      subst hzE
      exact hz
    have hcw := colWeight_spec hc hzn hzk (Nat.le_min.mpr ⟨Nat.one_le_two_pow, by omega⟩) (min_le_left _ _) (iwRoots m) (iwInvs m) pt
      (hκ ▸ hpt) (hκ ▸ hI) (hκ ▸ hR)
    have hr' := colWG_spec hzE hz hzk m qs lam pt hκ hpt hI hR hw hx as (q₀ + 2 ^ a) _
      (le_trans hp (adv_e_le _ _)) ht' hch' hr
    simp only [add] at ha ⊢
    rw [lin_spec ha, hcw, hr', ofK_one, ofK_zero, one_mul, add_zero]
    rw [← sum_chunk _ q₀ (2 ^ a) t hq₀]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hit : q₀ + i < t := by have := min_le_right (2 ^ a) (t - q₀); omega
    rw [Nat.add_assoc lp, hw _ hit, Nat.add_assoc xb, hx _ hit, hκ]

/-! ## `F`'s sums -/

theorem powers_len_wh (b : FE) (n : Nat) : (powers b n).length = n := by
  have key : ∀ (acc : FE) (n : Nat), (powersFrom acc b n).length = n := by
    intro acc n
    induction n generalizing acc with
    | zero => rfl
    | succ n ih => simp [powersFrom, ih]
  exact key 1 n

theorem inducedWeight_pow (m : Nat) (qs : List Nat) (lam : FE) (pt : List FE) :
    inducedWeight m qs (powers lam qs.length) pt = ∑ q ∈ Finset.range qs.length,
      (iwSeq (iwRoots m) (iwInvs m) pt (lam ^ q) (eOfNat (qs.getD q 0)) pt.length).1 := by
  rw [inducedWeight_sum m qs _ pt (powers_len_wh _ _)]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [powers_getD lam qs.length q (Finset.mem_range.mp hq)]

theorem dot_powers (lam : FE) (l : List FE) :
    Lvm.dot (powers lam l.length) l = ∑ q ∈ Finset.range l.length, lam ^ q * l.getD q 0 := by
  rw [dot_eq_sum _ _ (powers_len_wh _ _), powers_len_wh]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [powers_getD lam l.length q (Finset.mem_range.mp hq)]

/-! ## Constants -/

theorem constK_adv (v : FK) (g : Cell) (p : Ptr) : p.adv (const .K v g p).2 = ⟨p.k + 1, p.e⟩ := by
  simp [const, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem kconsts_adv (g : Cell) (hg : g.ty = .K) : ∀ (vs : List FK) (p : Ptr),
    p.adv (kconsts g vs p).2 = ⟨p.k + vs.length, p.e⟩
  | [], p => by simp [kconsts, pure_apply]
  | v :: vs, p => by
    simp only [kconsts, bind_apply, Ptr.adv_append, constK_adv, kconsts_adv g hg vs, List.length_cons]
    congr 1; omega

theorem kconsts_spec {g : Cell} (hg : g.ty = .K) : ∀ (vs : List FK) (p : Ptr), SegsHold c M p (kconsts g vs p).2 →
    ∀ k < vs.length, M.k (p.k + k) = vs.getD k 0
  | [], _, _, k, hk => absurd hk (by simp)
  | v :: vs, p, h, k, hk => by
    simp only [kconsts, bind_apply] at h
    rw [segsHold_append] at h
    rcases k with _ | k
    · have e := lin_spec h.1
      have hv : (const .K v g p).1.val M = FE.ofK (M.k p.k) := rfl
      simp only [const] at e hv
      rw [hv, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add] at e
      simpa using ofK_inj e
    · have := kconsts_spec hg vs _ (by rw [constK_adv] at h; exact h.2) k (by simpa using hk)
      simp only [List.getD_cons_succ]
      rw [← this]; congr 1; show p.k + (k + 1) = p.k + 1 + k; omega

theorem iwConsts_adv (m : Nat) {g : Cell} (hg : g.ty = .K) (p : Ptr) :
    p.adv (iwConsts m g p).2 = ⟨p.k + 2 * m, p.e⟩ := by
  simp only [iwConsts, bind_apply, Ptr.adv_append, kconsts_adv g hg, List.length_map, List.length_range]
  congr 1; omega

theorem iwConsts_spec (m : Nat) {g : Cell} (hg : g.ty = .K) {p : Ptr} (h : SegsHold c M p (iwConsts m g p).2) :
    ∀ k < m, FE.ofK (M.k (p.k + k)) = (iwRoots m).getD k 0 ∧ FE.ofK (M.k (p.k + m + k)) = (iwInvs m).getD k 0 := by
  simp only [iwConsts, bind_apply] at h
  rw [segsHold_append] at h
  intro k hk
  have h1 := kconsts_spec hg _ p h.1 k (by simpa using hk)
  have h2 := kconsts_spec hg _ _ h.2 k (by simpa using hk)
  rw [kconsts_adv g hg] at h2
  simp only [List.length_map, List.length_range] at h2
  have hr := iwRoots_isK m k
  have hi := iwInvs_isK m k
  refine ⟨?_, ?_⟩
  · rw [h1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some]
    rw [← List.getD_eq_getElem?_getD]; exact hr
  · rw [h2]; simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some]
    rw [← List.getD_eq_getElem?_getD]; exact hi

/-! ## The final weight sum -/

theorem wsumG_spec : ∀ (gl : List (Cell × Cell)) (w : Cell) (p : Ptr), SegsHold c M p (wsumG w gl p).2 →
    (wsumG w gl p).1.val M = gl.foldl (fun acc x => acc + x.1.val M * x.2.val M) (w.val M)
  | [], w, p, _ => by simp [wsumG, pure_apply]
  | (lam, W) :: gl, w, p, h => by
    simp only [wsumG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [wsumG_spec gl _ _ h.2, mulAdd_spec h.1, List.foldl_cons]
    congr 1
    ring

/-! ## Copies and preloads -/

theorem seqCopy_adv : ∀ (cells : List Cell), (∀ x ∈ cells, x.ty = .E) → ∀ p : Ptr,
    p.adv (seqAll (cells.map copy) p).2 = ⟨p.k, p.e + cells.length⟩
  | [], _, p => by simp [seqAll, pure_apply]
  | x :: cells, hE, p => by
    obtain ⟨xt, xn⟩ := x
    have hx : xt = .E := hE ⟨xt, xn⟩ (by simp)
    subst hx
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, Ptr.adv_append, QRing.copyE_adv,
      seqCopy_adv cells (fun y hy => hE y (List.mem_cons_of_mem _ hy))]
    simp only [List.length_cons, Ptr.mk.injEq, true_and]; omega

theorem seqCopy_spec : ∀ (cells : List Cell), (∀ x ∈ cells, x.ty = .E) → ∀ p : Ptr,
    SegsHold c M p (seqAll (cells.map copy) p).2 → ∀ i < cells.length, M.e (p.e + i) = (cells.getD i default).val M
  | [], _, _, _, i, hi => absurd hi (by simp)
  | x :: cells, hE, p, h, i, hi => by
    obtain ⟨xt, xn⟩ := x
    have hx : xt = .E := hE ⟨xt, xn⟩ (by simp)
    subst hx
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, segsHold_append] at h
    rcases i with _ | i
    · simpa using (QRing.copyE_spec h.1).2
    · have := seqCopy_spec cells (fun y hy => hE y (List.mem_cons_of_mem _ hy)) _ (by rw [QRing.copyE_adv] at h; exact h.2) i
        (by simpa using hi)
      simp only [List.getD_cons_succ]
      rw [← this]; congr 1; show p.e + (i + 1) = p.e + 1 + i; omega

theorem copiesG_adv (cells : List Cell) (hE : ∀ x ∈ cells, x.ty = .E) (p : Ptr) :
    p.adv (copiesG cells p).2 = ⟨p.k, p.e + cells.length⟩ := by
  simp only [copiesG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil]
  exact seqCopy_adv cells hE p

theorem copiesG_spec {cells : List Cell} (hE : ∀ x ∈ cells, x.ty = .E) {p : Ptr} (h : SegsHold c M p (copiesG cells p).2) :
    (copiesG cells p).1 = p.e ∧ ∀ i < cells.length, M.e (p.e + i) = (cells.getD i default).val M := by
  simp only [copiesG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil] at h ⊢
  exact ⟨by first | rfl | trivial, seqCopy_spec cells hE p h⟩

theorem seqLd_adv : ∀ (ls : List Nat) (p : Ptr), p.adv (seqAll (ls.map ldEW) p).2 = ⟨p.k, p.e + ls.length⟩
  | [], p => by simp [seqAll, pure_apply]
  | v :: ls, p => by
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, Ptr.adv_append, ldEW_adv, seqLd_adv ls]
    simp only [List.length_cons, Ptr.mk.injEq, true_and]; omega

theorem seqLd_spec {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) : ∀ (ls : List Nat) (p : Ptr),
    (∀ v ∈ ls, v + 2 < T) → SegsHold c M p (seqAll (ls.map ldEW) p).2 →
    ∀ i < ls.length, M.e (p.e + i) = feAt sig (8 * ls.getD i 0)
  | [], _, _, _, i, hi => absurd hi (by simp)
  | v :: ls, p, hT, h, i, hi => by
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, segsHold_append] at h
    rcases i with _ | i
    · have := ldE_spec hS (hT v (by simp)) h.1
      rw [ldE_out] at this
      simpa using this
    · have := seqLd_spec hS ls _ (fun w hw => hT w (by simp [hw])) (by rw [ldEW_adv] at h; exact h.2) i
        (by simpa using hi)
      simp only [List.getD_cons_succ]
      rw [← this]; congr 1; show p.e + (i + 1) = p.e + 1 + i; omega

theorem preloadG_adv (ls : List Nat) (p : Ptr) : p.adv (preloadG ls p).2 = ⟨p.k, p.e + ls.length⟩ := by
  simp only [preloadG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil]
  exact seqLd_adv ls p

theorem preloadG_spec {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {ls : List Nat} {p : Ptr}
    (hT : ∀ v ∈ ls, v + 2 < T) (h : SegsHold c M p (preloadG ls p).2) :
    (preloadG ls p).1 = p.e ∧ ∀ i < ls.length, M.e (p.e + i) = feAt sig (8 * ls.getD i 0) := by
  simp only [preloadG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil] at h ⊢
  exact ⟨by first | rfl | trivial, seqLd_spec hS ls p hT h⟩

/-! ## Pointers of the straight-line gadgets -/

theorem pev_adv (q : Cell × Cell × Cell) (cc : Cell) (p : Ptr) : p.adv (pev q cc p).2 = ⟨p.k, p.e + 2⟩ := by
  simp [pev, bind_apply, mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem rdQ_adv (v : Nat) (cl : Cell) (p : Ptr) : p.adv (rdQ v cl p).2 = ⟨p.k, p.e + 3⟩ := by
  simp [rdQ, bind_apply, pure_apply, ldEW, loadE, add, lin, jn, rowRes, Ptr.adv, segsW, Seg.w, Row.w,
    Row.writes]

theorem glueG_adv (lam : Cell) (q i : Cell × Cell × Cell) (p : Ptr) : p.adv (glueG lam q i p).2 = ⟨p.k, p.e + 3⟩ := by
  simp [glueG, bind_apply, pure_apply, mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem wsumG_adv : ∀ (gl : List (Cell × Cell)) (w : Cell) (p : Ptr), p.adv (wsumG w gl p).2 = ⟨p.k, p.e + gl.length⟩
  | [], w, p => by simp [wsumG, pure_apply]
  | (lam, W) :: gl, w, p => by
    simp only [wsumG, bind_apply, Ptr.adv_append]
    rw [wsumG_adv gl]
    simp [mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]; omega

theorem roundsG_adv (pc : Nat) : ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr),
    p.adv (roundsG pc f V n q p).2 = ⟨p.k, p.e + 5 * n⟩
  | 0, f, V, q, p => by simp [roundsG, pure_apply]
  | n + 1, f, V, q, p => by
    simp only [roundsG, bind_apply, Ptr.adv_append, pev_adv, rdQ_adv, roundsG_adv pc n]
    simp only [Ptr.mk.injEq, true_and]; omega

theorem tailG_adv (pc : Nat) : ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr), 1 ≤ n →
    p.adv (tailG pc f V n q p).2 = ⟨p.k, p.e + 5 * n - 3⟩
  | 0, _, _, _, _, h => absurd h (by omega)
  | 1, f, V, q, p, _ => by simp only [tailG, pev_adv, Ptr.mk.injEq, true_and]; omega
  | n + 2, f, V, q, p, _ => by
    simp only [tailG, bind_apply, Ptr.adv_append, pev_adv, rdQ_adv]
    rw [tailG_adv pc (n + 1) _ _ _ _ (by omega)]
    simp only [Ptr.mk.injEq, true_and]; omega

end Lvm.Har
