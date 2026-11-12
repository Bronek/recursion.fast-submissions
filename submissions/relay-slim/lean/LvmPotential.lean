-- WP-5 (FS). New for lvm (BLUEPRINT §7.3): the potential of the compiled verifier and its `step`
-- law. The shape (`1` on a bad log, else a sum over the forest's frontier) follows FR's `muG`
-- (`FRSoundnessDefs`); the per-node charge is leanVM's `esc` of the node's open group.
import LvmCompileCert

/-!
# The potential

For a knowledge certificate `K` and a node `I` (its group started at `I.st.hb`), the **group
term** is the escape probability of the open group from the node, for doom (charged when the group
started in doom) and for luck (charged when it started not lucky):

`gterm I = [D hb]·esc_D(h, p) + [¬B hb]·esc_{¬B}(h, p)`.

A node **leaves the frontier** when it continues its group (`Cont`: openings reach a challenge)
and its continuation, the query of its own answer, has been asked: its charge has passed to the
child. **`μ L = 1`** on a bad log, else **`S L = Σ_j term L j`**, the charge of each node.

**`mu_step`** (the `step` law at `ε + εB + badCount/2^256`): a fresh query is
* the continuation of a frontier node: its charge `g` moves to the child, whose average over the
  answer is `g` (a martingale: `esc` at a challenge is the average, `chal_sum`);
* a seed or a child with a message: a new group starts at a boundary, average at most `ε + εB`
  (`Cert.group`, `B_group`);
* anything else: no change;
and at most `badCount` answers make the log bad (charge `1`).
-/

namespace Lvm.FS

open LeanVM.Parameters LeanVM.Protocol.Compile RecursionFast
open scoped NNReal

namespace Scheme

variable {S : Scheme} {R : Digest → Wit → Prop}

open Classical in
/-- **The group term of a node.** -/
noncomputable def gterm (K : KCert S R) (I : S.NI) : ℝ≥0 :=
  (if (K.cert I.x).D I.st.hb then escR (K.cert I.x).D I.st.h I.st.p else 0) +
  (if ¬ K.B I.x I.st.hb then escR (fun h => ¬ K.B I.x h) I.st.h I.st.p else 0)

open Classical in
/-- The charge of node `j` with state `I` in the log `L`: `0` once its continuation is asked. -/
noncomputable def contrib (K : KCert S R) (L : Log) (j : ℕ) (I : S.NI) : ℝ≥0 :=
  if S.Cont I ∧ ∃ e, L[j]? = some e ∧ toQ e.2.toList ∈ L.map Prod.fst then 0 else gterm K I

open Classical in
/-- The charge of entry `j`: its node's, `0` if it is no node. -/
noncomputable def term (K : KCert S R) (L : Log) (j : ℕ) : ℝ≥0 :=
  if h : ∃ I, S.IsNode L j I then contrib K L j h.choose else 0

/-- The sum of the charges. -/
noncomputable def sumT (K : KCert S R) (L : Log) : ℝ≥0 :=
  ∑ j ∈ Finset.range L.length, term K L j

open Classical in
/-- **The potential.** -/
noncomputable def μ (K : KCert S R) (L : Log) : ℝ≥0 := if Bad L then 1 else sumT K L

/-- The error of the compiled verifier's knowledge state. -/
noncomputable def εFS (K : KCert S R) : ℝ≥0 := K.ε + K.εB + (badCount : ℝ≥0) / 2 ^ 256

/-! ## Programs after histories -/

theorem after_append {α : Type} (p : VerifierProgram α) (h l : List Ev) :
    p.after (h ++ l) = (p.after h).bind fun p' => p'.after l := by
  induction h generalizing p with
  | nil => simp [VerifierProgram.after]
  | cons e h ih =>
    cases p <;> cases e <;> simp only [List.cons_append, VerifierProgram.after, ih,
      Option.bind_none] <;> split_ifs <;> simp

theorem after_nil {α : Type} (p : VerifierProgram α) : p.after [] = some p := by
  cases p <;> rfl

theorem after_snoc {P p : VerifierProgram Bool} {h : List Ev} (hp : P.after h = some p) (e : Ev) :
    P.after (h ++ [e]) = p.after [e] := by
  rw [after_append, hp, Option.bind_some]

theorem boundary_snoc_read (h : List Ev) (x : E) : Boundary (h ++ [Ev.read x]) := by
  cases h with
  | nil => simp [Boundary]
  | cons a t =>
    unfold Boundary
    simp only [List.cons_append]
    rw [← List.cons_append, List.getLast?_concat]
    trivial

theorem boundary_snoc_commit (h : List Ev) (ht w : ℕ) (word : Word) :
    Boundary (h ++ [Ev.commit ht w word]) := by
  cases h with
  | nil => simp [Boundary]
  | cons a t =>
    unfold Boundary
    simp only [List.cons_append]
    rw [← List.cons_append, List.getLast?_concat]
    trivial

/-- The program state of an interactive state is reachable. -/
def Inv (P : VerifierProgram Bool) (s : PS) : Prop := P.Reachable s.h ∧ P.after s.h = some s.p

/-- The group of an interactive state started at a reachable boundary and reached it by openings. -/
def BdryOK (P : VerifierProgram Bool) (s : PS) : Prop :=
  ∃ pb, P.Reachable s.hb ∧ P.after s.hb = some pb ∧ Boundary s.hb ∧ Opens (pb, s.hb) (s.p, s.h)

theorem steps_inv {P : VerifierProgram Bool} {W : CapI → Word}
    (hW : ∀ ci, WellShaped ci.wd (W ci)) {s : PS} {m : Bytes} (hs : Inv P s) :
    ∀ y : PS × Bytes, S.Steps W (s, m) y → Inv P y.1 ∧ (y.2.length < m.length → BdryOK P y.1) := by
  intro y hy
  induction hy with
  | refl => exact ⟨hs, fun h => absurd h (lt_irrefl _)⟩
  | tail hxy hst ih =>
    obtain ⟨⟨hr, ha⟩, hbd⟩ := ih
    cases hst with
    | read hl =>
      rename_i k h hb caps msg
      have ha' := after_snoc ha (Ev.read (S.decE (msg.take 24)))
      simp only [VerifierProgram.after] at ha'
      refine ⟨⟨VerifierProgram.Reachable.read _ hr ha, ha'⟩, fun _ => ⟨_, VerifierProgram.Reachable.read _ hr ha, ha',
        boundary_snoc_read _ _, Relation.ReflTransGen.refl⟩⟩
    | commit hl =>
      rename_i ht w k h hb caps msg
      have hws : WellShaped w (W (S.capI ht w msg)) := hW _
      have ha' := after_snoc ha (Ev.commit ht w (W (S.capI ht w msg)))
      simp only [VerifierProgram.after] at ha'
      refine ⟨⟨VerifierProgram.Reachable.commit _ hr ha hws, ha'⟩, fun _ => ⟨_, VerifierProgram.Reachable.commit _ hr ha hws, ha',
        boundary_snoc_commit _ _ _ _, Relation.ReflTransGen.refl⟩⟩
    | «open» hr' =>
      rename_i i ps k h hb caps msg rows
      have ha' := after_snoc ha (Ev.query rows)
      simp only [VerifierProgram.after] at ha'
      refine ⟨⟨VerifierProgram.Reachable.query hr ha hr', ha'⟩, fun hlt => ?_⟩
      obtain ⟨pb, h1, h2, h3, h4⟩ := hbd hlt
      exact ⟨pb, h1, h2, h3, h4.tail (OpenStep.mk hr')⟩

/-- **A node's state is reachable.** -/
theorem node_inv {L : Log} {j : ℕ} {I : S.NI} (h : S.IsNode L j I) : Inv (S.P I.x) I.st := by
  induction h with
  | seed x hr h0 hq hcap => exact ⟨VerifierProgram.Reachable.nil, after_nil _⟩
  | child hI hij hi hq hcap hs ih =>
    rename_i i j I qi ai a msg k hs' hb caps
    obtain ⟨⟨hr, ha⟩, -⟩ := S.steps_inv (S.wellShaped_wordOf L) ih _ hs
    have ha' := after_snoc ha (Ev.sample (S.chal a))
    simp only [VerifierProgram.after] at ha'
    exact ⟨VerifierProgram.Reachable.sample _ hr ha, ha'⟩

/-! ## Group bounds -/

theorem escD_le (K : KCert S R) {x : S.Stmt} {hb : List Ev} {pb : VerifierProgram Bool}
    (hr : (S.P x).Reachable hb) (hbd : Boundary hb) (ha : (S.P x).after hb = some pb)
    (hg : (∃ k, pb = .sample k) ∨ (∃ i ps k, pb = .query i ps k)) (hD : (K.cert x).D hb) :
    escR (K.cert x).D hb pb ≤ K.ε := by
  have h1 := (K.cert x).group hr hbd ha hg hD
  rw [← coe_escR] at h1
  exact ENNReal.coe_le_coe.mp (h1.trans (K.cert_ε x hb hr hbd hD))

theorem escB_le (K : KCert S R) {x : S.Stmt} {hb : List Ev} {pb : VerifierProgram Bool}
    (hr : (S.P x).Reachable hb) (hbd : Boundary hb) (ha : (S.P x).after hb = some pb)
    (hg : (∃ k, pb = .sample k) ∨ (∃ i ps k, pb = .query i ps k)) (hB : ¬ K.B x hb) :
    escR (fun h => ¬ K.B x h) hb pb ≤ K.εB := by
  have h1 := K.B_group hr hbd ha hg hB
  rw [← coe_escR] at h1
  exact ENNReal.coe_le_coe.mp h1

/-- An escape probability at a point where the group has ended inside the predicate is `0`. -/
theorem escR_end_zero {G : List Ev → Prop} {h : List Ev} {p : VerifierProgram Bool}
    (hg : ¬ ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k))) (hG : G h) : escR G h p = 0 := by
  classical
  cases p with
  | sample k => exact absurd (Or.inl ⟨k, rfl⟩) hg
  | query i ps k => exact absurd (Or.inr ⟨i, ps, k, rfl⟩) hg
  | ret b => cases b <;> simp [escR, hG]
  | fail => simp [escR]
  | read k => simp [escR, hG]
  | grind b k => simp [escR, hG]
  | commit ht w k => simp [escR, hG]

open Classical in
/-- **A group started at a reachable boundary** charges at most `ε + εB`. -/
theorem group_le (K : KCert S R) {x : S.Stmt} {hb : List Ev} {pb : VerifierProgram Bool}
    (hr : (S.P x).Reachable hb) (hbd : Boundary hb) (ha : (S.P x).after hb = some pb) :
    (if (K.cert x).D hb then escR (K.cert x).D hb pb else 0) +
      (if ¬ K.B x hb then escR (fun h => ¬ K.B x h) hb pb else 0) ≤ K.ε + K.εB := by
  by_cases hD : (K.cert x).D hb <;> by_cases hB : K.B x hb <;>
    simp only [hD, hB, ite_true, ite_false, not_true_eq_false, not_false_eq_true, zero_add, add_zero]
  all_goals by_cases hg : (∃ k, pb = .sample k) ∨ (∃ i ps k, pb = .query i ps k)
  · exact (escD_le K hr hbd ha hg hD).trans le_self_add
  · rw [escR_end_zero hg hD]; exact zero_le
  · exact add_le_add (escD_le K hr hbd ha hg hD) (escB_le K hr hbd ha hg hB)
  · rw [escR_end_zero hg hD, escR_end_zero (G := fun h => ¬ K.B x h) hg hB, zero_add]
    exact zero_le
  · exact zero_le
  · exact zero_le
  · exact (escB_le K hr hbd ha hg hB).trans le_add_self
  · rw [escR_end_zero (G := fun h => ¬ K.B x h) hg hB]; exact zero_le

theorem card_E_nnreal : (Fintype.card E : ℝ≥0) = 2 ^ 192 := by
  rw [BF64.card_ext3]; norm_num

open Classical in
/-- **The martingale**: a child's group term, summed over the answer, is the group's escape
at the challenge. -/
theorem sum_child (K : KCert S R) (x : S.Stmt) (k : E → VerifierProgram Bool) (hs hb : List Ev)
    (caps : List CapI) :
    ∑ a : Digest, gterm K (S.childNI x k hs hb caps a) =
      2 ^ 256 * ((if (K.cert x).D hb then escR (K.cert x).D hs (.sample k) else 0) +
        (if ¬ K.B x hb then escR (fun h => ¬ K.B x h) hs (.sample k) else 0)) := by
  set F : E → ℝ≥0 := fun c =>
    (if (K.cert x).D hb then escR (K.cert x).D (hs ++ [Ev.sample c]) (k c) else 0) +
      (if ¬ K.B x hb then escR (fun h => ¬ K.B x h) (hs ++ [Ev.sample c]) (k c) else 0) with hF
  have h1 : ∑ a : Digest, gterm K (S.childNI x k hs hb caps a) = ∑ a : Digest, F (S.chal a) :=
    Finset.sum_congr rfl fun a _ => rfl
  rw [h1, S.chal_sum F, escR_sample, escR_sample, card_E_nnreal]
  have h256 : (2 : ℝ≥0) ^ 256 = 2 ^ 64 * 2 ^ 192 := by norm_num
  have hinv : (2 : ℝ≥0) ^ 192 * ((2 : ℝ≥0) ^ 192)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [hF, h256]
  by_cases hD : (K.cert x).D hb <;> by_cases hB : K.B x hb <;>
    simp only [hD, hB, ite_true, ite_false, not_true_eq_false, not_false_eq_true, add_zero,
      zero_add, Finset.sum_const_zero, mul_zero, Finset.sum_add_distrib, mul_add] <;>
    simp only [mul_assoc] <;> simp only [← mul_assoc ((2 : ℝ≥0) ^ 192), hinv, one_mul]

/-! ## Terms -/

theorem contrib_le_gterm (K : KCert S R) (L : Log) (j : ℕ) (I : S.NI) :
    contrib K L j I ≤ gterm K I := by
  unfold contrib; split_ifs <;> simp

theorem term_of_node (K : KCert S R) {L : Log} {j : ℕ} {I : S.NI} (hb : ¬ Bad L)
    (h : S.IsNode L j I) : term K L j = contrib K L j I := by
  unfold term
  rw [dite_eq_left ⟨I, h⟩, S.isNode_unique hb (Exists.choose_spec ⟨I, h⟩) h]

theorem term_of_not_node (K : KCert S R) {L : Log} {j : ℕ} (h : ¬ ∃ I, S.IsNode L j I) :
    term K L j = 0 := by
  unfold term; rw [dite_eq_right h]

open Classical in
/-- The charge an old entry gives up when the fresh query `q` is its continuation. -/
noncomputable def tdrop (K : KCert S R) (L : Log) (q : ByteArray) (j : ℕ) : ℝ≥0 :=
  if ∃ I, S.IsNode L j I ∧ S.Cont I ∧ ∃ e, L[j]? = some e ∧ toQ e.2.toList = q then term K L j
  else 0

theorem tdrop_le (K : KCert S R) (L : Log) (q : ByteArray) (j : ℕ) : tdrop K L q j ≤ term K L j := by
  unfold tdrop; split_ifs <;> simp

/-- **An old entry's charge** after a fresh good answer, plus what it gave up, is its old charge. -/
theorem term_old (K : KCert S R) {L : Log} {q : ByteArray} {a : Digest}
    (hb : ¬ Bad (L ++ [(q, a)])) (hq : q ∉ L.map Prod.fst) {j : ℕ} (hj : j < L.length) :
    term K (L ++ [(q, a)]) j + tdrop K L q j = term K L j := by
  classical
  have hbL := not_bad_of_append hb
  by_cases hn : ∃ I, S.IsNode L j I
  · obtain ⟨I, hI⟩ := hn
    have hI' := (S.isNode_append hb hj I).mpr hI
    obtain ⟨e, he⟩ : ∃ e, L[j]? = some e := ⟨L[j], List.getElem?_eq_getElem hj⟩
    have hget : (L ++ [(q, a)])[j]? = some e := by rw [List.getElem?_append_left hj]; exact he
    have hmem : toQ e.2.toList ∈ (L ++ [(q, a)]).map Prod.fst ↔
        toQ e.2.toList ∈ L.map Prod.fst ∨ toQ e.2.toList = q := by simp
    rw [term_of_node K hb hI', term_of_node K hbL hI]
    unfold tdrop contrib
    simp only [hget, he, Option.some.injEq, exists_eq_left', hmem]
    by_cases hc : S.Cont I
    · by_cases heq : toQ e.2.toList = q
      · have hnm : toQ e.2.toList ∉ L.map Prod.fst := heq ▸ hq
        have hex : ∃ I', S.IsNode L j I' ∧ S.Cont I' ∧ toQ e.2.toList = q := ⟨I, hI, hc, heq⟩
        rw [ite_eq_left hex, term_of_node K hbL hI]
        unfold contrib
        simp only [he, Option.some.injEq, exists_eq_left']
        simp [hc, heq]
      · have hex : ¬ ∃ I', S.IsNode L j I' ∧ S.Cont I' ∧ toQ e.2.toList = q :=
          fun ⟨_, _, _, h⟩ => heq h
        rw [ite_eq_right hex]
        simp [hc, heq]
    · have hex : ¬ ∃ I', S.IsNode L j I' ∧ S.Cont I' ∧ toQ e.2.toList = q := by
        rintro ⟨I', hI'', hc', -⟩
        rw [S.isNode_unique hbL hI'' hI] at hc'
        exact hc hc'
      rw [ite_eq_right hex]
      simp [hc]
  · have hn' : ¬ ∃ I, S.IsNode (L ++ [(q, a)]) j I := fun ⟨I, hI⟩ =>
      hn ⟨I, (S.isNode_append hb hj I).mp hI⟩
    rw [term_of_not_node K hn', term_of_not_node K hn]
    unfold tdrop
    rw [ite_eq_right (fun ⟨I, hI, _⟩ => hn ⟨I, hI⟩)]
    simp

/-! ## The laws -/

theorem mu_empty (K : KCert S R) : μ K [] = 0 := by
  unfold μ; rw [ite_eq_right not_bad_nil]; simp [sumT]

theorem mu_lt_one {K : KCert S R} {L : Log} (h : μ K L < 1) : ¬ Bad L ∧ sumT K L < 1 := by
  unfold μ at h
  by_cases hb : Bad L
  · rw [ite_eq_left hb] at h; exact absurd h (lt_irrefl _)
  · rw [ite_eq_right hb] at h; exact ⟨hb, h⟩

/-- The sum over a log with one more good entry. -/
theorem sumT_good (K : KCert S R) {L : Log} {q : ByteArray} {a : Digest}
    (hb : ¬ Bad (L ++ [(q, a)])) (hq : q ∉ L.map Prod.fst) :
    sumT K (L ++ [(q, a)]) + ∑ j ∈ Finset.range L.length, tdrop K L q j =
      sumT K L + term K (L ++ [(q, a)]) L.length := by
  unfold sumT
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ, add_right_comm,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j hj => term_old K hb hq (Finset.mem_range.mp hj)

/-- **The `step` law.** -/
theorem mu_step (K : KCert S R) (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : μ K L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, μ K (L ++ [(q, a)]) ≤ (μ K L + εFS K) * 2 ^ 256 := by
  classical
  obtain ⟨hbL, -⟩ := mu_lt_one hμ
  have hμL : μ K L = sumT K L := by unfold μ; rw [ite_eq_right hbL]
  rw [hμL]
  set D := ∑ j ∈ Finset.range L.length, tdrop K L q j with hDdef
  have hD : D ≤ sumT K L := Finset.sum_le_sum fun j _ => tdrop_le K L q j
  set X := sumT K L - D with hX
  have hXD : X + D = sumT K L := tsub_add_cancel_of_le hD
  have hgood : ∀ a, ¬ Bad (L ++ [(q, a)]) →
      sumT K (L ++ [(q, a)]) = X + term K (L ++ [(q, a)]) L.length := by
    intro a ha
    have h1 := sumT_good K ha hq
    rw [← hXD, add_right_comm] at h1
    exact add_right_cancel h1
  -- the bound from any upper bound `newF` of the new entry's charge
  suffices hsuff : ∀ newF : Digest → ℝ≥0,
      (∀ a, ¬ Bad (L ++ [(q, a)]) → term K (L ++ [(q, a)]) L.length ≤ newF a) →
      ∑ a, newF a ≤ 2 ^ 256 * (D + K.ε + K.εB) →
      ∑ a : Digest, μ K (L ++ [(q, a)]) ≤ (sumT K L + εFS K) * 2 ^ 256 by
    -- the cases of the fresh query
    by_cases hseed : ∃ x, S.SeedQ L q x
    · obtain ⟨x, hx⟩ := hseed
      refine hsuff (fun _ => gterm K (S.seedNI x)) (fun a ha => ?_) ?_
      · have hN := (S.isNode_new ha (S.seedNI x)).mpr (Or.inl ⟨x, hx, rfl⟩)
        rw [term_of_node K ha hN]; exact contrib_le_gterm K _ _ _
      · rw [Finset.sum_const, Finset.card_univ, fintype_card_digest, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans ?_ (le_add_of_nonneg_left zero_le |>.trans_eq (add_assoc _ _ _).symm)
        exact group_le K (x := x) VerifierProgram.Reachable.nil trivial (after_nil _)
    · by_cases hchild : ∃ i I₀ msg k hs hb' caps, S.ChildQ L q i I₀ msg k hs hb' caps
      · obtain ⟨i, I₀, msg, k, hs, hb', caps, hC⟩ := hchild
        refine hsuff (fun a => gterm K (S.childNI I₀.x k hs hb' caps a)) (fun a ha => ?_) ?_
        · have hN := (S.isNode_new ha _).mpr
            (Or.inr ⟨i, I₀, msg, k, hs, hb', caps, hC, rfl⟩)
          rw [term_of_node K ha hN]; exact contrib_le_gterm K _ _ _
        · rw [sum_child]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          obtain ⟨hI, ⟨qi, ai, hi, hqeq⟩, hcap, hst⟩ := hC
          by_cases hm : msg = []
          · subst hm
            obtain ⟨ho, hhb, -⟩ := (S.steps_nil_iff _ _ _).mp hst
            simp only at ho hhb
            subst hhb
            have hg : gterm K I₀ ≤ D := by
              have hiL : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
              have hq' : toQ (qi, ai).2.toList = q := by rw [hqeq]; simp
              have hcont : S.Cont I₀ := ⟨k, hs, ho⟩
              have ht : tdrop K L q i = gterm K I₀ := by
                unfold tdrop
                rw [ite_eq_left ⟨I₀, hI, hcont, (qi, ai), hi, hq'⟩, term_of_node K hbL hI]
                unfold contrib
                rw [ite_eq_right]
                rintro ⟨-, e, he, hm⟩
                rw [hi, Option.some.injEq] at he
                subst he
                exact hq (hq' ▸ hm)
              rw [← ht]
              exact Finset.single_le_sum (fun j _ => zero_le)
                (Finset.mem_range.mpr hiL)
            refine le_trans ?_ (le_add_of_nonneg_right zero_le)
            refine le_trans ?_ (le_add_of_nonneg_right zero_le)
            refine le_trans (le_of_eq ?_) hg
            unfold gterm
            rw [← escR_opens' _ ho, ← escR_opens' _ ho]
          · obtain ⟨-, hbd⟩ := S.steps_inv (S.wellShaped_wordOf L) (node_inv hI) _ hst
            obtain ⟨pb, h1, h2, h3, h4⟩ := hbd (by
              simp only [List.length_nil]; exact List.length_pos_of_ne_nil hm)
            simp only at h1 h2 h3 h4
            rw [← escR_opens' _ h4, ← escR_opens' _ h4]
            refine (group_le K h1 h3 h2).trans ?_
            rw [add_assoc]; exact le_add_of_nonneg_left zero_le
      · refine hsuff (fun _ => 0) (fun a ha => ?_) (by simp)
        have hn : ¬ ∃ I, S.IsNode (L ++ [(q, a)]) L.length I := by
          rintro ⟨I, hI⟩
          rcases (S.isNode_new ha I).mp hI with ⟨x, hx, -⟩ | ⟨i, I₀, msg, k, hs, hb', caps, hC, -⟩
          · exact hseed ⟨x, hx⟩
          · exact hchild ⟨i, I₀, msg, k, hs, hb', caps, hC⟩
        rw [term_of_not_node K hn]
  intro newF h1 h2
  have hbad := bad_step_frac hbL hq hl
  have hpt : ∀ a, μ K (L ++ [(q, a)]) ≤
      (if Bad (L ++ [(q, a)]) then 1 else 0) + (X + newF a) := by
    intro a
    unfold μ
    split_ifs with ha
    · exact le_add_of_le_of_nonneg le_rfl (zero_le)
    · rw [zero_add, hgood a ha]; exact add_le_add le_rfl (h1 a ha)
  calc ∑ a : Digest, μ K (L ++ [(q, a)])
      ≤ ∑ a : Digest, ((if Bad (L ++ [(q, a)]) then 1 else 0) + (X + newF a)) :=
        Finset.sum_le_sum fun a _ => hpt a
    _ = ((Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card : ℝ≥0) +
          (2 ^ 256 * X + ∑ a, newF a) := by
        rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, fintype_card_digest, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (badCount : ℝ≥0) + (2 ^ 256 * X + 2 ^ 256 * (D + K.ε + K.εB)) := by
        exact add_le_add (by exact_mod_cast hbad) (add_le_add le_rfl h2)
    _ = (sumT K L + εFS K) * 2 ^ 256 := by
        rw [← hXD]
        unfold εFS
        have h256 : (2 : ℝ≥0) ^ 256 ≠ 0 := by positivity
        field_simp
        ring

end Scheme

end Lvm.FS
