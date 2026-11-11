-- WP-5 (FS). New for lvm (BLUEPRINT §7.3): the `final` law of the compiled verifier's knowledge
-- state.
import LvmPotential

/-!
# The final law

On a log with potential below `1`, an accepting replay of the compiled verifier is an accepting
reachable history of `P x` whose Fiat–Shamir queries are nodes of the forest (each one the child
of the previous, the first the seed). Every node charges less than `1`, so:

* a group that started in doom ended in doom (the node where it ends charges `[¬D]`), and moves
  keep doom: doom at a boundary would reach the accepting end, which `Cert.final` refutes;
* a group that started not lucky ended not lucky, and moves keep that: the end is not lucky;
* groups with no challenge (openings right after a move) are covered by `ε, εB < 1`.

So `KCert.extract` applies to the replay's history, which is what `Ex` returns.

* **`trun_accept`**: the invariant of the replay, by induction on the program.
* **`final_law`**: `KState.final` for `μ` and `Ex K.ext`.
-/

namespace Lvm.FS

open LeanVM.Parameters RecursionFast
open LeanVM.Protocol.Compile hiding Proof  -- INT-1: WP-2's DSL also has a `Proof`; here it is `RecursionFast.Proof`
open scoped NNReal

namespace Scheme

variable {S : Scheme} {R : Digest → Wit → Prop}

/-! ## Facts about histories and steps -/

theorem commits_append (h l : List Ev) : commits (h ++ l) = commits h ++ commits l := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

theorem not_boundary_snoc_sample (h : List Ev) (c : E) : ¬ Boundary (h ++ [Ev.sample c]) := by
  cases h with
  | nil => simp [Boundary]
  | cons a t =>
    unfold Boundary
    simp only [List.cons_append]
    rw [← List.cons_append, List.getLast?_concat]
    exact id

theorem not_boundary_snoc_query (h : List Ev) (rows : List (List K)) :
    ¬ Boundary (h ++ [Ev.query rows]) := by
  cases h with
  | nil => simp [Boundary]
  | cons a t =>
    unfold Boundary
    simp only [List.cons_append]
    rw [← List.cons_append, List.getLast?_concat]
    exact id

/-- Openings from a point that is no opening stay there. -/
theorem opens_of_not_query {p : VerifierProgram Bool} {h : List Ev}
    {y : VerifierProgram Bool × List Ev} (ho : Opens (p, h) y)
    (hp : ¬ ∃ i ps k, p = .query i ps k) : y = (p, h) := by
  rcases ho.cases_head with h1 | ⟨z, hz, -⟩
  · exact h1.symm
  · cases hz with
    | mk hr => exact absurd ⟨_, _, _, rfl⟩ hp

/-- Openings are deterministic. -/
theorem openStep_det {x y z : VerifierProgram Bool × List Ev} (h₁ : OpenStep x y)
    (h₂ : OpenStep x z) : y = z := by
  cases h₁ with
  | mk hr => cases h₂ with
    | mk hr' => rw [hr] at hr'; cases hr'; rfl

/-- A point reached by openings that is neither an opening nor a challenge is not a group
continuation. -/
theorem not_cont_of_opens {I : S.NI} {p : VerifierProgram Bool} {h : List Ev}
    (ho : Opens (I.st.p, I.st.h) (p, h)) (hq : ¬ ∃ i ps k, p = .query i ps k)
    (hs : ¬ ∃ k, p = .sample k) : ¬ S.Cont I := by
  rintro ⟨k, hs', ho'⟩
  have hru : Relator.RightUnique OpenStep := fun _ _ _ a b => openStep_det a b
  rcases Relation.ReflTransGen.total_of_right_unique hru ho ho' with h1 | h1
  · have := opens_of_not_query h1 hq
    simp only [Prod.mk.injEq] at this
    exact hs ⟨k, this.1.symm⟩
  · have := opens_of_not_query h1 (by rintro ⟨_, _, _, h⟩; cases h)
    simp only [Prod.mk.injEq] at this
    exact hs ⟨k, this.1⟩

/-- Reading appended bytes. -/
theorem steps_append_msg {W : CapI → Word} {x y : PS × Bytes} (h : S.Steps W x y) (m₂ : Bytes) :
    S.Steps W (x.1, x.2 ++ m₂) (y.1, y.2 ++ m₂) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hst ih =>
    refine ih.tail ?_
    cases hst with
    | read hl =>
      rename_i k h hb caps msg
      have h1 : (msg ++ m₂).take 24 = msg.take 24 := List.take_append_of_le_length hl
      have h2 : (msg ++ m₂).drop 24 = msg.drop 24 ++ m₂ := List.drop_append_of_le_length hl
      have := Step.read (S := S) (W := W) (k := k) (h := h) (hb := hb) (caps := caps)
        (msg := msg ++ m₂) (by simp; omega)
      rw [h1, h2] at this
      exact this
    | commit hl =>
      rename_i ht w k h hb caps msg
      have h1 : S.capI ht w (msg ++ m₂) = S.capI ht w msg := by
        unfold capI; rw [List.take_append_of_le_length hl]
      have h2 : (msg ++ m₂).drop (S.capBytes ht w) = msg.drop (S.capBytes ht w) ++ m₂ :=
        List.drop_append_of_le_length hl
      have := Step.commit (S := S) (W := W) (ht := ht) (w := w) (k := k) (h := h) (hb := hb)
        (caps := caps) (msg := msg ++ m₂) (by simp; omega)
      rw [h1, h2] at this
      exact this
    | «open» hr => exact Step.open hr

/-- The points where a group ends and no opening or challenge follows. -/
def IsEnd (p : VerifierProgram Bool) : Prop :=
  (∃ k, p = .read k) ∨ (∃ ht w k, p = .commit ht w k) ∨ p = .ret true

theorem isEnd_not_query {p : VerifierProgram Bool} (h : IsEnd p) : ¬ ∃ i ps k, p = .query i ps k := by
  rintro ⟨i, ps, k, rfl⟩
  rcases h with ⟨_, h⟩ | ⟨_, _, _, h⟩ | h <;> cases h

theorem isEnd_not_sample {p : VerifierProgram Bool} (h : IsEnd p) : ¬ ∃ k, p = .sample k := by
  rintro ⟨k, rfl⟩
  rcases h with ⟨_, h⟩ | ⟨_, _, _, h⟩ | h <;> cases h

open Classical in
theorem escR_isEnd (G : List Ev → Prop) (h : List Ev) {p : VerifierProgram Bool} (hp : IsEnd p) :
    escR G h p = if G h then 0 else 1 := by
  rcases hp with ⟨k, rfl⟩ | ⟨ht, w, k, rfl⟩ | rfl <;> simp [escR]

open Classical in
/-- **A group ends where it started**: on a log of total charge below `1`, at a point `s` read
from a node with no challenge left before a move or the verdict, doom at the group's start gives
doom at `s`, and no luck at the start gives no luck at `s`. -/
theorem group_end (K : KCert S R) {L : Log} (hb : ¬ Bad L) (hS : sumT K L < 1) {j : ℕ}
    {I : S.NI} (hN : S.IsNode L j I) {s : PS} {buf : Bytes}
    (hst : S.Steps (S.wordOf L) (I.st, buf) (s, [])) (hp : IsEnd s.p) :
    ((K.cert I.x).D s.hb → (K.cert I.x).D s.h) ∧ (¬ K.B I.x s.hb → ¬ K.B I.x s.h) := by
  by_cases hm : buf = []
  · subst hm
    obtain ⟨ho, hhb, -⟩ := (S.steps_nil_iff _ _ _).mp hst
    have hnc := S.not_cont_of_opens ho (isEnd_not_query hp) (isEnd_not_sample hp)
    have hj : j < L.length := by
      obtain ⟨e, he, -⟩ := S.isNode_size hN
      exact (List.getElem?_eq_some_iff.mp he).1
    have hlt : contrib K L j I < 1 := by
      rw [← term_of_node K hb hN]
      refine lt_of_le_of_lt ?_ hS
      exact Finset.single_le_sum (f := term K L) (fun _ _ => zero_le) (Finset.mem_range.mpr hj)
    unfold contrib at hlt
    rw [ite_eq_right (fun h => hnc h.1)] at hlt
    unfold gterm at hlt
    rw [escR_opens' _ ho, escR_opens' _ ho, escR_isEnd _ _ hp, escR_isEnd _ _ hp, ← hhb] at hlt
    constructor
    · intro hD
      by_contra hD'
      rw [ite_eq_left hD, ite_eq_right hD'] at hlt
      exact absurd (le_add_of_le_of_nonneg le_rfl zero_le) (not_le.mpr hlt)
    · intro hB hB'
      rw [ite_eq_left hB, ite_eq_right (show ¬ ¬ K.B I.x s.h from fun h => h hB')] at hlt
      exact absurd (le_add_of_nonneg_left zero_le) (not_le.mpr hlt)
  · obtain ⟨-, hbd⟩ := S.steps_inv (S.wellShaped_wordOf L) (node_inv hN) _ hst
    obtain ⟨pb, h1, h2, h3, h4⟩ := hbd (by simp only [List.length_nil]; exact List.length_pos_of_ne_nil hm)
    by_cases hg : (∃ k, pb = .sample k) ∨ (∃ i ps k, pb = .query i ps k)
    · constructor
      · intro hD
        by_contra hD'
        have := escD_le K h1 h3 h2 hg hD
        rw [escR_opens' _ h4, escR_isEnd _ _ hp, ite_eq_right hD'] at this
        exact absurd K.ε_lt_one (not_lt.mpr this)
      · intro hB hB'
        have := escB_le K h1 h3 h2 hg hB
        rw [escR_opens' _ h4, escR_isEnd _ _ hp, ite_eq_right (show ¬ ¬ K.B I.x s.h from fun h => h hB')] at this
        exact absurd K.εB_lt_one (not_lt.mpr this)
    · have hq : ¬ ∃ i ps k, pb = .query i ps k := fun h => hg (Or.inr h)
      have := opens_of_not_query h4 hq
      simp only [Prod.mk.injEq] at this
      rw [← this.2]
      exact ⟨id, id⟩

/-! ## The replay's invariant -/

/-- The verifier's commitments are the history's, with the log's words. -/
def Align (L : Log) (caps : List CapI) (h : List Ev) : Prop :=
  commits h = caps.map fun ci => (ci.ht, ci.wd, S.wordOf L ci)

open Classical in
/-- **The replay's invariant**, by induction on the program. -/
theorem trun_accept (K : KCert S R) {L : Log} (hb : ¬ Bad L) (hS : sumT K L < 1) (x : S.Stmt) :
    ∀ (p : VerifierProgram Bool) (st : Digest) (buf : Bytes) (caps : List CapI) (body : Bytes)
      (h hbc : List Ev) (j : ℕ) (I : S.NI) (hf : List Ev),
      S.IsNode L j I → I.x = x → (∃ e, L[j]? = some e ∧ e.2 = st) →
      S.Steps (S.wordOf L) (I.st, buf) (⟨p, h, hbc, caps⟩, []) →
      (∀ h', h' <+: h → Boundary h' → (K.cert x).D h' → (K.cert x).D hbc) →
      ¬ K.B x hbc → (∀ h', h' <+: h → Boundary h' → ¬ K.B x h') → S.Align L caps h →
      S.trun L p st buf caps body h = some (true, hf) →
      (S.P x).Reachable hf ∧ (S.P x).after hf = some (.ret true) ∧ ¬ K.B x hf ∧
        (∀ h', h' <+: hf → Boundary h' → ¬ K.B x h') ∧
        ∀ h', h' <+: hf → Boundary h' → ¬ (K.cert x).D h' := by
  intro p
  induction p with
  | ret b =>
    intro st buf caps body h hbc j I hf hN hx hst hsteps hD hB hB' hal hrun
    simp only [trun, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨hb1, rfl⟩ := hrun
    have hbt : b = true := by cases b <;> simp_all
    subst hbt
    subst hx
    obtain ⟨⟨hr, ha⟩, -⟩ := S.steps_inv (S.wellShaped_wordOf L) (node_inv hN) _ hsteps
    obtain ⟨hgD, hgB⟩ := S.group_end K hb hS hN hsteps (Or.inr (Or.inr rfl))
    have hfin : ¬ (K.cert I.x).D h := (K.cert I.x).final hr ha
    exact ⟨hr, ha, hgB hB, hB', fun h' hp' hbd' hD' => hfin (hgD (hD h' hp' hbd' hD'))⟩
  | fail =>
    intro st buf caps body h hbc j I hf hN hx hst hsteps hD hB hB' hal hrun
    simp [trun] at hrun
  | grind bits k _ =>
    intro st buf caps body h hbc j I hf hN hx hst hsteps hD hB hB' hal hrun
    simp [trun] at hrun
  | read k ih =>
    intro st buf caps body h hbc j I hf hN hx hst hsteps hD hB hB' hal hrun
    simp only [trun] at hrun
    by_cases hl : body.length < 24
    · rw [ite_eq_left hl] at hrun; simp at hrun
    · rw [ite_eq_right hl] at hrun
      subst hx
      obtain ⟨⟨hr, ha⟩, -⟩ := S.steps_inv (S.wellShaped_wordOf L) (node_inv hN) _ hsteps
      obtain ⟨hgD, hgB⟩ := S.group_end K hb hS hN hsteps (Or.inl ⟨k, rfl⟩)
      set y := S.decE (body.take 24) with hy
      have h24 : (body.take 24).length = 24 := by simp; omega
      have hBn : ¬ K.B I.x (h ++ [.read y]) := K.B_read y hr ha (hgB hB)
      refine ih y st (buf ++ body.take 24) caps (body.drop 24) (h ++ [.read y])
        (h ++ [.read y]) j I hf hN rfl hst ?_ ?_ hBn ?_ ?_ hrun
      · have h1 := S.steps_append_msg hsteps (body.take 24)
        simp only [List.nil_append] at h1
        refine h1.tail ?_
        have := Step.read (S := S) (W := S.wordOf L) (k := k) (h := h) (hb := hbc) (caps := caps)
          (msg := body.take 24) (by omega)
        rwa [List.take_take, min_self, List.drop_eq_nil_of_le (by rw [h24])] at this
      · intro h' hp' hbd' hD'
        rcases List.prefix_concat_iff.mp hp' with rfl | hp''
        · exact hD'
        · exact (K.cert I.x).read y hr ha (hgD (hD h' hp'' hbd' hD'))
      · intro h' hp' hbd'
        rcases List.prefix_concat_iff.mp hp' with rfl | hp''
        · exact hBn
        · exact hB' h' hp'' hbd'
      · unfold Align at hal ⊢
        rw [commits_append, hal]; simp [commits]
  | sample k ih =>
    intro st buf caps body h hbc j I hf hN hx hst hsteps hD hB hB' hal hrun
    simp only [trun] at hrun
    by_cases hcap : 32 + buf.length ≤ queryCap
    · rw [ite_eq_left hcap] at hrun
      cases hf' : L.find? (fun e => decide (e.1 = toQ (st.toList ++ buf))) with
      | none => rw [hf'] at hrun; simp at hrun
      | some e =>
        rw [hf', Option.bind_some] at hrun
        obtain ⟨hpe, j', hj', hLj', -⟩ := List.find?_eq_some_iff_getElem.mp hf'
        have he1 : e.1 = toQ (st.toList ++ buf) := by simpa using hpe
        have hgj' : L[j']? = some (toQ (st.toList ++ buf), e.2) := by
          rw [List.getElem?_eq_some_iff]; exact ⟨hj', by rw [hLj', ← he1]⟩
        obtain ⟨e₀, he₀, hst₀⟩ := hst
        have hjj : j < j' := by
          by_contra hle
          refine not_inWins_of_not_bad hb (i := j') (j := j) (by omega) hgj' he₀ ?_
          refine ⟨by rw [size_toQ, List.length_append, Vector.length_toList]; exact hcap, 0,
            by rw [size_toQ, List.length_append, Vector.length_toList]; omega, ?_⟩
          unfold win
          rw [qb_toQ, List.drop_zero, dg_toList_append]
          exact hst₀
        have hN' : S.IsNode L j' (S.childNI I.x k h hbc caps e.2) :=
          IsNode.child hN hjj (by rw [he₀]) (by rw [hgj', ← hst₀]) hcap hsteps
        refine ih (S.chal e.2) e.2 [] caps body (h ++ [.sample (S.chal e.2)]) hbc j'
          (S.childNI I.x k h hbc caps e.2) hf hN' hx ⟨_, hgj', rfl⟩ Relation.ReflTransGen.refl
          ?_ hB ?_ ?_ hrun
        · intro h' hp' hbd' hD'
          rcases List.prefix_concat_iff.mp hp' with rfl | hp''
          · exact absurd hbd' (not_boundary_snoc_sample _ _)
          · exact hD h' hp'' hbd' hD'
        · intro h' hp' hbd'
          rcases List.prefix_concat_iff.mp hp' with rfl | hp''
          · exact absurd hbd' (not_boundary_snoc_sample _ _)
          · exact hB' h' hp'' hbd'
        · unfold Align at hal ⊢
          rw [commits_append, hal]; simp [commits]
    · rw [ite_eq_right hcap] at hrun; simp at hrun
  | commit ht w k ih =>
    intro st buf caps body h hbc j I hf hN hx hst hsteps hD hB hB' hal hrun
    simp only [trun] at hrun
    by_cases hl : body.length < S.capBytes ht w
    · rw [ite_eq_left hl] at hrun; simp at hrun
    · rw [ite_eq_right hl] at hrun
      subst hx
      obtain ⟨⟨hr, ha⟩, -⟩ := S.steps_inv (S.wellShaped_wordOf L) (node_inv hN) _ hsteps
      obtain ⟨hgD, hgB⟩ := S.group_end K hb hS hN hsteps (Or.inr (Or.inl ⟨ht, w, k, rfl⟩))
      set ci := S.capI ht w body with hci
      have hcb : (body.take (S.capBytes ht w)).length = S.capBytes ht w := by simp; omega
      have hci' : S.capI ht w (body.take (S.capBytes ht w)) = ci := by
        rw [hci]; unfold capI; rw [List.take_take, min_self]
      have hws : WellShaped w (S.wordOf L ci) := S.wellShaped_wordOf L ci
      have hBn : ¬ K.B I.x (h ++ [.commit ht w (S.wordOf L ci)]) := K.B_commit _ hr ha hws (hgB hB)
      refine ih st (buf ++ body.take (S.capBytes ht w)) (caps ++ [ci]) (body.drop (S.capBytes ht w))
        (h ++ [.commit ht w (S.wordOf L ci)]) (h ++ [.commit ht w (S.wordOf L ci)]) j I hf hN rfl
        hst ?_ ?_ hBn ?_ ?_ hrun
      · have h1 := S.steps_append_msg hsteps (body.take (S.capBytes ht w))
        simp only [List.nil_append] at h1
        refine h1.tail ?_
        have := Step.commit (S := S) (W := S.wordOf L) (ht := ht) (w := w) (k := k) (h := h)
          (hb := hbc) (caps := caps) (msg := body.take (S.capBytes ht w)) (by omega)
        rwa [hci', List.drop_eq_nil_of_le (by omega)] at this
      · intro h' hp' hbd' hD'
        rcases List.prefix_concat_iff.mp hp' with rfl | hp''
        · exact hD'
        · exact (K.cert I.x).commit _ hr ha hws (hgD (hD h' hp'' hbd' hD'))
      · intro h' hp' hbd'
        rcases List.prefix_concat_iff.mp hp' with rfl | hp''
        · exact hBn
        · exact hB' h' hp'' hbd'
      · unfold Align at hal ⊢
        rw [commits_append, hal]; simp [commits, hci, capI]
  | query i ps k ih =>
    intro st buf caps body h hbc j I hf hN hx hst hsteps hD hB hB' hal hrun
    simp only [trun] at hrun
    cases hci : caps[i]? with
    | none => rw [hci] at hrun; simp at hrun
    | some ci =>
      rw [hci] at hrun
      simp only at hrun
      cases ho : (S.openAll ci ps body).runLog L with
      | none => rw [ho] at hrun; simp at hrun
      | some r =>
        rw [ho, Option.bind_some] at hrun
        rcases r with _ | ⟨rows, rest⟩
        · simp at hrun
        · simp only at hrun
          have hrows := S.openAll_rows (nodup_snd_of_not_bad hb) ci ps body rest rows ho
          have hans : answer h i ps = some rows := by
            unfold answer
            rw [hal, List.getElem?_map, hci, Option.map_some, Option.map_some, hrows]
          refine ih rows st buf caps rest (h ++ [.query rows]) hbc j I hf hN hx hst ?_ ?_ hB ?_ ?_
            hrun
          · exact hsteps.tail (Step.open hans)
          · intro h' hp' hbd' hD'
            rcases List.prefix_concat_iff.mp hp' with rfl | hp''
            · exact absurd hbd' (not_boundary_snoc_query _ _)
            · exact hD h' hp'' hbd' hD'
          · intro h' hp' hbd'
            rcases List.prefix_concat_iff.mp hp' with rfl | hp''
            · exact absurd hbd' (not_boundary_snoc_query _ _)
            · exact hB' h' hp'' hbd'
          · unfold Align at hal ⊢
            rw [commits_append, hal]; simp [commits]

/-- **The final law.** -/
theorem final_law (K : KCert S R) (L : Log) (c : Digest) (π : Proof) (hμ : μ K L < 1)
    (hacc : (S.V c π).runLog L = some true) : ∃ w, S.Ex K.ext c π L = some w ∧ R c w := by
  obtain ⟨hb, hS⟩ := mu_lt_one hμ
  rw [runLog_V] at hacc
  unfold Ex
  rcases hhdr : S.hdr π with _ | ⟨x, body⟩
  · rw [hhdr] at hacc; simp at hacc
  · rw [hhdr] at hacc
    simp only at hacc ⊢
    by_cases hpre : S.preOk c x
    · rw [ite_eq_left hpre] at hacc ⊢
      have hok : S.ok c x = true := by unfold preOk at hpre; simp at hpre; exact hpre.1
      have hcap : 32 + (S.enc x).length ≤ queryCap := by unfold preOk at hpre; simp at hpre; exact hpre.2
      cases h0 : L.find? (fun e => decide (e.1 = toQ S.q0)) with
      | none => rw [h0] at hacc; simp at hacc
      | some e₀ =>
        rw [h0, Option.bind_some] at hacc
        rw [Option.bind_some]
        cases h1 : L.find? (fun e => decide (e.1 = S.seedQ e₀.2 x)) with
        | none => rw [h1] at hacc; simp at hacc
        | some e₁ =>
          rw [h1, Option.bind_some] at hacc
          rw [Option.bind_some]
          cases hr : S.trun L (S.P x) e₁.2 [] [] body [] with
          | none => rw [hr] at hacc; simp at hacc
          | some res =>
            rw [hr] at hacc
            obtain ⟨b, hf⟩ := res
            simp only [Option.map_some, Option.some.injEq] at hacc
            subst hacc
            simp only [Option.bind_some, ite_true, Option.some.injEq, exists_eq_left']
            -- the seed node
            obtain ⟨hp0, r, hrL, hLr, -⟩ := List.find?_eq_some_iff_getElem.mp h0
            obtain ⟨hp1, j₁, hj₁, hLj₁, -⟩ := List.find?_eq_some_iff_getElem.mp h1
            have he0 : e₀.1 = toQ S.q0 := by simpa using hp0
            have he1 : e₁.1 = S.seedQ e₀.2 x := by simpa using hp1
            have hgr : L[r]? = some (toQ S.q0, e₀.2) := by
              rw [List.getElem?_eq_some_iff]; exact ⟨hrL, by rw [hLr, ← he0]⟩
            have hgj : L[j₁]? = some (S.seedQ e₀.2 x, e₁.2) := by
              rw [List.getElem?_eq_some_iff]; exact ⟨hj₁, by rw [hLj₁, ← he1]⟩
            have hrj : r < j₁ := by
              by_contra hle
              refine not_inWins_of_not_bad hb (i := j₁) (j := r) (by omega) hgj hgr ?_
              refine ⟨by rw [seedQ_size]; exact hcap, 0, by rw [seedQ_size]; omega, ?_⟩
              unfold win seedQ
              rw [qb_toQ, List.drop_zero, dg_toList_append]
            have hN : S.IsNode L j₁ (S.seedNI x) := IsNode.seed x hrj hgr hgj hcap
            obtain ⟨hr', ha', hB', hBp, hD'⟩ := S.trun_accept K hb hS x (S.P x) e₁.2 [] [] body []
              [] j₁ (S.seedNI x) hf hN rfl ⟨_, hgj, rfl⟩ Relation.ReflTransGen.refl
              (fun h' hp' _ hD => by rw [List.prefix_nil.mp hp'] at hD; exact hD) (K.B_nil x)
              (fun h' hp' _ => by rw [List.prefix_nil.mp hp']; exact K.B_nil x)
              (by unfold Align; rfl) hr
            exact K.extract hok hr' ha' hB' hBp hD'
    · rw [ite_eq_right hpre] at hacc; simp at hacc

end Scheme

end Lvm.FS
