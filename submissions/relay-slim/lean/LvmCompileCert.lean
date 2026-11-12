-- WP-5 (FS). New for lvm (BLUEPRINT §7.2): the knowledge certificate `KCert` (leanVM's `Cert`
-- plus a luck predicate and an extraction map) and the escape probability in `ℝ≥0`.
import LvmForest
import Mathlib.Basic.ENNReal.BigOperators

/-!
# Knowledge certificates

**`KCert S R`** for a scheme `S` and a relation `R` on contract statements and witnesses:

* `cert x : Cert (S.P x)`: leanVM's doom certificate for every statement, with every group's
  escape bound at most one constant `ε < 1` (needed only at reachable boundaries in doom);
* the **luck** predicate `B x` (BLUEPRINT §7.2): not lucky at `[]`; moves keep "not lucky"; from
  every boundary that is not lucky, a group ends lucky with probability at most `εB < 1`
  (`B_group`, on leanVM's `esc` with the predicate `¬ B`);
* **`extract`**: for a statement the header check accepts (`S.ok c x`), an accepting reachable
  history that is not lucky (at its end and at every boundary prefix) and is outside doom at every
  boundary prefix gives a witness: `R c (ext c x h)`. The extraction map may read the contract
  statement `c`. (Knowledge in the computational sense comes with the extractor program,
  `KState.congrE`: `ext` should read only the words and messages of `h`.)

`ε < 1` and `εB < 1` serve the groups with no challenge (openings right after a move): their
escape is `0` or `1`, so a bound below `1` makes it `0`.

`escR`: leanVM's `esc` with values in `ℝ≥0` (the potential's type); `coe_escR` is the bridge,
`escR_le_one` the bound, `escR_opens` its invariance under openings, `escR_sample` the average.
-/

namespace Lvm.FS

open LeanVM.Parameters LeanVM.Protocol.Compile RecursionFast
open scoped NNReal

/-- leanVM's `esc` in `ℝ≥0`. -/
noncomputable def escR (D : List Ev → Prop) : List Ev → VerifierProgram Bool → ℝ≥0
  | h, VerifierProgram.sample k
      => (Fintype.card E : ℝ≥0)⁻¹ * ∑ c : E, escR D (h ++ [Ev.sample c]) (k c)
  | h, VerifierProgram.query i ps k => match answer h i ps with
    | some rows => escR D (h ++ [Ev.query rows]) (k rows)
    | none => 0
  | _, VerifierProgram.fail => 0
  | _, VerifierProgram.ret false => 0
  | h, _ => by classical exact if D h then 0 else 1

/-- **The bridge** to leanVM's `esc`. -/
theorem coe_escR (D : List Ev → Prop) (h : List Ev) (p : VerifierProgram Bool) :
    (escR D h p : ENNReal) = esc D h p := by
  classical
  induction p generalizing h with
  | ret b => cases b <;> simp only [escR, esc] <;> (try split_ifs) <;> simp
  | fail => simp [escR, esc]
  | read k ih => simp only [escR, esc]; split_ifs <;> simp
  | grind b k ih => simp only [escR, esc]; split_ifs <;> simp
  | commit ht w k ih => simp only [escR, esc]; split_ifs <;> simp
  | sample k ih =>
    simp only [escR, esc]
    rw [ENNReal.coe_mul, ENNReal.ofNNReal_finsetSum,
      ENNReal.coe_inv (by simp), ENNReal.coe_natCast]
    simp only [ih]
  | query i ps k ih =>
    simp only [escR, esc]
    cases answer h i ps with
    | none => simp
    | some rows => exact ih rows _

theorem escR_le_one (D : List Ev → Prop) (h : List Ev) (p : VerifierProgram Bool) :
    escR D h p ≤ 1 := by
  classical
  induction p generalizing h with
  | ret b => cases b <;> simp only [escR] <;> (try split_ifs) <;> simp
  | fail => simp [escR]
  | read k ih => simp only [escR]; split_ifs <;> simp
  | grind b k ih => simp only [escR]; split_ifs <;> simp
  | commit ht w k ih => simp only [escR]; split_ifs <;> simp
  | sample k ih =>
    simp only [escR]
    have hc : (0 : ℝ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos
    calc (Fintype.card E : ℝ≥0)⁻¹ * ∑ c : E, escR D (h ++ [Ev.sample c]) (k c)
        ≤ (Fintype.card E : ℝ≥0)⁻¹ * ∑ _c : E, (1 : ℝ≥0) := by gcongr with c; exact ih c _
      _ = 1 := by simp [Finset.card_univ]
  | query i ps k ih =>
    simp only [escR]
    cases answer h i ps with
    | none => simp
    | some rows => exact ih rows _

/-- Openings do not change the escape probability. -/
theorem escR_opens (D : List Ev → Prop) {s t : VerifierProgram Bool × List Ev} (h : Opens s t) :
    escR D s.2 s.1 = escR D t.2 t.1 := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    rw [ih]
    cases hst with
    | mk hr => simp only [escR, hr]

/-- Openings do not change the escape probability (components). -/
theorem escR_opens' (D : List Ev → Prop) {p p' : VerifierProgram Bool} {h h' : List Ev}
    (ho : Opens (p, h) (p', h')) : escR D h p = escR D h' p' := escR_opens D ho

/-- At a challenge, the escape probability is the average over the challenge. -/
theorem escR_sample (D : List Ev → Prop) (h : List Ev) (k : E → VerifierProgram Bool) :
    escR D h (.sample k) = (Fintype.card E : ℝ≥0)⁻¹ * ∑ c : E, escR D (h ++ [Ev.sample c]) (k c) := by
  rw [escR]

/-- **A knowledge certificate** for the scheme `S` and the relation `R`. -/
structure KCert (S : Scheme) (R : Digest → Wit → Prop) where
  /-- leanVM's doom certificate of every statement's program. -/
  cert : ∀ x : S.Stmt, Cert (S.P x)
  /-- The groups' escape bound. -/
  ε : ℝ≥0
  cert_ε : ∀ x h, (S.P x).Reachable h → Boundary h → (cert x).D h → (cert x).ε h ≤ ε
  ε_lt_one : ε < 1
  /-- Luck. -/
  B : S.Stmt → List Ev → Prop
  /-- The luck bound of a group. -/
  εB : ℝ≥0
  εB_lt_one : εB < 1
  B_nil : ∀ x, ¬ B x []
  B_read : ∀ {x h k} (y : E), (S.P x).Reachable h → (S.P x).after h = some (.read k) → ¬ B x h →
    ¬ B x (h ++ [Ev.read y])
  B_commit : ∀ {x h ht w k} (word : Word), (S.P x).Reachable h →
    (S.P x).after h = some (.commit ht w k) → WellShaped w word → ¬ B x h →
    ¬ B x (h ++ [Ev.commit ht w word])
  B_group : ∀ {x h p}, (S.P x).Reachable h → Boundary h → (S.P x).after h = some p →
    ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k)) → ¬ B x h →
    esc (fun h' => ¬ B x h') h p ≤ εB
  /-- The extraction map. -/
  ext : Digest → S.Stmt → List Ev → Wit
  /-- **Extraction** from an accepting history, not lucky, outside doom at every boundary. -/
  extract : ∀ {c x h}, S.ok c x = true → (S.P x).Reachable h →
    (S.P x).after h = some (.ret true) → ¬ B x h → (∀ h', h' <+: h → Boundary h' → ¬ B x h') →
    (∀ h', h' <+: h → Boundary h' → ¬ (cert x).D h') → R c (ext c x h)

end Lvm.FS
