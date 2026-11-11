-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TableTerms.lean` (formal rev 40f877dc) as `LvmFrontTableTerms` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.TableTerms

  The final loop of the verifier program's table sumcheck (`table_sumcheck`'s per-table reads) as
  reads followed by a pure computation, specified on any property the reads keep.
-/


import LvmBTableClaims
import LvmFrontBusSpec

/-! lvm (WP-2): over a table list `tables` (`refTableTerms`, `tableTermsSpec` take it; the
source's are at leanISA's `tables`), with `tableTermsClaims` from `LvmBTableClaims`. -/

/-!
# The table sumcheck's final values

`tableTerms` (`crates/verifier/src/bus.rs:239-257`) reads each table's row evaluations, in table
order, and accumulates the final check's value and the column claims. `refTableTerms` is the same
computation on the evaluations read, a pure function; `tableTermsSpec` says the loop reads them (one
list per table, of the table's width) and returns `refTableTerms` of them, keeping any property of
the history that reads keep.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open scoped ENNReal

section

/-- The per-table loop of `table_sumcheck` on the evaluations read, one list per table. -/
def refTableTerms (tables : List Table) (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → List (List E) → ℕ → E → List Verifier.ColumnClaim →
      E × List Verifier.ColumnClaim
  | [], _, _, final, claims => (final, claims)
  | _ :: _, [], _, final, claims => (final, claims)
  | (table, height, forms, weight) :: rest, evaluations :: evs, cursor, final, claims =>
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let claims := claims ++ evaluations.zipIdx.map fun (value, column) ↦
      ⟨(globalColumnBases tables).getD table.opcode 0 + column, point.take height, value⟩
    refTableTerms tables constraintPowers formPowers point rest evs (cursor + table.nConstraints) final
      claims

/-- The lead of the loop: the follower's with no table, `0` otherwise (it starts with a read). -/
def rowsLead : List (Table × ℕ × List Form × E) → ℝ≥0∞ → ℝ≥0∞
  | [], T => T
  | _ :: _, _ => 0

theorem rowsLead_le (rows : List (Table × ℕ × List Form × E)) (T : ℝ≥0∞) : rowsLead rows T ≤ T := by
  cases rows <;> simp [rowsLead]

/-- What the loop read: one list per table, of the table's width. -/
def ReadShape (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)) : Prop :=
  List.Forall₂ (fun r ev ↦ ev.length = r.1.width) rows evs

variable {εmax : ℝ≥0∞}

/-- **The final values' loop**: it reads one list per table, of the table's width (each positive),
and returns `refTableTerms` of them, keeping `P`. -/
noncomputable def tableTermsSpec (tables : List Table) {T : ℝ≥0∞} (hT : T ≤ εmax)
    (P : List Ev → Prop)
    (hP : ∀ h x, P h → P (h ++ [Ev.read x])) (cps fps point : List E) :
    (rows : List (Table × ℕ × List Form × E)) → (∀ r ∈ rows, 0 < r.1.width) →
      (cursor : ℕ) → (final : E) → (claims : List Verifier.ColumnClaim) →
      Spec (tableTermsClaims tables cps fps point rows cursor final claims) P
        (fun r h ↦ ∃ evs, ReadShape rows evs ∧
          r = refTableTerms tables cps fps point rows evs cursor final claims ∧ P h) εmax
        (rowsLead rows T) T
  | [], _, cursor, final, claims =>
    (Spec.ret (Post := fun r h ↦ ∃ evs, ReadShape [] evs ∧
      r = refTableTerms tables cps fps point [] evs cursor final claims ∧ P h) (final, claims)).mono
      (fun _ hp ↦ ⟨[], List.Forall₂.nil, rfl, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | (table, height, forms, weight) :: rest, hw, cursor, final, claims =>
    have hw0 : 0 < table.width := hw _ List.mem_cons_self
    Spec.congr (show (do
        let evaluations ← VerifierProgram.readScalars (table.width - 1 + 1)
        tableTermsClaims tables cps fps point rest (cursor + table.nConstraints)
          (final + weight * (dot ((cps.drop cursor).take table.nConstraints)
            (table.constraints evaluations) +
            dot fps (forms.map (·.evaluate (evaluations.getD · 0)))))
          (claims ++ evaluations.zipIdx.map fun (value, column) ↦
            ⟨(globalColumnBases tables).getD table.opcode 0 + column, point.take height, value⟩)) =
        tableTermsClaims tables cps fps point ((table, height, forms, weight) :: rest) cursor final claims by
      rw [Nat.sub_add_cancel hw0]
      rfl)
      ((readNSuccSpec P hP (le_trans (rowsLead_le rest T) hT) (table.width - 1)).bind'
        fun evaluations ↦
        (tableTermsSpec tables hT (fun h ↦ evaluations.length = table.width - 1 + 1 ∧ P h)
          (fun _ _ hp ↦ ⟨hp.1, hP _ _ hp.2⟩) cps fps point rest
          (fun r hr ↦ hw r (List.mem_cons_of_mem _ hr)) _ _ _).mono (fun _ hp ↦ hp)
          (fun r h ⟨evs, hs, hr, hl, hp⟩ ↦ ⟨evaluations :: evs,
            List.Forall₂.cons (by dsimp only; rw [hl]; omega) hs, hr, hp⟩) le_rfl le_rfl le_rfl)

end
end LeanVM.Protocol.EndToEnd.Front
