-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/CommitDoom.lean` (formal rev 40f877dc) as `LvmFrontCommitDoom` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.CommitDoom

  The doom the stack's commitment creates: no stack the committed word binds satisfies the
  leanISA instance's relation. Its definition on histories, and the specification of the
  program's first two phases (the announced sizes and the stack's root) that creates it.
-/


import LvmSpecRulesLeaves
import LvmVCore

/-!
# The commitment's doom

Steps 1 and 2 of the verifier program (`readAnnouncedSizes`, `commitStack`; `verify_execution`,
`crates/verifier/src/lib.rs:219-237` at leanVM `40f877dc`) read
the announced sizes and the stack's root. Before the root, nothing is at stake: the doom is
false, so no group of challenges is charged. The root creates the doom `CommitDoom`: for the sizes
`s` the layout was built from, no candidate of the committed word `W₀` (`Candidates`, at the
Johnson threshold `A μ R`, a parameter) satisfies `M3Holds` of the leanISA instance at `s` for the
public input `input`.

* `firstWord h`: the word of the first commitment of a history, the stack's (commitment `0`).
* `CommitDoom prog input A (layout, ρ) h`: the doom after the root, for the value
  `(layout, ρ)` `readAnnouncedSizes` returned.
* `readSizesSpec`, `commitStackSpec`: the specifications of the two steps, from no doom; the
  second ends in `CommitDoom`. They compose with `Spec.bind` as the program does:
  `readSizesSpec.bind fun a ↦ (commitStackSpec a).bind fun _ ↦ …`.

The doom quantifies over the candidates; it says nothing about which candidate the prover had
in mind. Its negation, at the end of a run, is the knowledge statement: some candidate satisfies
the relation, and it is the extractor's output.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

section

/-- The word of the first commitment of a history. -/
def firstWord (h : List Ev) : Option Word := (commits h).head?.map (·.2.2)

/-- The commitments of a concatenation. -/
theorem commits_append_hist (h l : List Ev) : commits (h ++ l) = commits h ++ commits l := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

/-- The first commitment of a history extended past it is unchanged. -/
theorem firstWord_append {h : List Ev} {W : Word} (hW : firstWord h = some W) (l : List Ev) :
    firstWord (h ++ l) = some W := by
  unfold firstWord at hW ⊢
  rw [commits_append_hist]
  rcases hc : commits h with _ | ⟨c, cs⟩
  · simp [hc] at hW
  · simpa [hc] using hW

-- lvm (WP-2) cut: `CommitDoom` and `CommitDoom.append` (the doom over the leanISA instance
-- `leanIsaInstance prog s` and `verifierLayout`, a leanISA seam) and `readSizesSpec` (over the
-- leanISA verifier's `readAnnouncedSizes`). The generic form of the doom is `HDoom cands
-- (Seam.commit I) input` (`LvmFrontBusSpec`); `commitStackSpec` is stated for any postcondition.

variable {εmax T : ENNReal}

/-- **The stack's root**: from no doom to the commitment's doom. The boundary after the root
carries the follower's lead `T`, so `T ≤ εmax`. -/
noncomputable def commitStackSpec (Post : Unit → List Ev → Prop) (logN logInvRate : ℕ)
    (hT : T ≤ εmax) :
    Spec (commitStack logN logInvRate) (fun _ ↦ False) Post εmax 0 T :=
  Spec.bind (Spec.dead : Spec _ _ (fun _ _ ↦ False) εmax 0 0) fun config ↦ by
    cases config with
    | nil => exact Spec.fail
    | cons level _ =>
      exact Spec.commitP _ _ (fun _ _ h _ ↦ h.elim) hT

end
end LeanVM.Protocol.EndToEnd.Front
