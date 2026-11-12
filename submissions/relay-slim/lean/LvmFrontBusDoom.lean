-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/BusDoom.lean` (formal rev 40f877dc) as `LvmFrontBusDoom` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.BusDoom

  Doom on a relation: no candidate oracle puts the statement in the relation. The escape of a
  challenge from it, bounded through a component's security and a union bound over the
  candidates, in the form the calculus of verifier programs takes it.
-/


import LvmProtoField
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card
import Mathlib.Basic.ENNReal.Inv

/-!
# Doom on a relation

A front phase's security is appended from one-round components on ArkLib's typed framework, a
checked message (`Typed.sendChecked`) or a checked challenge (`Typed.sampleChallenge`), each
between two relations on `(statement, oracles)`. The verifier program carries the statement in
its variables (the GKR state, the sumcheck's claim and point), so its doom after a sub-program can
be stated on the component's relation: `RelDoom C R x`, no oracle `o` of the candidate set `C` has
`((x, o), ()) ∈ R`. A prover message that passes its check keeps it (`say_keep`, from any
security of the message by `Typed.sendChecked_reflect`), and a challenge escapes it, over the
candidates, with probability at most `|C|` times the component's error (`draw_escape_le`, from
any security of the challenge by `Typed.sample_escape`): the count of bad challenges that
`Spec.sampleE` asks for.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol
open scoped NNReal ENNReal

section

/-- **Doom on a relation**: no candidate oracle puts the statement in the relation. -/
def RelDoom {S : Type} {ι : Type} {O : ι → Type} (C : Set (∀ i, O i))
    (R : Set ((S × ∀ i, O i) × Unit)) (x : S) : Prop :=
  ∀ o ∈ C, ((x, o), ()) ∉ R

open Classical in
/-- **The union bound over candidates**, counted: the challenges bad for some of at most `L₀`
candidates, each bad for at most a fraction `e` of the challenges, are at most a fraction
`L₀ · e`. -/
theorem card_exists_le {β : Type} {C : Set β} (hfin : C.Finite) {L₀ : ℕ} (hcard : C.ncard ≤ L₀)
    (P : β → E → Prop) {e : ℝ≥0∞}
    (h : ∀ q ∈ C, (Fintype.card E : ℝ≥0∞)⁻¹ *
      ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) ≤ e) :
    (Fintype.card E : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c).card : ℝ≥0∞) ≤ L₀ * e := by
  classical
  let s := hfin.toFinset
  have hsub : (Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c) ⊆
      s.biUnion fun q ↦ Finset.univ.filter fun c ↦ P q c := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨q, hq, hp⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨q, hfin.mem_toFinset.mpr hq, by simpa using hp⟩
  calc (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c).card : ℝ≥0∞)
      ≤ (Fintype.card E : ℝ≥0∞)⁻¹ *
          ∑ q ∈ s, ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) := by
        gcongr
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ = ∑ q ∈ s, (Fintype.card E : ℝ≥0∞)⁻¹ *
          ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) := Finset.mul_sum _ _ _
    _ ≤ ∑ _q ∈ s, e := Finset.sum_le_sum fun q hq ↦ h q (hfin.mem_toFinset.mp hq)
    _ = s.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L₀ * e := by
        gcongr
        rw [← Set.ncard_eq_toFinset_card C hfin]
        exact_mod_cast hcard

/-! lvm (WP-2): the source states the two keep/escape facts from a typed component's security
(`Typed.Security` of `Typed.sendChecked` / `Typed.sampleChallenge`, through
`Typed.sendChecked_reflect` and `Typed.sample_escape`, ArkLib's typed front, cut). Here they are
stated from what those securities give: for a message, the reflection of the output relation into
the input relation; for a challenge, the per-oracle fraction of challenges that carry a statement
outside the input relation into the output relation. The VCVio probability
`Pr{let c ← $ᵗ E}[p c]` is the fraction `|E|⁻¹ · #{c | p c}` throughout. -/

section Say

variable {S T : Type} {ι : Type} {O : ι → Type}
  {relIn : Set ((S × ∀ i, O i) × Unit)} {relOut : Set ((T × ∀ i, O i) × Unit)}

/-- **A checked message keeps doom**: when the output relation at `t` reflects into the input
relation at `s` (what a checked message's security gives for a message passing the check), a
doomed `s` makes a doomed `t`. -/
theorem say_keep {C : Set (∀ i, O i)} {s : S} {t : T}
    (hrefl : ∀ o, ((t, o), ()) ∈ relOut → ((s, o), ()) ∈ relIn)
    (hpre : RelDoom C relIn s) : RelDoom C relOut t := fun o ho hout ↦
  hpre o ho (hrefl o hout)

end Say

section Draw

variable {S T : Type} {ι : Type} {O : ι → Type} {f : E → T}
  {relIn : Set ((S × ∀ i, O i) × Unit)} {relOut : Set ((T × ∀ i, O i) × Unit)}

open Classical in
/-- **A challenge escapes doom** with probability at most `L₀ · e` over at most `L₀`
candidates, when for every oracle outside the input relation at `s` at most a fraction `e` of
the challenges carry it into the output relation (what a checked challenge's security at error
`e` gives). -/
theorem draw_escape_le {C : Set (∀ i, O i)} (hfin : C.Finite) {L₀ : ℕ} (hcard : C.ncard ≤ L₀)
    {s : S} {e : ℝ≥0∞}
    (hesc : ∀ o, ((s, o), ()) ∉ relIn → (Fintype.card E : ℝ≥0∞)⁻¹ *
      ((Finset.univ.filter fun c ↦ ((f c, o), ()) ∈ relOut).card : ℝ≥0∞) ≤ e)
    (hpre : RelDoom C relIn s) :
    (Fintype.card E : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun c ↦ ¬ RelDoom C relOut (f c)).card : ℝ≥0∞) ≤ L₀ * e := by
  have hev : (Finset.univ.filter fun c ↦ ¬ RelDoom C relOut (f c)) =
      Finset.univ.filter fun c ↦ ∃ o ∈ C, ((f c, o), ()) ∈ relOut := by
    ext c
    simp [RelDoom]
  rw [hev]
  exact card_exists_le hfin hcard (fun o c ↦ ((f c, o), ()) ∈ relOut) fun o ho ↦
    hesc o (hpre o ho)

/-- A count of challenges as a fraction: at most `N` of them is a fraction at most `N / |E|`. -/
theorem inv_card_mul_card_le_of_natCard_le (p : E → Prop) [DecidablePred p] {N : ℕ}
    (h : Nat.card {c // p c} ≤ N) :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter p).card : ℝ≥0∞) ≤
      (((N : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  have hE : (Fintype.card E : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card, ENNReal.coe_div hE, ENNReal.coe_natCast, ENNReal.coe_natCast,
    div_eq_mul_inv, mul_comm]
  gcongr
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact_mod_cast h

end Draw

end
end LeanVM.Protocol.EndToEnd.Front
