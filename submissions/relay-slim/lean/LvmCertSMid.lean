-- WP-14 (ASM). New for lvm (O6 glue): `MidSpec` for middle phases of the shape
-- `bus >>= kg >>= ret (assemble …)` from a bus/table phase specification (WP-9b `midBusTableSpecS`
-- form), a Keccak phase specification (WP-8 `kgSpec` form, framed with `RootShape`) and the
-- semantic link of the assembled stack claims.
import LvmCertSExt

/-!
# The middle phases' specification from its phases (O6 glue)

**`midSpecOf`**: for `mid x = busP x >>= fun a ↦ kgP >>= fun k ↦ ret (asm x a k)`, a specification of
`busP x` from `RootShape ∧ Doomed candPairs (Gb x ∧ Gk)` to `Doomed candPairs (B x a ∧ Gk) ∧
RootShape`, one of `kgP` from `Doomed candPairs (Gk ∧ B x a)` to `Doomed candPairs (Kc k ∧ B x a)`
(`kgP` commits nothing, so `RootShape` is framed across it), and the link "the assembled claims hold
on a pair ⇒ `Kc k ∧ B x a` on it" with the claims multiaffine and at most `2^63` give
`MidSpec mid (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk (qm, qr)) εS Lb`. **`midShapeOf`**: its shape.
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front (Doomed)
open scoped ENNReal

/-- A pair of candidates. -/
abbrev Pair : Type := Column CMain.nu20 × Column 19

theorem rootShape_append' {h₀ l : List Ev} (hl : commits l = []) (hr : RootShape h₀) :
    RootShape (h₀ ++ l) := by
  obtain ⟨Wm, Wr, hc, hw⟩ := hr
  exact ⟨Wm, Wr, by rw [LeanVM.Protocol.Whir.Sound.commits_append, hl, List.append_nil, hc], hw⟩

section Glue

variable {α κ : Type} {busP : List UInt8 → VerifierProgram α} {kgP : VerifierProgram κ}
  {asm : List UInt8 → α → κ → OpenClaims}
  {Gb : List UInt8 → Pair → Prop} {Gk : Pair → Prop} {B : List UInt8 → α → Pair → Prop}
  {Kc : κ → Pair → Prop} {Lb Lk : ℝ≥0∞}

/-- The assembled claims' doom: a pair failing `Kc ∧ B` fails one of the assembled claims. -/
theorem openPost_of {x : List UInt8} {a : α} {k : κ} {h : List Ev}
    (hasm : ∀ p : Pair, (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc k p ∧ B x a p)
    (hside : (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧
      (asm x a k).1.length ≤ 2 ^ 63 ∧ (asm x a k).2.length ≤ 2 ^ 40)
    (hD : Doomed candPairs (fun p ↦ Kc k p ∧ B x a p) h) (hR : RootShape h) :
    OpenPost (asm x a k) h := by
  refine ⟨fun p hp ↦ ?_, hR, hside⟩
  by_contra hno
  push Not at hno
  exact hD p hp (hasm p hno.1 hno.2)

/-- **`MidSpec` from the phases** (see the module docstring). -/
noncomputable def midSpecOf
    (SB : ∀ x (T : ℝ≥0∞), T ≤ εS → Spec (busP x)
      (fun h ↦ RootShape h ∧ Doomed candPairs (fun p ↦ Gb x p ∧ Gk p) h)
      (fun a h ↦ Doomed candPairs (fun p ↦ B x a p ∧ Gk p) h ∧ RootShape h) εS Lb T)
    (SK : ∀ x a (T : ℝ≥0∞), T ≤ εS → Spec kgP (Doomed candPairs (fun p ↦ Gk p ∧ B x a p))
      (fun k h ↦ Doomed candPairs (fun p ↦ Kc k p ∧ B x a p) h) εS Lk T)
    (hkc : kgP.NoCommit) (hLk : Lk ≤ εS)
    (hasm : ∀ x a k (p : Pair), (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc k p ∧ B x a p)
    (hside : ∀ x a k, (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 63 ∧
      (asm x a k).2.length ≤ 2 ^ 40) :
    MidSpec (fun x ↦ busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k))
      (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk (qm, qr)) εS Lb := fun x T hT ↦
  ⟨((SB x Lk hLk).bind' fun a ↦
      (((SK x a T hT).frame RootShape fun _ _ hl hr ↦
          rootShape_append' (hkc.reach_commits hl) hr).mono
        (fun h hp ↦ ⟨Doomed.mono hp.1 fun p hq ↦ ⟨hq.2, hq.1⟩, hp.2⟩) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl).bind' fun k ↦
      (Spec.ret (Post := OpenPost) (εmax := εS) (T := T) (asm x a k)).mono
        (fun h hp ↦ openPost_of (hasm x a k) (hside x a k) hp.1 hp.2) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl).mono
    (fun h hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

/-- **`MidShape` of the composed phases.** -/
theorem midShapeOf (hbc : ∀ x, (busP x).NoCommit) (hbg : ∀ x, (busP x).NoGrind)
    (hkc : kgP.NoCommit) (hkg : kgP.NoGrind)
    (hret : ∀ x l cl, (busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k)).after l =
      some (.ret cl) → ∀ c ∈ cl.1, IsMultiaffine 19 c.1) :
    MidShape (fun x ↦ busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k)) where
  noCommit x := NoCommit.bind (hbc x) fun _ ↦ NoCommit.bind hkc fun _ ↦ trivial
  noGrind x := NoGrind.bind (hbg x) fun _ ↦ NoGrind.bind hkg fun _ ↦ trivial
  recAffine := hret

/-- The returned claims of the composed phases are the assembled ones. -/
theorem ret_assembled {x : List UInt8} {l : List Ev} {cl : OpenClaims}
    (h : (busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k)).after l =
      some (.ret cl)) : ∃ a k, cl = asm x a k := by
  obtain ⟨a, -, l₂, -, -, h2⟩ := after_bind_ret (p := busP x) h
  obtain ⟨k, -, l₃, -, -, h3⟩ := after_bind_ret (p := kgP) h2
  cases l₃ with
  | nil => simp [VerifierProgram.after] at h3; exact ⟨a, k, h3.symm⟩
  | cons e es => cases e <;> simp [VerifierProgram.after] at h3

end Glue

end Lvm.ASM
