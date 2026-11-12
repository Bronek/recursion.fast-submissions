-- New for lvm (WP-14a): V_S's stream reads refine the verifier language's events (scalars,
-- challenges, caps, positions, openings), through the byte decoders' bridges (LvmVEqCodec).
import LvmVEqCore
import LvmVEqCodec
import LvmWhirProg

/-!
# The primitives

`DM.readE`, `sampleE`, `readEs n`, `samples n` refine `readScalar`, `sampleChallenge`,
`readScalars n`, `sampleChallenges n` with the values related by `FE.toExt3`; `skip` of a cap's
bytes refines `readCommitment`; `positionsR L` refines `samplePositions 8 L.height L.t` with the same
positions; `openingR L` refines `queryOpenings i ps` with the rows read at V_S's row offsets. Every
native primitive never clears a failed check (`MonoD`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile

/-! ## `MonoD` of the primitives -/

theorem monoD_readE : MonoD DM.readE := fun _ _ h ↦ h
theorem monoD_sampleE : MonoD DM.sampleE := fun _ _ h ↦ h
theorem monoD_skip (n : ℕ) : MonoD (DM.skip n) := fun _ _ h ↦ h

theorem monoD_readEs : ∀ n, MonoD (DM.readEs n)
  | 0 => MonoD.pure _
  | n + 1 => monoD_readE.bind fun _ ↦ (monoD_readEs n).bind fun _ ↦ MonoD.pure _

theorem monoD_samples : ∀ n, MonoD (DM.samples n)
  | 0 => MonoD.pure _
  | n + 1 => monoD_sampleE.bind fun _ ↦ (monoD_samples n).bind fun _ ↦ MonoD.pure _

theorem monoD_positionsAux (h : ℕ) : ∀ n rem, MonoD (DM.positionsAux h n rem)
  | 0, _ => MonoD.pure _
  | n + 1, _ => monoD_sampleE.bind fun _ ↦ (monoD_positionsAux h n _).bind fun _ ↦ MonoD.pure _

theorem monoD_positionsR (L : Level) : MonoD (DM.positionsR L) := monoD_positionsAux _ _ _

theorem monoD_openingAux (L : Level) : ∀ n, MonoD (DM.openingAux L n)
  | 0 => MonoD.pure _
  | n + 1 => by
    refine MonoD.bind ?_ fun _ ↦ (monoD_openingAux L n).bind fun _ ↦ MonoD.pure _
    exact fun _ _ h ↦ h

theorem monoD_openingR (L : Level) : MonoD (DM.openingR L) := by
  refine MonoD.bind ?_ fun _ ↦ monoD_openingAux L _
  intro _ s h
  simp only [runD, modify, modifyGet, MonadStateOf.modifyGet] at h
  exact (Bool.and_eq_true _ _ ▸ h).1

section Prim

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **A scalar.** -/
theorem ref_readE : RefAt cap occ shp sig DM.readE VerifierProgram.readScalar fun x y ↦ y = FE.toExt3 x :=
  fun s _ ↦ ⟨_, rfl, rfl, rfl, (toExt3_feAt sig _).symm⟩

/-- **A challenge.** -/
theorem ref_sampleE :
    RefAt cap occ shp sig DM.sampleE VerifierProgram.sampleChallenge fun x y ↦ y = FE.toExt3 x :=
  fun s _ ↦ ⟨_, rfl, rfl, rfl, (toExt3_feAt_chal sig _).symm⟩

/-- **Scalars.** -/
theorem ref_readEs : ∀ n, RefAt cap occ shp sig (DM.readEs n) (VerifierProgram.readScalars n)
    fun xs ys ↦ ys = xs.map FE.toExt3
  | 0 => RefAt.pure rfl
  | n + 1 => by
    refine RefAt.bind (fun _ ↦ (monoD_readEs n).bind fun _ ↦ MonoD.pure _) ref_readE ?_
    intro x y hxy
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_readEs n) ?_
    intro xs ys hs
    exact RefAt.pure (by simp [hxy, hs])

/-- **Challenges.** -/
theorem ref_samples : ∀ n, RefAt cap occ shp sig (DM.samples n) (VerifierProgram.sampleChallenges n)
    fun xs ys ↦ ys = xs.map FE.toExt3
  | 0 => RefAt.pure rfl
  | n + 1 => by
    refine RefAt.bind (fun _ ↦ (monoD_samples n).bind fun _ ↦ MonoD.pure _) ref_sampleE ?_
    intro x y hxy
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_samples n) ?_
    intro xs ys hs
    exact RefAt.pure (by simp [hxy, hs])

/-- **A cap**: its bytes skipped. -/
theorem ref_skip {ht w n : ℕ} (h : n = 32 * 2 ^ cap ht w) :
    RefAt cap occ shp sig (DM.skip n) (VerifierProgram.readCommitment ht w) fun _ _ ↦ True := by
  intro s _
  subst h
  exact ⟨(), rfl, rfl, rfl, trivial⟩

/-- **The positions**: `⌈t/8⌉` challenges, the same bit fields. -/
theorem ref_positionsAux (h : ℕ) : ∀ (n fuel rem : ℕ), rem ≤ positionsPerAnswer * n → n ≤ fuel →
    (n = 0 ∨ positionsPerAnswer * (n - 1) < rem) →
    RefAt cap occ shp sig (DM.positionsAux h n rem)
      (LeanVM.Protocol.Verifier.samplePositionsAux positionsPerAnswer h fuel rem) fun ps ps' ↦ ps' = ps
  | 0, fuel, rem, h1, _, _ => by
    have hr : rem = 0 := by simpa [positionsPerAnswer] using h1
    subst hr
    cases fuel with
    | zero => exact RefAt.pure rfl
    | succ f => exact RefAt.pure rfl
  | n + 1, fuel, rem, h1, h2, h3 => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hrem : rem ≠ 0 := by
      rcases h3 with h3 | h3
      · omega
      · simp only [positionsPerAnswer] at h3; omega
    simp only [LeanVM.Protocol.Verifier.samplePositionsAux, hrem, ↓reduceIte]
    refine RefAt.bind (fun _ ↦ (monoD_positionsAux h n _).bind fun _ ↦ MonoD.pure _) ref_sampleE ?_
    intro x y hxy
    subst hxy
    refine RefAt.bind (fun _ ↦ MonoD.pure _)
      (ref_positionsAux h n f _ ?_ (by omega) ?_) ?_
    · simp only [positionsPerAnswer] at h1 ⊢; omega
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · exact .inl hn
      · right; simp only [positionsPerAnswer] at h1 h3 ⊢
        rcases h3 with h3 | h3
        · omega
        · omega
    · intro ps ps' hps
      subst hps
      refine RefAt.pure ?_
      simp [eToNat_toExt3, positionsPerAnswer]

/-- **The positions of a level.** -/
theorem ref_positionsR (L : Level) :
    RefAt cap occ shp sig (DM.positionsR L)
      (LeanVM.Protocol.Verifier.samplePositions positionsPerAnswer L.height L.t) fun ps ps' ↦ ps' = ps :=
  ref_positionsAux _ _ _ _ (by simp only [positionsPerAnswer]; omega)
    (by simp only [positionsPerAnswer]; omega)
    (by
      rcases Nat.eq_zero_or_pos ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) with h | h
      · exact .inl h
      · right; simp only [positionsPerAnswer] at h ⊢; omega)

theorem openingAux_succ (L : Level) (n : ℕ) (s : RS) :
    runD (DM.openingAux L (n + 1)) sig s =
      ((s.ent + 8) :: (runD (DM.openingAux L n) sig
          { s with ent := s.ent + 40 + L.row + 104 * L.path }).1,
        (runD (DM.openingAux L n) sig { s with ent := s.ent + 40 + L.row + 104 * L.path }).2) := rfl

/-- The rows `openingAux` points at, read as the compiled verifier reads them. -/
theorem opRows_openingAux (L : Level) (wd oc : ℕ) (hrow : L.row = 8 * min oc wd) :
    ∀ (n : ℕ) (s : RS), (opRows sig wd oc L.path n s.ent).2 = (runD (DM.openingAux L n) sig s).2.ent ∧
      (opRows sig wd oc L.path n s.ent).1 =
        (runD (DM.openingAux L n) sig s).1.map (fun o ↦ padAt sig o wd oc) ∧
      (runD (DM.openingAux L n) sig s).2.msg = s.msg
  | 0, s => ⟨rfl, rfl, rfl⟩
  | n + 1, s => by
    obtain ⟨h1, h2, h3⟩ := opRows_openingAux L wd oc hrow n
      { s with ent := s.ent + 40 + L.row + 104 * L.path }
    rw [openingAux_succ]
    simp only [opRows, ← hrow]
    exact ⟨h1, by rw [h2]; rfl, h3⟩

/-- **An opening**: the rows at V_S's row offsets, with the commitment's shape and occupancy. -/
theorem ref_openingR (L : Level) {i : ℕ} {ps : List ℕ} {wd : ℕ} (hshp : shp i = (L.height, wd))
    (hrow : L.row = 8 * min (occ L.height wd) wd) (hpath : L.path = L.height - cap L.height wd)
    (hlen : ps.length = L.t) :
    RefAt cap occ shp sig (DM.openingR L) (VerifierProgram.queryOpenings i ps)
      fun offs rows ↦ rows = offs.map fun o ↦ padAt sig o wd (occ L.height wd) := by
  intro s _
  have hsplit : runD (DM.openingR L) sig s =
      runD (DM.openingAux L L.t) sig { s with ok := s.ok && s.msg == 0 } := rfl
  obtain ⟨h1, h2, h3⟩ := opRows_openingAux (sig := sig) L wd (occ L.height wd) hrow L.t
    { s with ok := s.ok && s.msg == 0 }
  have hiv : ivp cap occ shp (VerifierProgram.queryOpenings i ps) sig s =
      (some (opRows sig wd (occ L.height wd) L.path L.t s.ent).1,
        { s with ent := (opRows sig wd (occ L.height wd) L.path L.t s.ent).2 }) := by
    simp only [VerifierProgram.queryOpenings, ivp, hshp, hlen, ← hpath]
  rw [hsplit, hiv]
  exact ⟨_, rfl, h1, h3.symm, h2⟩

end Prim

end Lvm.VEq
