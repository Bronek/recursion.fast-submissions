-- New for lvm2 (X-REC2-CERT, stage S4): the doom of `C_rec`'s level-1 commitment in `P_S` (the third
-- part of the certificate's doom, joined to `psSpec` and `resSpec` by `Spec.or`). It creates the doom
-- at the commitment of `C_rec`'s level-1 oracle (`LvmWhir2Mid.midTailFarSpec`, `Spec.commitP`) and
-- reuses WP-7's final-level specification (`finSpec`) at level 1 after the level-0 query group.
import LvmCertSRes
import LvmWhir2Mid

/-!
# The level-1 commitment's doom

`psSpec`'s doom gives a good candidate `q` of `C_rec`'s root and `resSpec`'s gives `Enc₁(f₂)` in the
list of the level-1 word folded by `α₁`, but nothing ties the level-1 word to `q`. The extractor's
facts (`ud_extract_rec20`, `LvmWhirDoom2`) need **`¬ MidDoomUd`**: some member of the level-1 list
has a level-0 encoding close to the root word folded by `α₀`. This module adds that doom:

* `recMid2Spec`: a two-level stacked opening from no doom; the batching challenge, the first round
  polynomial and the level-0 fold rounds are dead; at the level-1 commitment the doom `FarC` is
  created (bookkeeping of the level-0 folds and `FarU`: every level-1 list member meeting the running
  claim is far from the folded root word), then the level-0 query group escapes with probability
  at most `eQueryUd` into `LevelPre` of level 1, and WP-7's `finSpec` (level 1) rejects except with
  its groups' probabilities (fold `eFold P₁ 4`, queries `eQueryFinal P₁ 156`, tail).
* `midSpec1`: `P_S` from no doom: roots and middle phases dead, `C_rec`'s opening by `recMid2Spec`
  (dead when the claims are not multiaffine), `C_main`'s opening dead.
* `midSpec1_D`: at the boundary right after the level-1 commitment, `FarC` is doom; `MidDoomUd`
  with the bookkeeping gives `FarC` (`farU_of_midDoom`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound
open scoped ENNReal

/-- The doom of `Spec.commitP` right after the commitment. -/
theorem commitP_D_one {Pre : List Ev → Prop} {Post : Unit → List Ev → Prop} {εmax T : ℝ≥0∞}
    (ht w : ℕ) (h : ∀ h₀ word, Pre h₀ → WellShaped w word → Post () (h₀ ++ [Ev.commit ht w word]))
    (hT : T ≤ εmax) (h₀ : List Ev) (e : Ev) :
    (Spec.commitP (Pre := Pre) (Post := Post) ht w h hT).D h₀ [e] ↔ Post () (h₀ ++ [e]) :=
  Iff.rfl

/-- A completed commitment is one commitment event. -/
theorem readCommitment_after {ht w : ℕ} {l : List Ev}
    (h : (readCommitment ht w).after l = some (.ret ())) : ∃ W, l = [Ev.commit ht w W] := by
  rcases l with _ | ⟨e, _ | ⟨e', es⟩⟩
  · simp [readCommitment, VerifierProgram.after] at h
  · cases e <;> simp [readCommitment, VerifierProgram.after] at h
    rename_i h' w' W
    exact ⟨W, by simp_all⟩
  · cases e <;> simp [readCommitment, VerifierProgram.after] at h

/-! ## A two-level stacked opening, doom at the level-1 commitment -/

section Mid2

variable (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
  (hc : cfg.levels = [level, next]) (P₀ P₁ : LevelCode)
  (cl : List LeanVM.Protocol.Verifier.StackClaim) {εmax : ℝ≥0∞}
  (H : ∀ ρ, MidHyp cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ (batW cl ρ) P₀ P₁ level next 0)
  (hg : cfg.grind ≤ 192) (hκ : P₀.κ = next.fold + P₁.κ)
  (hQlt : eQueryUd P₀ P₁ level.queries < 1)
  (hεQ : (2 : ℝ≥0∞)⁻¹ ^ cfg.grind * eQueryUd P₀ P₁ level.queries ≤ εmax)
  (K : ∀ ρ s', Spec (whirLevelsUd cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ cfg.grind cfg.direct
      (batW cl ρ)
      (0 + 1) [next] s')
    (fun h ↦ LevelPre cfg.μ level.fold (batW cl ρ) (0 + 1) P₁ next.fold (0 + level.fold) s'
      (viewC cfg.c₀ cfg.n₀ (commits h)))
    (fun _ _ ↦ False) εmax εmax 0)

/-- **A two-level stacked opening from no doom**, doom created at the level-1 commitment. -/
noncomputable def recMid2Spec :
    Spec (verifyStackedUd cfg cl) (fun _ ↦ False) (fun _ _ ↦ False) εmax 0 0 :=
  Spec.congr (stacked_two_eq cfg level next hc cl).symm
    ((Spec.dead (p := sampleChallenge) (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun ρ ↦
      (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun quad ↦
        (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun r ↦
          midTailFarSpec (H ρ) hg hκ hQlt hεQ (K ρ) r)

/-- **The doom right after the level-1 commitment** is `FarC`. -/
theorem recMid2Spec_D {h₀ lq lf lc : List Ev} {ρ : E} {quad : List E} {r : WhirStateT × List E}
    (hq : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).after lq =
      some (.ret quad))
    (hf : (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (cfg.μ - r.1.folds.length - next.fold + next.logInvRate)
      (3 * 2 ^ next.fold)).after lc = some (.ret ())) :
    (recMid2Spec cfg level next hc P₀ P₁ cl H hg hκ hQlt hεQ K).D h₀
        ([Ev.sample ρ] ++ (lq ++ (lf ++ lc))) ↔
      FarC cfg.μ level.fold (batW cl ρ) 0 P₀ P₁ level.fold next.fold 0 hκ r
        (viewC cfg.c₀ cfg.n₀ (commits (h₀ ++ [Ev.sample ρ] ++ lq ++ lf ++ lc))) := by
  obtain ⟨W, rfl⟩ := readCommitment_after hcm
  rw [recMid2Spec, Spec.congr_D, bind_D_after _ _ (rfl : sampleChallenge.after [Ev.sample ρ] = _)
    (by simp), bind_D_after _ _ hq (by simp), bind_D_after _ _ hf (by simp), midTailFarSpec,
    show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_ret _ _ hcm, commitP_D_one]
  constructor
  · exact fun h ↦ by simpa only [List.append_assoc] using h.1
  · intro h
    have h' : FarC cfg.μ level.fold (batW cl ρ) 0 P₀ P₁ level.fold next.fold 0 hκ r
        (viewC cfg.c₀ cfg.n₀ (commits (h₀ ++ [Ev.sample ρ] ++ lq ++ lf ++
          [Ev.commit (cfg.μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
            W]))) := h
    simp only [List.append_assoc] at h' ⊢
    exact ⟨h', Spec.start_D _ _ (by simpa only [List.append_nil] using h')⟩

end Mid2

/-! ## P20 -/

theorem midHyp0_rec20 (cl : List LeanVM.Protocol.Verifier.StackClaim)
    (hcl : ∀ c ∈ cl, IsMultiaffine 19 c.1) (ρ : E) :
    MidHyp cfgRec20G.μ recLevel0.fold cfgRec20G.per cfgRec20G.c₀ cfgRec20G.n₀ (batW cl ρ)
      (codesRec20 0) (codesRec20 1) recLevel0 recLevel1 0 :=
  ⟨isMultiaffine_batched cl hcl ρ, by decide, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    le_rfl⟩

/-- `C_rec`'s level-0 message variables: the level-1 fold and the level-1 code's. -/
theorem hκ_rec20 : (codesRec20 0).κ = recLevel1.fold + (codesRec20 1).κ := rfl

theorem hQlt0_20 : eQueryUd (codesRec20 0) (codesRec20 1) recLevel0.queries < 1 :=
  eQuery_rec20G.1.trans_lt (inv_two_pow_lt_one (by norm_num))

theorem hεQ0_20 :
    (2 : ℝ≥0∞)⁻¹ ^ cfgRec20G.grind * eQueryUd (codesRec20 0) (codesRec20 1) recLevel0.queries ≤ εS :=
  (disc_le 14 eQuery_rec20G.1).trans pow129_le_εS

theorem hεF1_20 : eFold (codesRec20 1) recLevel1.fold ≤ εS :=
  (eFold_rec20_1.trans (inv_two_pow_anti (by norm_num))).trans pow129_le_εS

section Concrete

attribute [local irreducible] verifyStackedUd verifyStackedJ recMid2Spec midTailFarSpec finSpec

/-- WP-7's final-level specification at `C_rec`'s level 1 (P20). -/
noncomputable def fin1_20 (cl : List LeanVM.Protocol.Verifier.StackClaim)
    (hcl : ∀ c ∈ cl, IsMultiaffine 19 c.1) (ρ : E) (s' : WhirStateT) :
    Spec (whirLevelsUd cfgRec20G.μ recLevel0.fold cfgRec20G.per cfgRec20G.c₀ cfgRec20G.n₀
        cfgRec20G.grind cfgRec20G.direct (batW cl ρ) (0 + 1) [recLevel1] s')
      (fun h ↦ LevelPre cfgRec20G.μ recLevel0.fold (batW cl ρ) (0 + 1) (codesRec20 1)
        recLevel1.fold (0 + recLevel0.fold) s' (viewC cfgRec20G.c₀ cfgRec20G.n₀ (commits h)))
      (fun _ _ ↦ False) εS εS 0 :=
  finSpec (finHyp1_rec20 cl hcl ρ) hg20 hεF1_20 hQlt1_20 hεQ1_20 hεT20 s'

open Classical in
/-- **`C_rec`'s opening at P20 from no doom**, doom created at the level-1 commitment (dead when
the claims are not multiaffine). -/
noncomputable def recMid20 (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    Spec (verifyStackedUd cfgRec20G cl) (fun _ ↦ False) (fun _ _ ↦ False) εS 0 0 :=
  if hcl : ∀ c ∈ cl, IsMultiaffine 19 c.1 then
    recMid2Spec cfgRec20G recLevel0 recLevel1 rec20_levels (codesRec20 0) (codesRec20 1) cl
      (midHyp0_rec20 cl hcl) hg20 hκ_rec20 hQlt0_20 hεQ0_20 (fin1_20 cl hcl)
  else Spec.dead

/-- The openings from no doom, doom only `C_rec`'s level-1 commitment's. -/
noncomputable def openMid (cl : OpenClaims) :
    Spec (openProg cl) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0 :=
  (recMid20 cl.1).bind' fun _ ↦ Spec.dead

/-- **The level-1 commitment's doom of `P_S`** (from no doom). -/
noncomputable def midSpec1 (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    Spec (PSWith mid x) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0 :=
  (Spec.bind' (Spec.dead (p := commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G)
      (Post := fun _ _ ↦ False) (L := 0) (T := 0)) fun _ ↦
    Spec.bind' (Spec.dead (p := mid x) (Post := fun _ _ ↦ False) (L := 0) (T := 0)) fun cl ↦
      openMid cl).congr (PSWith_eq mid x).symm

/-- **The level-1 commitment's doom at the boundary right after it**: a run through the roots
(`hroots`), the middle phases (`hm`), `C_rec`'s batching challenge, first round polynomial (`hq`),
level-0 fold rounds (`hf`) and level-1 commitment (`hcm`), with multiaffine claims, is doomed there
if `FarC` holds. -/
theorem midSpec1_D (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8)
    {hr lm lq lf lc : List Ev} {cl : OpenClaims} {ρ : E} {quad : List E}
    {r : WhirStateT × List E}
    (hroots : (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G).after hr = some (.ret ()))
    (hm : (mid x).after lm = some (.ret cl))
    (hcl : ∀ c ∈ cl.1, IsMultiaffine 19 c.1)
    (hq : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq =
      some (.ret quad))
    (hf : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).after lc = some (.ret ()))
    (hF : FarC 19 6 (batW cl.1 ρ) 0 (codesRec20 0) (codesRec20 1) 6 4 0 hκ_rec20 r
      (viewC 1 2 (commits (hr ++ lm ++ [Ev.sample ρ] ++ lq ++ lf ++ lc)))) :
    (midSpec1 mid x).D [] (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ lc))))) := by
  have hne : lc ≠ [] := by
    obtain ⟨W, rfl⟩ := readCommitment_after hcm; simp
  rw [midSpec1, Spec.congr_D]
  rw [show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_after _ _ hroots (by simp)]
  rw [show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_after _ _ hm (by simp)]
  obtain ⟨g', hafter⟩ := after_stacked_two_commit cfgRec20G recLevel0 recLevel1 rec20_levels cl.1
    hq hf hcm
  rw [openMid, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ hafter (queryFrag_bind_ne_ret _ _ _ _ _ (by decide) _)]
  rw [recMid20, dif_pos hcl]
  refine (recMid2Spec_D cfgRec20G recLevel0 recLevel1 rec20_levels (codesRec20 0) (codesRec20 1)
    cl.1 (midHyp0_rec20 cl.1 hcl) hg20 hκ_rec20 hQlt0_20 hεQ0_20 (fin1_20 cl.1 hcl) hq hf hcm).2 ?_
  simp only [List.nil_append, List.append_assoc] at hF ⊢
  exact hF

end Concrete

end Lvm.ASM
