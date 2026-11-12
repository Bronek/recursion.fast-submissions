-- New for lvm (WP-14a, H4): V_S's stacked WHIR openings (phases 8–9: LvmDecideWhir `verifyStackedOpening`,
-- `direct = false`, A20) refine WP-7's `verifyStackedUd cfgRec20` / `cfgMain24` (lvm2 S2) (LvmWhirProg, LvmWhirParams)
-- event for event; the level loop is generic in a level correspondence and in the PoW bits `g`, instantiated at
-- P20 and at the grinding test set P20G (g = 14). lvm2 JB-VQP: with `ood` the level loop refines JB-L's
-- `whirLevelsJ` (`verifyStackedJ`); at P20 (J1) `C_main`'s opening is `verifyStackedJ (cfgMain24J 3)`.
import LvmVEqWhirPure
import LvmWhirParams24
import LvmWhirParamsG
import LvmWhirParamsJ

/-!
# The stacked WHIR openings: V_S refines the verifier language

* `LevelOK`, `NextOK`, `LevelsCorr`: a native level (`Lvm.Level`: fold, height, `t`, row bytes, path,
  next cap) against a language level (`Whir.Level`: fold, rate, queries) and the commitment table
  `cap shp` at the commitment index `cidx c₀ n₀ j` it opens;
* `ref_foldRounds`, `ref_tailRounds`, `ref_grindPreR`, `ref_powCheckR` (PI-GRIND: the separator,
  the nonce, the PoW challenge and its check), `ref_whirLevels` (generic loop, `direct = false`,
  generic in the PoW bits `g`), `ref_verifyWhir`, `ref_verifyStacked`; `monoD_*` (V_S's steps never
  clear a failed check);
* with out-of-domain samples (lvm2 JB-VQP; V_S's `whirLevels … ood` with `ood = true`, the DSL's
  `whirLevelsJ`): `ref_oodStep` (the `κ` samples, the answer, the intro polynomial), `wrel_glue2`
  (the OOD claim at `λ¹`, the queries at `λ²`), `ref_whirLevelsJ`, `ref_verifyWhirJ`,
  `ref_verifyStackedJ`; the same `LevelsCorr` (the OOD point has the folded message's variables
  on both sides);
* at P20 (J1): `corrRec20`, `corrMain24` (by `decide` on the literal levels; `C_main` against
  `cfgMain24J 3`), **`ref_dOpen`** (`verifyStackedUd cfgRec20G`, then `verifyStackedJ (cfgMain24J 3)`),
  `monoD_dOpen`;
* at the grinding test set P20G (PI-GRIND, `g = 14`, not frozen): `corrRec20G`, `corrMain24G`,
  **`ref_dOpenG`** against `cfgRec20G`, `cfgMain24G`.

Event order (both sides): per level the fold rounds (challenge, round polynomial), the next cap
(`skip` vs `readCommitment`) or the residual, with OOD the point, its answer and intro polynomial,
the proof of work (with `g > 0`: the separator, the
nonce, the PoW challenge and its check), the positions, `λ`, the openings, the intro
polynomial; after the final level the tail rounds and the terminal check. V_S's `tailRounds 0`
(`require false`) and `whirLevels []` (`require false`) never end `ok`, so the DSL's `target`
(returned by `tailRoundsT 0`, not tracked by V_S) is never observed where V_S accepts.
The round-polynomial step (`ref_rpW`) is a local copy of H1's `ref_sumcheckRoundPoly` at `none`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (WhirStateT foldRoundsT tailRoundsT glueT whirLevelsUd verifyWhirUd
  verifyStackedUd UdConfig cidx whirLevelsJ verifyWhirJ verifyStackedJ WhirConfig)
open LeanVM.Protocol.Whir.Sound (cfgRec20 cfgMain24 cfgRec20G cfgMain24G cfgMain24J)
open Lvm.M3 (tE_add tE_mul tE_zero tE_one FE_eq_of_beq)

/-! ## The level correspondence -/

/-- The leaf width (in `K` words) of level `j`'s commitment: `2^ℓ` at the root, `3·2^ℓ` later. -/
def wdOf (j fold : ℕ) : ℕ := if j = 0 then 2 ^ fold else 3 * 2 ^ fold

/-- **A native level against a language level**, level `j` of an opening of `logN` variables after
`F` folded variables, opening commitment `cidx c₀ n₀ j` of the table `cap shp`. -/
structure LevelOK (cap : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (logN c₀ n₀ j F : ℕ) (L : Level)
    (W : Whir.Level) : Prop where
  fold : L.fold = W.fold
  t : L.t = W.queries
  height : L.height = logN - (F + L.fold) + W.logInvRate
  level : L.level = 0 ↔ j = 0
  shp : shp (cidx c₀ n₀ j) = (L.height, wdOf j L.fold)
  row : L.row = 8 * wdOf j L.fold
  path : L.path = L.height - cap L.height (wdOf j L.fold)

instance (cap : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (logN c₀ n₀ j F : ℕ) (L : Level) (W : Whir.Level) :
    Decidable (LevelOK cap shp logN c₀ n₀ j F L W) :=
  decidable_of_iff (L.fold = W.fold ∧ L.t = W.queries ∧ L.height = logN - (F + L.fold) + W.logInvRate ∧
      (L.level = 0 ↔ j = 0) ∧ shp (cidx c₀ n₀ j) = (L.height, wdOf j L.fold) ∧
      L.row = 8 * wdOf j L.fold ∧ L.path = L.height - cap L.height (wdOf j L.fold))
    ⟨fun ⟨a, b, c, d, e, f, g⟩ ↦ ⟨a, b, c, d, e, f, g⟩, fun ⟨a, b, c, d, e, f, g⟩ ↦ ⟨a, b, c, d, e, f, g⟩⟩

/-- The next level's cap: V_S skips `nodeBytes · 2^cap` bytes where the language reads the
commitment of `2^(κ − ℓ' + R')` leaves of `3·2^ℓ'` words. -/
def NextOK (cap : ℕ → ℕ → ℕ) (logN F' : ℕ) : List Level → List Whir.Level → Prop
  | N :: _, W :: _ => nodeBytes * 2 ^ N.cap = 32 * 2 ^ cap (logN - F' - W.fold + W.logInvRate) (3 * 2 ^ W.fold)
  | _, _ => True

/-- **The levels correspond**, from level `j` after `F` folded variables. -/
def LevelsCorr (cap : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (logN c₀ n₀ : ℕ) :
    ℕ → ℕ → List Level → List Whir.Level → Prop
  | _, _, [], [] => True
  | j, F, L :: Ls, W :: Ws => LevelOK cap shp logN c₀ n₀ j F L W ∧ NextOK cap logN (F + L.fold) Ls Ws ∧
      LevelsCorr cap shp logN c₀ n₀ (j + 1) (F + L.fold) Ls Ws
  | _, _, _, _ => False

/-! ## Steps that never clear a failed check -/

private theorem monoD_rpW (claim : FE) (e : Option FE) : MonoD (Lvm.sumcheckRoundPoly 3 claim e) := by
  cases e
  · exact monoD_readE.bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ MonoD.pure _
  · exact (monoD_readEs _).bind fun _ ↦ MonoD.pure _

theorem monoD_foldRounds : ∀ (n : ℕ) (s : Lvm.WhirState) (lf : List FE), MonoD (Lvm.foldRounds n s lf)
  | 0, _, _ => MonoD.pure _
  | n + 1, _, _ => monoD_sampleE.bind fun _ ↦ (monoD_rpW _ _).bind fun _ ↦ monoD_foldRounds n _ _

theorem monoD_tailRounds : ∀ (n : ℕ) (quad : List FE), MonoD (Lvm.tailRounds n quad)
  | 0, _ => (MonoD.require _).bind fun _ ↦ MonoD.pure _
  | n + 1, _ => monoD_sampleE.bind fun _ ↦ by
    dsimp only
    split
    · exact MonoD.pure _
    · exact (monoD_rpW _ _).bind fun _ ↦ (monoD_tailRounds n _).bind fun _ ↦ MonoD.pure _

theorem monoD_grindPreR (g : ℕ) : MonoD (DM.grindPreR g) := by
  unfold DM.grindPreR
  split
  · exact MonoD.pure _
  · exact monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ MonoD.pure _

theorem monoD_powCheckR (g : ℕ) : MonoD (DM.powCheckR g) := by
  unfold DM.powCheckR
  split
  · exact MonoD.pure _
  · exact monoD_sampleE.bind fun _ ↦ MonoD.require _

theorem monoD_oodStep (ood : Bool) (k : ℕ) : MonoD (Lvm.oodStep ood k) := by
  unfold Lvm.oodStep
  cases ood
  · rw [if_neg Bool.false_ne_true]
    exact MonoD.pure _
  · rw [if_pos rfl]
    exact (monoD_samples _).bind fun _ ↦ monoD_readE.bind fun _ ↦ (monoD_rpW _ _).bind fun _ ↦
      MonoD.pure _

theorem monoD_whirLevels (logN laneFolds : ℕ) (eb : List FE → FE) (direct : Bool) (g : ℕ) (ood : Bool) :
    ∀ (Ls : List Level) (s : Lvm.WhirState), MonoD (Lvm.whirLevels logN laneFolds eb direct g ood Ls s)
  | [], _ => MonoD.require _
  | [L], s => by
    rw [Lvm.whirLevels]
    refine (monoD_foldRounds _ _ _).bind fun r ↦ ?_
    obtain ⟨s', lf⟩ := r
    dsimp only
    refine (monoD_readEs _).bind fun _ ↦ (MonoD.pure _).bind fun _ ↦ (monoD_grindPreR _).bind fun _ ↦
      (monoD_powCheckR _).bind
      fun _ ↦ (monoD_positionsR _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
      (monoD_openingR _).bind fun _ ↦ MonoD.read.bind fun _ ↦ (monoD_rpW _ _).bind fun _ ↦ ?_
    split
    · exact (MonoD.require _).bind fun _ ↦ (monoD_tailRounds _ _).bind fun _ ↦ MonoD.require _
    · exact (monoD_tailRounds _ _).bind fun _ ↦ MonoD.require _
  | L :: N :: Ls, s => by
    rw [Lvm.whirLevels]
    refine (monoD_foldRounds _ _ _).bind fun r ↦ ?_
    obtain ⟨s', lf⟩ := r
    dsimp only
    exact (monoD_skip _).bind fun _ ↦ (MonoD.pure _).bind fun _ ↦ (monoD_oodStep _ _).bind fun _ ↦
      (monoD_grindPreR _).bind fun _ ↦
      (monoD_powCheckR _).bind fun _ ↦ (monoD_positionsR _).bind fun _ ↦
      monoD_sampleE.bind fun _ ↦ (monoD_openingR _).bind fun _ ↦ MonoD.read.bind fun _ ↦
      (monoD_rpW _ _).bind fun _ ↦ monoD_whirLevels logN laneFolds eb direct g ood (N :: Ls) _

theorem monoD_verifyWhir (levels : List Level) (logN : ℕ) (target : FE) (eb : List FE → FE)
    (direct : Bool) (g : ℕ) (ood : Bool) : MonoD (Lvm.verifyWhir levels logN target eb direct g ood) :=
  (monoD_rpW _ _).bind fun _ ↦ monoD_whirLevels _ _ _ _ _ _ _ _

theorem monoD_verifyStacked (levels : List Level) (stackLog : ℕ) (claims : List Lvm.StackClaim)
    (direct : Bool) (g : ℕ) (ood : Bool) :
    MonoD (Lvm.verifyStackedOpening levels stackLog claims direct g ood) :=
  monoD_sampleE.bind fun _ ↦ monoD_verifyWhir _ _ _ _ _ _ _

/-- **Phases 8–9 never clear a failed check.** -/
theorem monoD_dOpen (p : Params) (claims : List (Com × Lvm.BlockClaim)) : MonoD (dOpen p claims) :=
  (monoD_verifyStacked _ _ _ _ _ _).bind fun _ ↦ monoD_verifyStacked _ _ _ _ _ _

/-! ## Refinement steps -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- A native step that never ends `ok`. -/
theorem RefAt.require_false_bind {α β : Type} {k : Unit → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} (hk : ∀ u, MonoD (k u)) : RefAt cap shp sig (DM.require false >>= k) P R := by
  intro s hok
  have hsplit : runD (DM.require false >>= k) sig s =
      runD (k ()) sig { s with ok := false && s.ok } := rfl
  rw [hsplit] at hok
  exact absurd (hk () sig _ hok) (by simp)

/-- A native check that fails. -/
theorem RefAt.require_false {α : Type} {P : VerifierProgram α} {R : Unit → α → Prop} :
    RefAt cap shp sig (DM.require false) P R := by
  intro s hok
  have h : (runD (DM.require false) sig s).2.ok = (false && s.ok) := rfl
  rw [h] at hok
  exact absurd hok (by simp)

/-- A fact on the native value, added to the relation. -/
theorem RefAt.and_val {α β : Type} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    {Q : β → Prop} (h : RefAt cap shp sig d P R) (hq : ∀ s, Q (runD d sig s).1) :
    RefAt cap shp sig d P fun b a ↦ R b a ∧ Q b := fun s hok ↦ by
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, hq s⟩

/-- The round polynomial of a plain round (local copy of H1's `ref_sumcheckRoundPoly` at `none`). -/
private theorem ref_rpW {claim : FE} {claim' : E} (h : claim' = FE.toExt3 claim) :
    RefAt cap shp sig (Lvm.sumcheckRoundPoly 3 claim none) (Verifier.sumcheckRoundPoly 3 claim' none)
      (fun xs ys ↦ ys = xs.map FE.toExt3) := by
  subst h
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ MonoD.pure _) ref_readE ?_
  rintro x _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro xs _ rfl
  exact RefAt.pure (by simp [toExt3_sumE])

theorem positionsAux_length (h : ℕ) : ∀ (n rem : ℕ) (s : RS),
    (runD (DM.positionsAux h n rem) sig s).1.length = min rem (positionsPerAnswer * n)
  | 0, rem, s => by simp [runD, DM.positionsAux]; rfl
  | n + 1, rem, s => by
    show ((List.range (min positionsPerAnswer rem)).map
        (fun j ↦ (Lvm.eToNat (feAt sig (s.ent + 40 + s.msg)) >>> (j * h)) % 2 ^ h) ++
      (runD (DM.positionsAux h n (rem - min positionsPerAnswer rem)) sig
        { s with ent := s.ent + 72 + s.msg, msg := 0 }).1).length = _
    rw [List.length_append, List.length_map, List.length_range, positionsAux_length]
    simp only [positionsPerAnswer]
    omega

theorem positionsR_length (L : Level) (s : RS) : (runD (DM.positionsR L) sig s).1.length = L.t := by
  rw [DM.positionsR, positionsAux_length]
  simp only [positionsPerAnswer]
  omega

/-- **The positions** of a level, with their count. -/
theorem ref_positionsW (L : Level) {h' t' : ℕ} (hh : h' = L.height) (ht : t' = L.t) :
    RefAt cap shp sig (DM.positionsR L) (Verifier.samplePositions positionsPerAnswer h' t')
      (fun ps ps' ↦ ps' = ps ∧ ps.length = L.t) := by
  subst hh ht
  exact (ref_positionsR L).and_val (positionsR_length L)

/-- **Before the proof of work** (PI-GRIND): the separator and the nonce (nothing at `g = 0`). -/
theorem ref_grindPreR (g : ℕ) :
    RefAt cap shp sig (DM.grindPreR g) (Verifier.grindPre g) fun _ _ ↦ True := by
  unfold DM.grindPreR Verifier.grindPre
  by_cases hg : g = 0
  · simp only [hg, ↓reduceIte]
    exact RefAt.pure trivial
  · simp only [hg, ↓reduceIte]
    refine RefAt.bind (fun _ ↦ monoD_readE.bind fun _ ↦ MonoD.pure _) ref_sampleE fun _ _ _ ↦ ?_
    exact RefAt.bind (fun _ ↦ MonoD.pure _) ref_readE fun _ _ _ ↦ RefAt.pure trivial

/-- **The proof of work** (PI-GRIND): the PoW challenge, the same top-`g`-bits check (`powOKR`
against `powOK`, through `eToNat_toExt3`). -/
theorem ref_powCheckR (g : ℕ) :
    RefAt cap shp sig (DM.powCheckR g) (Verifier.powCheck g) fun _ _ ↦ True := by
  unfold DM.powCheckR Verifier.powCheck
  by_cases hg : g = 0
  · simp only [hg, ↓reduceIte]
    exact RefAt.pure trivial
  · simp only [hg, ↓reduceIte]
    refine RefAt.bind (fun _ ↦ MonoD.require _) ref_sampleE fun c _ hc ↦ ?_
    subst hc
    exact RefAt.require fun h ↦ by
      simpa only [DM.powOKR, Verifier.powOK, eToNat_toExt3, decide_eq_true_eq] using h

/-- **The fold rounds** of a level. -/
theorem ref_foldRounds : ∀ (n : ℕ) (s : Lvm.WhirState) (t : WhirStateT) (lf : List FE) (lf' : List E),
    WRel s t → lf' = lf.map FE.toExt3 →
    RefAt cap shp sig (Lvm.foldRounds n s lf) (foldRoundsT n t lf')
      (fun r r' ↦ WRel r.1 r'.1 ∧ r'.2 = r.2.map FE.toExt3 ∧ r.1.folds.length = s.folds.length + n ∧
        r.2.length = lf.length + n)
  | 0, _, _, _, _, hW, hl => RefAt.pure ⟨hW, hl, rfl, rfl⟩
  | n + 1, s, t, lf, lf', hW, hl => by
    refine RefAt.bind (fun _ ↦ (monoD_rpW _ _).bind fun _ ↦ monoD_foldRounds _ _ _) ref_sampleE ?_
    rintro c _ rfl
    refine RefAt.bind (fun _ ↦ monoD_foldRounds _ _ _)
      (ref_rpW (by rw [toExt3_polyEval, hW.quad])) ?_
    rintro q _ rfl
    refine (ref_foldRounds n { s with runningQuad := q, folds := s.folds ++ [c] }
      { t with target := Verifier.polyEval t.quad (FE.toExt3 c), quad := q.map FE.toExt3,
                folds := t.folds ++ [FE.toExt3 c] } (lf ++ [c]) (lf' ++ [FE.toExt3 c])
      ⟨rfl, ?_, hW.glued⟩ (by simp [hl])).mono ?_
    · simp [hW.folds]
    · rintro r r' ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, by simp only [List.length_append, List.length_singleton] at h3; omega,
        by simp only [List.length_append, List.length_singleton] at h4; omega⟩

/-- **The tail rounds** (V_S's `tailRounds 0` never ends `ok`). -/
theorem ref_tailRounds : ∀ (n : ℕ) (quad : List FE) (tgt : E) (quad' : List E),
    quad' = quad.map FE.toExt3 →
    RefAt cap shp sig (Lvm.tailRounds n quad) (tailRoundsT n tgt quad')
      (fun r r' ↦ r' = (r.1.map FE.toExt3, FE.toExt3 r.2))
  | 0, _, _, _, _ => RefAt.require_false_bind fun _ ↦ MonoD.pure _
  | 1, quad, tgt, quad', hq => by
    refine RefAt.bind (fun _ ↦ MonoD.pure _) ref_sampleE ?_
    rintro c _ rfl
    exact RefAt.pure (by simp [toExt3_polyEval, hq])
  | n + 2, quad, tgt, quad', hq => by
    refine RefAt.bind (fun _ ↦ (monoD_rpW _ _).bind fun _ ↦ (monoD_tailRounds _ _).bind fun _ ↦
      MonoD.pure _) ref_sampleE ?_
    rintro c _ rfl
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    refine RefAt.bind (fun _ ↦ (monoD_tailRounds _ _).bind fun _ ↦ MonoD.pure _)
      (ref_rpW (by rw [toExt3_polyEval, hq])) ?_
    rintro q _ rfl
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_tailRounds (n + 1) q _ _ rfl) ?_
    rintro ⟨r, x⟩ _ rfl
    exact RefAt.pure rfl

/-- **The enforced sum** of a level: the DSL's rows (`row.reverse.map ofK` at level 0, `extRow`
later) against V_S's folds read in place. -/
theorem toExt3_enforced (L : Level) (j : ℕ) (hlev : L.level = 0 ↔ j = 0) (lf : List FE)
    (hlf : lf.length = L.fold) (offs : List ℕ) (ws : List FE) (ws' : List E) (hws : ws' = ws.map FE.toExt3) :
    Verifier.enforcedSum (if j = 0 then (offs.map fun o ↦ rowAt sig o (wdOf j L.fold)).map
        (fun row ↦ row.reverse.map ofK) else (offs.map fun o ↦ rowAt sig o (wdOf j L.fold)).map Verifier.extRow)
      (lf.map FE.toExt3) ws' =
    FE.toExt3 (Lvm.dot ws (offs.map fun o ↦ if L.level = 0 then foldRow0 sig (eqKernelA lf) o (2 ^ L.fold)
      else foldRowE sig (eqKernelA lf) o (2 ^ L.fold))) := by
  subst hws
  by_cases hj : j = 0
  · have hl : L.level = 0 := hlev.2 hj
    simp only [hj, hl, ↓reduceIte, wdOf, List.map_map]
    rw [toExt3_dot_rows ws offs _ (fun o ↦ (rowAt sig o (2 ^ L.fold)).reverse.map ofK) (lf.map FE.toExt3)
      (fun o ↦ toExt3_foldRow0 sig lf o _ (by rw [hlf]))]
    rfl
  · have hl : ¬ L.level = 0 := fun h ↦ hj (hlev.1 h)
    simp only [hj, hl, ↓reduceIte, wdOf, List.map_map]
    rw [toExt3_dot_rows ws offs _ (fun o ↦ Verifier.extRow (rowAt sig o (3 * 2 ^ L.fold))) (lf.map FE.toExt3)
      (fun o ↦ toExt3_foldRowE sig lf o _ (by rw [hlf]))]
    rfl

/-- **The final level** (no next commitment): residual, proof of work, positions, `λ`, openings, intro
polynomial, glue, tail rounds, terminal check. -/
theorem ref_levelFinal (logN laneFolds c₀ n₀ g : ℕ) (ood : Bool) (eb : List FE → FE) (eb' : List E → E)
    (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs)) (L : Level) (W : Whir.Level) (j F : ℕ)
    (s : Lvm.WhirState) (t : WhirStateT) (hL : LevelOK cap shp logN c₀ n₀ j F L W) (hW : WRel s t)
    (hF : s.folds.length = F) :
    RefAt cap shp sig (Lvm.whirLevels logN laneFolds eb false g ood [L] s)
      (whirLevelsUd logN laneFolds positionsPerAnswer c₀ n₀ g false eb' j [W] t) (fun _ _ ↦ True) := by
  rw [Lvm.whirLevels, whirLevelsUd, ← hL.fold, ← hL.t]
  refine RefAt.bind ?_ (ref_foldRounds L.fold s t [] [] hW rfl) ?_
  rotate_left
  rintro ⟨s1, lf⟩ ⟨t1, lf'⟩ ⟨hW1, rfl, hF1, hlf⟩
  dsimp only at hW1 hF1 hlf ⊢
  simp only [List.length_nil, Nat.zero_add] at hlf
  have hm : t1.folds.length = F + L.fold := by rw [hW1.folds, List.length_map, hF1, hF]
  rw [hm, hF1, hF]
  refine RefAt.bind ?_ (ref_readEs _) ?_
  rotate_left
  rintro res _ rfl
  refine RefAt.dm_left (b₀ := ([] : List (List FE × (List FE → FE)))) (fun _ ↦ rfl) ?_
  refine RefAt.bind ?_ (ref_grindPreR g) ?_
  rotate_left
  rintro _ _ -
  refine RefAt.bind ?_ (ref_powCheckR g) ?_
  rotate_left
  rintro _ _ -
  refine RefAt.bind ?_ (ref_positionsW L hL.height.symm rfl) ?_
  rotate_left
  rintro qs0 qs ⟨rfl, hqs⟩
  refine RefAt.bind ?_ ref_sampleE ?_
  rotate_left
  rintro lam _ rfl
  refine RefAt.bind ?_ (ref_openingR L hL.shp hL.row hL.path hqs) ?_
  rotate_left
  rintro offs _ rfl
  refine RefAt.read_left ?_
  refine RefAt.bind ?_ (ref_rpW (toExt3_enforced L j hL.level lf hlf offs _ _ (map_powers _ _).symm)) ?_
  rotate_left
  rintro intro _ rfl
  have hW2 : ∀ v, WRel (Lvm.glue lam s1 [(intro, fun x ↦
        Lvm.inducedWeight (logN - (F + L.fold)) qs (powers lam qs.length) x)])
      (glueT (FE.toExt3 lam) t1 [(v, intro.map FE.toExt3, fun x ↦
        Verifier.inducedWeight (logN - (F + L.fold)) qs (Verifier.powers (FE.toExt3 lam) qs.length) x)]) :=
    fun v ↦ wrel_glue hW1 rfl rfl (fun xs ↦ by rw [toExt3_inducedWeight, map_powers]) v
  rw [ite_cond_eq_false _ _ (by decide : (false = true) = False),
    ite_cond_eq_false _ _ (by decide : (false = true) = False),
    VerifierProgram.pure_eq, VerifierProgram.ret_bind]
  refine RefAt.bind ?_ (ref_tailRounds _ _ _ _ (hW2 _).quad) ?_
  rotate_left
  rintro ⟨tf, tg⟩ _ rfl
  exact RefAt.require fun h ↦
    (toExt3_terminal (hW2 _) eb eb' heb laneFolds tf res).trans (congrArg FE.toExt3 (FE_eq_of_beq h))
  all_goals repeat' (first
    | (with_reducible exact MonoD.pure _) | (with_reducible exact MonoD.require _)
    | (with_reducible exact MonoD.read) | (with_reducible exact monoD_readE)
    | (with_reducible exact monoD_sampleE) | (with_reducible exact monoD_skip _)
    | (with_reducible exact monoD_readEs _) | (with_reducible exact monoD_positionsR _)
    | (with_reducible exact monoD_openingR _) | (with_reducible exact monoD_rpW _ _)
    | (with_reducible exact monoD_foldRounds _ _ _) | (with_reducible exact monoD_tailRounds _ _)
    | (with_reducible exact monoD_whirLevels _ _ _ _ _ _ _ _) | (with_reducible exact monoD_oodStep _ _) | (with_reducible exact monoD_samples _)
    | (with_reducible exact monoD_grindPreR _) | (with_reducible exact monoD_powCheckR _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

/-- **The level loop**, generic: levels in correspondence, `direct = false`. -/
theorem ref_whirLevels (logN laneFolds c₀ n₀ g : ℕ) (eb : List FE → FE) (eb' : List E → E)
    (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs)) :
    ∀ (Ls : List Level) (Ws : List Whir.Level) (j F : ℕ) (s : Lvm.WhirState) (t : WhirStateT),
      LevelsCorr cap shp logN c₀ n₀ j F Ls Ws → WRel s t → s.folds.length = F →
      RefAt cap shp sig (Lvm.whirLevels logN laneFolds eb false g false Ls s)
        (whirLevelsUd logN laneFolds positionsPerAnswer c₀ n₀ g false eb' j Ws t) (fun _ _ ↦ True)
  | [], _, _, _, _, _, _, _, _ => by rw [Lvm.whirLevels]; exact RefAt.require_false
  | _ :: _, [], _, _, _, _, hc, _, _ => False.elim hc
  | [L], [W], j, F, s, t, hc, hW, hF =>
    ref_levelFinal logN laneFolds c₀ n₀ g false eb eb' heb L W j F s t hc.1 hW hF
  | [_], _ :: _ :: _, _, _, _, _, hc, _, _ => False.elim hc.2.2
  | _ :: _ :: _, [_], _, _, _, _, hc, _, _ => False.elim hc.2.2
  | L :: N :: Ls, W :: W' :: Ws, j, F, s, t, hc, hW, hF => by
    obtain ⟨hL, hN, hc'⟩ := hc
    have ih := ref_whirLevels logN laneFolds c₀ n₀ g eb eb' heb (N :: Ls) (W' :: Ws) (j + 1) (F + L.fold)
    rw [Lvm.whirLevels, whirLevelsUd, ← hL.fold, ← hL.t]
    refine RefAt.bind ?_ (ref_foldRounds L.fold s t [] [] hW rfl) ?_
    rotate_left
    rintro ⟨s1, lf⟩ ⟨t1, lf'⟩ ⟨hW1, rfl, hF1, hlf⟩
    dsimp only at hW1 hF1 hlf ⊢
    simp only [List.length_nil, Nat.zero_add] at hlf
    have hm : t1.folds.length = F + L.fold := by rw [hW1.folds, List.length_map, hF1, hF]
    rw [hm, hF1, hF]
    refine RefAt.bind ?_ (ref_skip hN) ?_
    rotate_left
    rintro _ _ -
    refine RefAt.dm_left (b₀ := ([] : List FE)) (fun _ ↦ rfl) ?_
    rw [VerifierProgram.pure_eq, VerifierProgram.bind_eq, VerifierProgram.ret_bind]
    refine RefAt.dm_left (b₀ := ([] : List (List FE × (List FE → FE)))) (fun _ ↦ rfl) ?_
    refine RefAt.bind ?_ (ref_grindPreR g) ?_
    rotate_left
    rintro _ _ -
    refine RefAt.bind ?_ (ref_powCheckR g) ?_
    rotate_left
    rintro _ _ -
    refine RefAt.bind ?_ (ref_positionsW L hL.height.symm rfl) ?_
    rotate_left
    rintro qs0 qs ⟨rfl, hqs⟩
    refine RefAt.bind ?_ ref_sampleE ?_
    rotate_left
    rintro lam _ rfl
    refine RefAt.bind ?_ (ref_openingR L hL.shp hL.row hL.path hqs) ?_
    rotate_left
    rintro offs _ rfl
    refine RefAt.read_left ?_
    refine RefAt.bind ?_ (ref_rpW (toExt3_enforced L j hL.level lf hlf offs _ _ (map_powers _ _).symm)) ?_
    rotate_left
    rintro intro _ rfl
    exact ih _ _ hc' (wrel_glue hW1 rfl rfl (fun xs ↦ by rw [toExt3_inducedWeight, map_powers]) _)
      (hF1.trans (congrArg (· + L.fold) hF))
    all_goals repeat' (first
      | (with_reducible exact MonoD.pure _) | (with_reducible exact MonoD.require _)
      | (with_reducible exact MonoD.read) | (with_reducible exact monoD_readE)
      | (with_reducible exact monoD_sampleE) | (with_reducible exact monoD_skip _)
      | (with_reducible exact monoD_readEs _) | (with_reducible exact monoD_positionsR _)
      | (with_reducible exact monoD_openingR _) | (with_reducible exact monoD_rpW _ _)
      | (with_reducible exact monoD_foldRounds _ _ _) | (with_reducible exact monoD_tailRounds _ _)
      | (with_reducible exact monoD_whirLevels _ _ _ _ _ _ _ _) | (with_reducible exact monoD_oodStep _ _) | (with_reducible exact monoD_samples _)
      | (with_reducible exact monoD_grindPreR _) | (with_reducible exact monoD_powCheckR _)
      | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

theorem ref_whirLevels' (logN laneFolds laneFolds' c₀ n₀ g : ℕ) (hlane : laneFolds' = laneFolds)
    (eb : List FE → FE) (eb' : List E → E) (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs))
    (Ls : List Level) (Ws : List Whir.Level) (s : Lvm.WhirState) (t : WhirStateT)
    (hc : LevelsCorr cap shp logN c₀ n₀ 0 0 Ls Ws) (hW : WRel s t) (hF : s.folds.length = 0) :
    RefAt cap shp sig (Lvm.whirLevels logN laneFolds eb false g false Ls s)
      (whirLevelsUd logN laneFolds' positionsPerAnswer c₀ n₀ g false eb' 0 Ws t) (fun _ _ ↦ True) := by
  subst hlane
  exact ref_whirLevels logN laneFolds' c₀ n₀ g eb eb' heb Ls Ws 0 0 s t hc hW hF

/-- **One WHIR opening** (`verify_whir`): the levels in correspondence from level 0. -/
theorem ref_verifyWhir (levels : List Level) (cfg : UdConfig) (logN g : ℕ) (target : FE) (target' : E)
    (eb : List FE → FE) (eb' : List E → E) (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs))
    (ht : target' = FE.toExt3 target) (hμ : cfg.μ = logN) (hper : cfg.per = positionsPerAnswer)
    (hdir : cfg.direct = false) (hg : cfg.grind = g)
    (hc : LevelsCorr cap shp logN cfg.c₀ cfg.n₀ 0 0 levels cfg.levels) :
    RefAt cap shp sig (Lvm.verifyWhir levels logN target eb false g false) (verifyWhirUd cfg target' eb')
      (fun _ _ ↦ True) := by
  obtain ⟨μ, Ws, per, c₀, n₀, direct, grind⟩ := cfg
  dsimp only at hμ hper hdir hg hc
  subst hμ hper hdir hg
  have hlf : (Ws.head?.map (·.fold)).getD 0 = (levels.head?.map (·.fold)).getD 0 := by
    cases levels <;> cases Ws
    · rfl
    · exact False.elim hc
    · exact False.elim hc
    · simp [hc.1.fold]
  refine RefAt.bind (fun _ ↦ monoD_whirLevels _ _ _ _ _ _ _ _) (ref_rpW ht) ?_
  rintro q _ rfl
  exact ref_whirLevels' _ _ _ _ _ _ hlf eb eb' heb levels Ws _ _ hc ⟨rfl, rfl, List.Forall₂.nil⟩ rfl

theorem map_eq_of_forall₂W {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ} {l : List α}
    {l' : List β} (h : List.Forall₂ R l l') (hfg : ∀ a b, R a b → g b = f a) : l'.map g = l.map f := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, hfg _ _ hab, ih]

/-- **A stacked opening** (`verify_stacked_opening`): the claims batched with powers of one
challenge, then one WHIR opening. -/
theorem ref_verifyStacked (levels : List Level) (cfg : UdConfig) (stackLog g : ℕ)
    (claims : List Lvm.StackClaim) (cl : List VStackClaim) (h : List.Forall₂ SCRel claims cl)
    (hμ : cfg.μ = stackLog) (hper : cfg.per = positionsPerAnswer) (hdir : cfg.direct = false)
    (hg : cfg.grind = g) (hc : LevelsCorr cap shp stackLog cfg.c₀ cfg.n₀ 0 0 levels cfg.levels) :
    RefAt cap shp sig (Lvm.verifyStackedOpening levels stackLog claims false g false)
      (verifyStackedUd cfg cl) (fun _ _ ↦ True) := by
  refine RefAt.bind (fun _ ↦ monoD_verifyWhir _ _ _ _ _ _ _) ref_sampleE ?_
  rintro c _ rfl
  have hlen : cl.length = claims.length := h.length_eq.symm
  rw [hlen]
  refine ref_verifyWhir levels cfg stackLog g _ _ _ _ (fun xs ↦ ?_) ?_ hμ hper hdir hg hc
  · rw [toExt3_dot, map_powers, List.map_map]
    congr 1
    exact map_eq_of_forall₂W h fun a b hab ↦ hab.2 xs
  · rw [toExt3_dot, map_powers, List.map_map]
    congr 1
    exact map_eq_of_forall₂W h fun a b hab ↦ hab.1

/-! ## The levels with out-of-domain samples (lvm2 JB-VQP, J1: `C_main`) -/

/-- Re-association of a native bind (definitional). -/
theorem RefAt.assoc {α β γ δ : Type} {d : DM γ} {f : γ → DM δ} {k : δ → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} (h : RefAt cap shp sig (d >>= fun x ↦ f x >>= k) P R) :
    RefAt cap shp sig ((d >>= f) >>= k) P R := h

/-- **The OOD step** (`oodStep true κ`) against `whirLevelsJ`'s: the `κ` samples of the point, the
answer and the intro polynomial, then the rest with the pending claim `(intro, eq(z, ·))`. -/
theorem ref_oodStep {α β : Type} (k : ℕ) {K : List (List FE × (List FE → FE)) → DM β}
    {P : List E → E → List E → VerifierProgram α} {R : β → α → Prop} (hK : ∀ oc, MonoD (K oc))
    (h : ∀ (z : List FE) (y : FE) (i : List FE), RefAt cap shp sig (K [(i, fun x ↦ Lvm.eqEval z x)])
      (P (z.map FE.toExt3) (FE.toExt3 y) (i.map FE.toExt3)) R) :
    RefAt cap shp sig (Lvm.oodStep true k >>= K)
      ((VerifierProgram.sampleChallenges k).bind fun z ↦ VerifierProgram.readScalar.bind fun y ↦
        (Verifier.sumcheckRoundPoly 3 y none).bind fun i ↦ P z y i) R := by
  rw [Lvm.oodStep, if_pos rfl]
  refine RefAt.assoc ?_
  refine RefAt.bind (fun _ ↦ (monoD_readE.bind fun _ ↦ (monoD_rpW _ _).bind fun _ ↦ MonoD.pure _).bind hK)
    (ref_samples k) ?_
  rintro z _ rfl
  refine RefAt.assoc ?_
  refine RefAt.bind (fun _ ↦ ((monoD_rpW _ _).bind fun _ ↦ MonoD.pure _).bind hK) ref_readE ?_
  rintro y _ rfl
  refine RefAt.assoc ?_
  refine RefAt.bind (fun _ ↦ (MonoD.pure _).bind hK) (ref_rpW rfl) ?_
  rintro i _ rfl
  exact RefAt.dm_left (fun _ ↦ rfl) (h z y i)

/-- **`glue` vs `glueT`** on two pending claims (the OOD claim at `λ¹`, the queries at `λ²`). -/
theorem wrel_glue2 {s : Lvm.WhirState} {t : Verifier.WhirStateT} (h : WRel s t) {lam : FE} {lam' : E}
    (hl : lam' = FE.toExt3 lam) {i1 i2 : List FE} {i1' i2' : List E} (hi1 : i1' = i1.map FE.toExt3)
    (hi2 : i2' = i2.map FE.toExt3) {w1 w2 : List FE → FE} {w1' w2' : List E → E}
    (hw1 : ∀ xs, w1' (xs.map FE.toExt3) = FE.toExt3 (w1 xs))
    (hw2 : ∀ xs, w2' (xs.map FE.toExt3) = FE.toExt3 (w2 xs)) (v1 v2 : E) :
    WRel (Lvm.glue lam s [(i1, w1), (i2, w2)]) (Verifier.glueT lam' t [(v1, i1', w1'), (v2, i2', w2')]) := by
  subst hl hi1 hi2
  refine ⟨?_, h.folds, ?_⟩
  · simp only [Lvm.glue, Verifier.glueT, List.foldl_cons, List.foldl_nil, h.quad]
    rw [map_zipWith_of (g' := fun a b ↦ a + 1 * FE.toExt3 lam * FE.toExt3 lam * b)
        (fun q i ↦ by rw [tE_add, tE_mul, tE_mul, tE_mul, tE_one]),
      map_zipWith_of (g' := fun a b ↦ a + 1 * FE.toExt3 lam * b)
        (fun q i ↦ by rw [tE_add, tE_mul, tE_mul, tE_one])]
  · simp only [Lvm.glue, Verifier.glueT, List.foldl_cons, List.foldl_nil]
    refine List.rel_append (List.rel_append h.glued
      (List.Forall₂.cons ⟨by rw [tE_mul, tE_one], ?_, hw1⟩ List.Forall₂.nil))
      (List.Forall₂.cons ⟨by rw [tE_mul, tE_mul, tE_one], ?_, hw2⟩ List.Forall₂.nil)
    · simp [h.folds]
    · simp [h.folds]

/-- **The level loop with OOD samples** (`ood = true`) against `whirLevelsJ`: levels in
correspondence, `direct = false`. The final level is `ref_levelFinal` (`whirLevelsJ_one`). -/
theorem ref_whirLevelsJ (logN laneFolds c₀ n₀ g : ℕ) (eb : List FE → FE) (eb' : List E → E)
    (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs)) :
    ∀ (Ls : List Level) (Ws : List Whir.Level) (j F : ℕ) (s : Lvm.WhirState) (t : WhirStateT),
      LevelsCorr cap shp logN c₀ n₀ j F Ls Ws → WRel s t → s.folds.length = F →
      RefAt cap shp sig (Lvm.whirLevels logN laneFolds eb false g true Ls s)
        (whirLevelsJ logN laneFolds positionsPerAnswer c₀ n₀ g false eb' j Ws t) (fun _ _ ↦ True)
  | [], _, _, _, _, _, _, _, _ => by rw [Lvm.whirLevels]; exact RefAt.require_false
  | _ :: _, [], _, _, _, _, hc, _, _ => False.elim hc
  | [L], [W], j, F, s, t, hc, hW, hF => by
    rw [LeanVM.Protocol.Verifier.whirLevelsJ_one]
    exact ref_levelFinal logN laneFolds c₀ n₀ g true eb eb' heb L W j F s t hc.1 hW hF
  | [_], _ :: _ :: _, _, _, _, _, hc, _, _ => False.elim hc.2.2
  | _ :: _ :: _, [_], _, _, _, _, hc, _, _ => False.elim hc.2.2
  | L :: N :: Ls, W :: W' :: Ws, j, F, s, t, hc, hW, hF => by
    obtain ⟨hL, hN, hc'⟩ := hc
    have ih := ref_whirLevelsJ logN laneFolds c₀ n₀ g eb eb' heb (N :: Ls) (W' :: Ws) (j + 1) (F + L.fold)
    rw [Lvm.whirLevels, whirLevelsJ, ← hL.fold, ← hL.t]
    refine RefAt.bind ?_ (ref_foldRounds L.fold s t [] [] hW rfl) ?_
    rotate_left
    rintro ⟨s1, lf⟩ ⟨t1, lf'⟩ ⟨hW1, rfl, hF1, hlf⟩
    dsimp only at hW1 hF1 hlf ⊢
    simp only [List.length_nil, Nat.zero_add] at hlf
    have hm : t1.folds.length = F + L.fold := by rw [hW1.folds, List.length_map, hF1, hF]
    rw [hm, hF1, hF]
    refine RefAt.bind ?_ (ref_skip hN) ?_
    rotate_left
    rintro _ _ -
    refine RefAt.dm_left (b₀ := ([] : List FE)) (fun _ ↦ rfl) ?_
    refine ref_oodStep _ ?_ fun z y oi ↦ ?_
    rotate_left
    refine RefAt.bind ?_ (ref_grindPreR g) ?_
    rotate_left
    rintro _ _ -
    refine RefAt.bind ?_ (ref_powCheckR g) ?_
    rotate_left
    rintro _ _ -
    refine RefAt.bind ?_ (ref_positionsW L hL.height.symm rfl) ?_
    rotate_left
    rintro qs0 qs ⟨rfl, hqs⟩
    refine RefAt.bind ?_ ref_sampleE ?_
    rotate_left
    rintro lam _ rfl
    refine RefAt.bind ?_ (ref_openingR L hL.shp hL.row hL.path hqs) ?_
    rotate_left
    rintro offs _ rfl
    refine RefAt.read_left ?_
    refine RefAt.bind ?_ (ref_rpW (toExt3_enforced L j hL.level lf hlf offs _ _ (map_powers _ _).symm)) ?_
    rotate_left
    rintro intro _ rfl
    exact ih _ _ hc' (wrel_glue2 hW1 rfl rfl rfl (fun xs ↦ (toExt3_eqEval z xs).symm)
      (fun xs ↦ by rw [toExt3_inducedWeight, map_powers]) _ _) (hF1.trans (congrArg (· + L.fold) hF))
    all_goals repeat' (first
      | (with_reducible exact MonoD.pure _) | (with_reducible exact MonoD.require _)
      | (with_reducible exact MonoD.read) | (with_reducible exact monoD_readE)
      | (with_reducible exact monoD_sampleE) | (with_reducible exact monoD_skip _)
      | (with_reducible exact monoD_readEs _) | (with_reducible exact monoD_positionsR _)
      | (with_reducible exact monoD_openingR _) | (with_reducible exact monoD_rpW _ _)
      | (with_reducible exact monoD_foldRounds _ _ _) | (with_reducible exact monoD_tailRounds _ _)
      | (with_reducible exact monoD_whirLevels _ _ _ _ _ _ _ _) | (with_reducible exact monoD_oodStep _ _)
      | (with_reducible exact monoD_samples _)
      | (with_reducible exact monoD_grindPreR _) | (with_reducible exact monoD_powCheckR _)
      | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

/-- **One WHIR opening with OOD samples** (`verifyWhirJ`, `cfg.ood = true`). -/
theorem ref_verifyWhirJ (levels : List Level) (cfg : WhirConfig) (logN g : ℕ) (target : FE) (target' : E)
    (eb : List FE → FE) (eb' : List E → E) (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs))
    (ht : target' = FE.toExt3 target) (hood : cfg.ood = true) (hμ : cfg.μ = logN)
    (hper : cfg.per = positionsPerAnswer) (hdir : cfg.direct = false) (hg : cfg.grind = g)
    (hc : LevelsCorr cap shp logN cfg.c₀ cfg.n₀ 0 0 levels cfg.levels) :
    RefAt cap shp sig (Lvm.verifyWhir levels logN target eb false g true) (verifyWhirJ cfg target' eb')
      (fun _ _ ↦ True) := by
  obtain ⟨⟨μ, Ws, per, c₀, n₀, direct, grind⟩, ood⟩ := cfg
  dsimp only at hood hμ hper hdir hg hc
  subst hood hμ hper hdir hg
  have hlf : (Ws.head?.map (·.fold)).getD 0 = (levels.head?.map (·.fold)).getD 0 := by
    cases levels <;> cases Ws
    · rfl
    · exact False.elim hc
    · exact False.elim hc
    · simp [hc.1.fold]
  unfold verifyWhirJ
  rw [if_pos rfl]
  dsimp only
  rw [hlf]
  refine RefAt.bind (fun _ ↦ monoD_whirLevels _ _ _ _ _ _ _ _) (ref_rpW ht) ?_
  rintro q _ rfl
  exact ref_whirLevelsJ _ _ _ _ _ eb eb' heb levels Ws 0 0 _ _ hc ⟨rfl, rfl, List.Forall₂.nil⟩ rfl

/-- **A stacked opening with OOD samples** (`verifyStackedJ`, `cfg.ood = true`) against V_S's
`verifyStackedOpening … ood` with `ood = true`. -/
theorem ref_verifyStackedJ (levels : List Level) (cfg : WhirConfig) (stackLog g : ℕ) (ood : Bool)
    (claims : List Lvm.StackClaim) (cl : List VStackClaim) (h : List.Forall₂ SCRel claims cl)
    (hood' : ood = true) (hood : cfg.ood = true) (hμ : cfg.μ = stackLog)
    (hper : cfg.per = positionsPerAnswer) (hdir : cfg.direct = false) (hg : cfg.grind = g)
    (hc : LevelsCorr cap shp stackLog cfg.c₀ cfg.n₀ 0 0 levels cfg.levels) :
    RefAt cap shp sig (Lvm.verifyStackedOpening levels stackLog claims false g ood)
      (verifyStackedJ cfg cl) (fun _ _ ↦ True) := by
  subst hood'
  refine RefAt.bind (fun _ ↦ monoD_verifyWhir _ _ _ _ _ _ _) ref_sampleE ?_
  rintro c _ rfl
  have hlen : cl.length = claims.length := h.length_eq.symm
  rw [hlen]
  refine ref_verifyWhirJ levels cfg stackLog g _ _ _ _ (fun xs ↦ ?_) ?_ hood hμ hper hdir hg hc
  · rw [toExt3_dot, map_powers, List.map_map]
    congr 1
    exact map_eq_of_forall₂W h fun a b hab ↦ hab.2 xs
  · rw [toExt3_dot, map_powers, List.map_map]
    congr 1
    exact map_eq_of_forall₂W h fun a b hab ↦ hab.1

end Ref

/-! ## P20 -/

theorem recLevels_P20 : P20.recLevels = [⟨0, 6, 13, 2, 15, 7, 8, 170, 512⟩, ⟨1, 4, 9, 3, 12, 7, 5, 139, 384⟩] := by
  decide +kernel

/-- `C_main`'s levels at P20 (J1: `t = 230, 115, 77`). -/
theorem mainLevels_P20 : P20.mainLevels = [⟨0, 6, 18, 1, 19, 8, 11, 230, 512⟩,
    ⟨1, 4, 14, 2, 16, 7, 9, 115, 384⟩, ⟨2, 4, 10, 3, 13, 7, 6, 77, 384⟩] := by decide +kernel

/-- `C_rec`'s level against `cfgRec20G` (commitment 1, `(15, 64)`, cap 7). -/
theorem corrRec20 : LevelsCorr capS shpS 19 1 2 0 0 P20.recLevels cfgRec20G.levels := by
  rw [recLevels_P20]
  simp only [LevelsCorr, NextOK, cfgRec20G]
  decide

/-- `C_main`'s levels against `cfgMain24J 3` (lvm2 JB-VQP J1; commitments 0, 2, 3; caps 8, 7, 7). -/
theorem corrMain24 : LevelsCorr capS shpS 24 0 3 0 0 P20.mainLevels (cfgMain24J 3).levels := by
  rw [mainLevels_P20]
  simp only [LevelsCorr, NextOK, cfgMain24J]
  decide

/-- P20's `C_main` takes the OOD samples (J1). -/
theorem mainOod_P20 : P20.mainOod = true := by decide +kernel

/-- **Phases 8–9 at P20**: V_S's two stacked openings (`C_rec` in unique decoding, then `C_main`
with its OOD samples; `direct = false`) refine `verifyStackedUd cfgRec20G` then
`verifyStackedJ (cfgMain24J 3)` on claims related by `SCRel`. -/
theorem ref_dOpen {sig : ByteArray} (claims : List (Com × Lvm.BlockClaim))
    (cl : List VStackClaim × List VStackClaim)
    (h1 : List.Forall₂ SCRel ((claims.filter (·.1 == .crec)).map (·.2.onStack)) cl.1)
    (h2 : List.Forall₂ SCRel ((claims.filter (·.1 == .main)).map (·.2.onStack)) cl.2) :
    Ref20 sig (dOpen P20 claims)
      (LeanVM.Protocol.Verifier.verifyStackedUd cfgRec20G cl.1 >>= fun _ ↦
        verifyStackedJ (cfgMain24J 3) cl.2) (fun _ _ ↦ True) :=
  RefAt.bind (fun _ ↦ monoD_verifyStacked _ _ _ _ _ _)
    (ref_verifyStacked _ cfgRec20G _ _ _ _ h1 rfl rfl rfl rfl corrRec20)
    fun _ _ _ ↦ ref_verifyStackedJ _ (cfgMain24J 3) _ _ _ _ _ h2 mainOod_P20 rfl rfl rfl rfl rfl corrMain24

/-! ## P20G (PI-GRIND's test set: P20 with `g = 14`) -/

theorem recLevels_P20G : P20G.recLevels = [⟨0, 6, 13, 2, 15, 7, 8, 170, 512⟩, ⟨1, 4, 9, 3, 12, 7, 5, 139, 384⟩] := by
  decide +kernel

theorem mainLevels_P20G : P20G.mainLevels = [⟨0, 6, 18, 1, 19, 8, 11, 278, 512⟩,
    ⟨1, 4, 14, 2, 16, 7, 9, 170, 384⟩, ⟨2, 4, 10, 3, 13, 7, 6, 139, 384⟩] := by decide +kernel

/-- `C_rec`'s level against `cfgRec20G` (as `corrRec20`, `t = 170`). -/
theorem corrRec20G : LevelsCorr capS shpS 19 1 2 0 0 P20G.recLevels cfgRec20G.levels := by
  rw [recLevels_P20G]
  simp only [LevelsCorr, NextOK, cfgRec20G]
  decide

/-- `C_main`'s levels against `cfgMain24G` (as `corrMain24`, `t = 278, 170, 139`). -/
theorem corrMain24G : LevelsCorr capS shpS 24 0 3 0 0 P20G.mainLevels cfgMain24G.levels := by
  rw [mainLevels_P20G]
  simp only [LevelsCorr, NextOK, cfgMain24G]
  decide

/-- **Phases 8–9 at P20G** (`g = 14`): V_S's two stacked openings, each level with its proof of work,
refine `verifyStackedUd cfgRec20G` then `verifyStackedUd cfgMain24G`. -/
theorem ref_dOpenG {sig : ByteArray} (claims : List (Com × Lvm.BlockClaim))
    (cl : List VStackClaim × List VStackClaim)
    (h1 : List.Forall₂ SCRel ((claims.filter (·.1 == .crec)).map (·.2.onStack)) cl.1)
    (h2 : List.Forall₂ SCRel ((claims.filter (·.1 == .main)).map (·.2.onStack)) cl.2) :
    Ref20 sig (dOpen P20G claims)
      (LeanVM.Protocol.Verifier.verifyStackedUd cfgRec20G cl.1 >>= fun _ ↦
        LeanVM.Protocol.Verifier.verifyStackedUd cfgMain24G cl.2) (fun _ _ ↦ True) :=
  RefAt.bind (fun _ ↦ monoD_verifyStacked _ _ _ _ _ _)
    (ref_verifyStacked _ cfgRec20G _ _ _ _ h1 rfl rfl rfl rfl corrRec20G)
    fun _ _ _ ↦ ref_verifyStacked _ cfgMain24G _ _ _ _ h2 rfl rfl rfl rfl corrMain24G

end Lvm.VEq
