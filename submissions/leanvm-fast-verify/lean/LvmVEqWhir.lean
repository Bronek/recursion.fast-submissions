-- New for lvm (WP-14a, H4): V_S's stacked WHIR openings (phases 8–9: LvmDecideWhir `verifyStackedOpening`,
-- `direct = false`, A20) refine WP-7's `verifyStackedUd cfgRec20` / `cfgMain20` (LvmWhirProg, LvmWhirParams)
-- event for event; the level loop is generic in a level correspondence, instantiated at P20.
import LvmVEqWhirPure

/-!
# The stacked WHIR openings: V_S refines the verifier language

* `LevelOK`, `NextOK`, `LevelsCorr`: a native level (`Lvm.Level`: fold, height, `t`, row bytes, path,
  next cap) against a language level (`Whir.Level`: fold, rate, queries) and the commitment table
  `cap shp` at the commitment index `cidx c₀ n₀ j` it opens;
* `ref_foldRounds`, `ref_tailRounds`, `ref_whirLevels` (generic loop, `direct = false`),
  `ref_verifyWhir`, `ref_verifyStacked`; `monoD_*` (V_S's steps never clear a failed check);
* at P20: `corrRec20`, `corrMain20` (by `decide` on the literal levels), **`ref_dOpen`**, `monoD_dOpen`.

Event order (both sides): per level the fold rounds (challenge, round polynomial), the next cap
(`skip` vs `readCommitment`) or the residual, the positions, `λ`, the openings, the intro
polynomial; after the final level the tail rounds and the terminal check. V_S's `tailRounds 0`
(`require false`) and `whirLevels []` (`require false`) never end `ok`, so the DSL's `target`
(returned by `tailRoundsT 0`, not tracked by V_S) is never observed where V_S accepts.
The round-polynomial step (`ref_rpW`) is a local copy of H1's `ref_sumcheckRoundPoly` at `none`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (WhirStateT foldRoundsT tailRoundsT glueT whirLevelsUd verifyWhirUd
  verifyStackedUd UdConfig cidx)
open LeanVM.Protocol.Whir.Sound (cfgRec20 cfgMain20)
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

theorem monoD_whirLevels (logN laneFolds : ℕ) (eb : List FE → FE) (direct : Bool) :
    ∀ (Ls : List Level) (s : Lvm.WhirState), MonoD (Lvm.whirLevels logN laneFolds eb direct Ls s)
  | [], _ => MonoD.require _
  | [L], s => by
    rw [Lvm.whirLevels]
    refine (monoD_foldRounds _ _ _).bind fun r ↦ ?_
    obtain ⟨s', lf⟩ := r
    dsimp only
    refine (monoD_readEs _).bind fun _ ↦ (monoD_positionsR _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
      (monoD_openingR _).bind fun _ ↦ MonoD.read.bind fun _ ↦ (monoD_rpW _ _).bind fun _ ↦ ?_
    split
    · exact (MonoD.require _).bind fun _ ↦ (monoD_tailRounds _ _).bind fun _ ↦ MonoD.require _
    · exact (monoD_tailRounds _ _).bind fun _ ↦ MonoD.require _
  | L :: N :: Ls, s => by
    rw [Lvm.whirLevels]
    refine (monoD_foldRounds _ _ _).bind fun r ↦ ?_
    obtain ⟨s', lf⟩ := r
    dsimp only
    exact (monoD_skip _).bind fun _ ↦ (MonoD.pure _).bind fun _ ↦ (monoD_positionsR _).bind fun _ ↦
      monoD_sampleE.bind fun _ ↦ (monoD_openingR _).bind fun _ ↦ MonoD.read.bind fun _ ↦
      (monoD_rpW _ _).bind fun _ ↦ monoD_whirLevels logN laneFolds eb direct (N :: Ls) _

theorem monoD_verifyWhir (levels : List Level) (logN : ℕ) (target : FE) (eb : List FE → FE)
    (direct : Bool) : MonoD (Lvm.verifyWhir levels logN target eb direct) :=
  (monoD_rpW _ _).bind fun _ ↦ monoD_whirLevels _ _ _ _ _ _

theorem monoD_verifyStacked (levels : List Level) (stackLog : ℕ) (claims : List Lvm.StackClaim)
    (direct : Bool) : MonoD (Lvm.verifyStackedOpening levels stackLog claims direct) :=
  monoD_sampleE.bind fun _ ↦ monoD_verifyWhir _ _ _ _ _

/-- **Phases 8–9 never clear a failed check.** -/
theorem monoD_dOpen (p : Params) (claims : List (Com × Lvm.BlockClaim)) : MonoD (dOpen p claims) :=
  (monoD_verifyStacked _ _ _ _).bind fun _ ↦ monoD_verifyStacked _ _ _ _

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

/-- **The final level** (no next commitment): residual, positions, `λ`, openings, intro polynomial,
glue, tail rounds, terminal check. -/
theorem ref_levelFinal (logN laneFolds c₀ n₀ : ℕ) (eb : List FE → FE) (eb' : List E → E)
    (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs)) (L : Level) (W : Whir.Level) (j F : ℕ)
    (s : Lvm.WhirState) (t : WhirStateT) (hL : LevelOK cap shp logN c₀ n₀ j F L W) (hW : WRel s t)
    (hF : s.folds.length = F) :
    RefAt cap shp sig (Lvm.whirLevels logN laneFolds eb false [L] s)
      (whirLevelsUd logN laneFolds positionsPerAnswer c₀ n₀ false eb' j [W] t) (fun _ _ ↦ True) := by
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
    | (with_reducible exact monoD_whirLevels _ _ _ _ _ _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

/-- **The level loop**, generic: levels in correspondence, `direct = false`. -/
theorem ref_whirLevels (logN laneFolds c₀ n₀ : ℕ) (eb : List FE → FE) (eb' : List E → E)
    (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs)) :
    ∀ (Ls : List Level) (Ws : List Whir.Level) (j F : ℕ) (s : Lvm.WhirState) (t : WhirStateT),
      LevelsCorr cap shp logN c₀ n₀ j F Ls Ws → WRel s t → s.folds.length = F →
      RefAt cap shp sig (Lvm.whirLevels logN laneFolds eb false Ls s)
        (whirLevelsUd logN laneFolds positionsPerAnswer c₀ n₀ false eb' j Ws t) (fun _ _ ↦ True)
  | [], _, _, _, _, _, _, _, _ => by rw [Lvm.whirLevels]; exact RefAt.require_false
  | _ :: _, [], _, _, _, _, hc, _, _ => False.elim hc
  | [L], [W], j, F, s, t, hc, hW, hF => ref_levelFinal logN laneFolds c₀ n₀ eb eb' heb L W j F s t hc.1 hW hF
  | [_], _ :: _ :: _, _, _, _, _, hc, _, _ => False.elim hc.2.2
  | _ :: _ :: _, [_], _, _, _, _, hc, _, _ => False.elim hc.2.2
  | L :: N :: Ls, W :: W' :: Ws, j, F, s, t, hc, hW, hF => by
    obtain ⟨hL, hN, hc'⟩ := hc
    have ih := ref_whirLevels logN laneFolds c₀ n₀ eb eb' heb (N :: Ls) (W' :: Ws) (j + 1) (F + L.fold)
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
      | (with_reducible exact monoD_whirLevels _ _ _ _ _ _)
      | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

theorem ref_whirLevels' (logN laneFolds laneFolds' c₀ n₀ : ℕ) (hlane : laneFolds' = laneFolds)
    (eb : List FE → FE) (eb' : List E → E) (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs))
    (Ls : List Level) (Ws : List Whir.Level) (s : Lvm.WhirState) (t : WhirStateT)
    (hc : LevelsCorr cap shp logN c₀ n₀ 0 0 Ls Ws) (hW : WRel s t) (hF : s.folds.length = 0) :
    RefAt cap shp sig (Lvm.whirLevels logN laneFolds eb false Ls s)
      (whirLevelsUd logN laneFolds' positionsPerAnswer c₀ n₀ false eb' 0 Ws t) (fun _ _ ↦ True) := by
  subst hlane
  exact ref_whirLevels logN laneFolds' c₀ n₀ eb eb' heb Ls Ws 0 0 s t hc hW hF

/-- **One WHIR opening** (`verify_whir`): the levels in correspondence from level 0. -/
theorem ref_verifyWhir (levels : List Level) (cfg : UdConfig) (logN : ℕ) (target : FE) (target' : E)
    (eb : List FE → FE) (eb' : List E → E) (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs))
    (ht : target' = FE.toExt3 target) (hμ : cfg.μ = logN) (hper : cfg.per = positionsPerAnswer)
    (hdir : cfg.direct = false) (hc : LevelsCorr cap shp logN cfg.c₀ cfg.n₀ 0 0 levels cfg.levels) :
    RefAt cap shp sig (Lvm.verifyWhir levels logN target eb false) (verifyWhirUd cfg target' eb')
      (fun _ _ ↦ True) := by
  obtain ⟨μ, Ws, per, c₀, n₀, direct⟩ := cfg
  dsimp only at hμ hper hdir hc
  subst hμ hper hdir
  have hlf : (Ws.head?.map (·.fold)).getD 0 = (levels.head?.map (·.fold)).getD 0 := by
    cases levels <;> cases Ws
    · rfl
    · exact False.elim hc
    · exact False.elim hc
    · simp [hc.1.fold]
  refine RefAt.bind (fun _ ↦ monoD_whirLevels _ _ _ _ _ _) (ref_rpW ht) ?_
  rintro q _ rfl
  exact ref_whirLevels' _ _ _ _ _ hlf eb eb' heb levels Ws _ _ hc ⟨rfl, rfl, List.Forall₂.nil⟩ rfl

theorem map_eq_of_forall₂W {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ} {l : List α}
    {l' : List β} (h : List.Forall₂ R l l') (hfg : ∀ a b, R a b → g b = f a) : l'.map g = l.map f := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, hfg _ _ hab, ih]

/-- **A stacked opening** (`verify_stacked_opening`): the claims batched with powers of one
challenge, then one WHIR opening. -/
theorem ref_verifyStacked (levels : List Level) (cfg : UdConfig) (stackLog : ℕ)
    (claims : List Lvm.StackClaim) (cl : List VStackClaim) (h : List.Forall₂ SCRel claims cl)
    (hμ : cfg.μ = stackLog) (hper : cfg.per = positionsPerAnswer) (hdir : cfg.direct = false)
    (hc : LevelsCorr cap shp stackLog cfg.c₀ cfg.n₀ 0 0 levels cfg.levels) :
    RefAt cap shp sig (Lvm.verifyStackedOpening levels stackLog claims false) (verifyStackedUd cfg cl)
      (fun _ _ ↦ True) := by
  refine RefAt.bind (fun _ ↦ monoD_verifyWhir _ _ _ _ _) ref_sampleE ?_
  rintro c _ rfl
  have hlen : cl.length = claims.length := h.length_eq.symm
  rw [hlen]
  refine ref_verifyWhir levels cfg stackLog _ _ _ _ (fun xs ↦ ?_) ?_ hμ hper hdir hc
  · rw [toExt3_dot, map_powers, List.map_map]
    congr 1
    exact map_eq_of_forall₂W h fun a b hab ↦ hab.2 xs
  · rw [toExt3_dot, map_powers, List.map_map]
    congr 1
    exact map_eq_of_forall₂W h fun a b hab ↦ hab.1

end Ref

/-! ## P20 -/

theorem recLevels_P20 : P20.recLevels = [⟨0, 6, 13, 2, 15, 7, 8, 191, 512⟩] := by decide +kernel

theorem mainLevels_P20 : P20.mainLevels = [⟨0, 6, 20, 1, 21, 8, 13, 311, 512⟩,
    ⟨1, 4, 16, 2, 18, 7, 11, 191, 384⟩, ⟨2, 4, 12, 3, 15, 7, 8, 156, 384⟩,
    ⟨3, 4, 8, 4, 12, 7, 5, 142, 384⟩] := by decide +kernel

/-- `C_rec`'s level against `cfgRec20` (commitment 1, `(15, 64)`, cap 7). -/
theorem corrRec20 : LevelsCorr capS shpS 19 1 2 0 0 P20.recLevels cfgRec20.levels := by
  rw [recLevels_P20]
  simp only [LevelsCorr, NextOK, cfgRec20]
  decide

/-- `C_main`'s levels against `cfgMain20` (commitments 0, 2, 3, 4; caps 8, 7, 7, 7). -/
theorem corrMain20 : LevelsCorr capS shpS 26 0 2 0 0 P20.mainLevels cfgMain20.levels := by
  rw [mainLevels_P20]
  simp only [LevelsCorr, NextOK, cfgMain20]
  decide

/-- **Phases 8–9 at P20**: V_S's two stacked openings (`C_rec`, then `C_main`; `direct = false`)
refine `verifyStackedUd cfgRec20` then `verifyStackedUd cfgMain20` on claims related by `SCRel`. -/
theorem ref_dOpen {sig : ByteArray} (claims : List (Com × Lvm.BlockClaim))
    (cl : List VStackClaim × List VStackClaim)
    (h1 : List.Forall₂ SCRel ((claims.filter (·.1 == .crec)).map (·.2.onStack)) cl.1)
    (h2 : List.Forall₂ SCRel ((claims.filter (·.1 == .main)).map (·.2.onStack)) cl.2) :
    Ref20 sig (dOpen P20 claims)
      (LeanVM.Protocol.Verifier.verifyStackedUd cfgRec20 cl.1 >>= fun _ ↦
        LeanVM.Protocol.Verifier.verifyStackedUd cfgMain20 cl.2) (fun _ _ ↦ True) :=
  RefAt.bind (fun _ ↦ monoD_verifyStacked _ _ _ _)
    (ref_verifyStacked _ cfgRec20 _ _ _ h1 rfl rfl rfl corrRec20)
    fun _ _ _ ↦ ref_verifyStacked _ cfgMain20 _ _ _ h2 rfl rfl rfl corrMain20

end Lvm.VEq
