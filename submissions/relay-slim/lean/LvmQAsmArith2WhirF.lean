-- New for lvm (HAR-WH): `F`'s reads in phases 8–9 (the stacked WHIR openings) as pure functions of
-- the stream and the reader's position (`pos s = s.ent + s.msg`).
import LvmQAsmArith2WhirG

/-!
# Phases 8–9: run lemmas of `F`'s reader

Every read of the stacked opening depends only on the position `pos s` (and `openingR` on `ent`
with `msg = 0`): `sampleE_run`, `readE_run`, `readEs_run`, `srp3_run` (`sumcheckRoundPoly 3 _ none`),
`foldRounds_run` (`frQ`, `frC`), `positionsR_run` (`qsAt`, `qsAt_length`), `openingR_run`,
`tailRounds_run` (`frC`, `tlT`); the monad's `bind`, `read`, `require`, `skip`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

theorem dm_bind {α β : Type} (x : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (x >>= f) sig s = f (x sig s).1 sig (x sig s).2 := rfl

theorem dm_pure {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) := rfl

theorem read_run (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) := rfl

theorem require_runW (b : Bool) (sig : ByteArray) (s : RS) :
    require b sig s = ((), { s with ok := b && s.ok }) := rfl

theorem skip_run (n : Nat) (sig : ByteArray) (s : RS) : skip n sig s = ((), { s with msg := s.msg + n }) :=
  rfl

theorem pos_mk (a b : Nat) (o : Bool) : pos ⟨a, b, o⟩ = a + b := rfl

theorem sampleE_run (sig : ByteArray) (s : RS) :
    sampleE sig s = (feAt sig (pos s + 40), ⟨pos s + 72, 0, s.ok⟩) := by
  have h : sampleE sig s = (feAt sig (s.ent + 40 + s.msg), ⟨s.ent + 72 + s.msg, 0, s.ok⟩) := rfl
  rw [h]
  unfold pos
  rw [Nat.add_right_comm s.ent 40 s.msg, Nat.add_right_comm s.ent 72 s.msg]

theorem readE_run (sig : ByteArray) (s : RS) :
    readE sig s = (feAt sig (pos s + 40), { s with msg := s.msg + 24 }) := by
  have h : readE sig s = (feAt sig (s.ent + 40 + s.msg), { s with msg := s.msg + 24 }) := rfl
  rw [h]
  unfold pos
  rw [Nat.add_right_comm s.ent 40 s.msg]

theorem readEs_run (n : Nat) (sig : ByteArray) (s : RS) :
    readEs n sig s = ((List.range n).map (fun i => feAt sig (pos s + 40 + 24 * i)),
      { s with msg := s.msg + 24 * n }) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have e : readEs (n + 1) sig s =
        (feAt sig (pos s + 40) :: (readEs n sig { s with msg := s.msg + 24 }).1,
          (readEs n sig { s with msg := s.msg + 24 }).2) := by
      rw [readEs, dm_bind, readE_run]; rfl
    rw [e, ih]
    obtain ⟨en, m, o⟩ := s
    refine Prod.ext ?_ ?_
    · show feAt sig (en + m + 40) :: (List.range n).map (fun i => feAt sig (en + (m + 24) + 40 + 24 * i)) =
        (List.range (n + 1)).map (fun i => feAt sig (en + m + 40 + 24 * i))
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      show feAt sig _ = feAt sig _
      congr 1
      omega
    · show (⟨en, m + 24 + 24 * n, o⟩ : RS) = ⟨en, m + 24 * (n + 1), o⟩
      congr 1
      omega

theorem srp3_run (claim : FE) (sig : ByteArray) (s : RS) :
    sumcheckRoundPoly 3 claim none sig s =
      ([feAt sig (pos s + 40), claim + feAt sig (pos s + 64), feAt sig (pos s + 64)],
        { s with msg := s.msg + 48 }) := by
  have e : sumcheckRoundPoly 3 claim none sig s =
      (feAt sig (pos s + 40) :: (claim + sumE (readEs 1 sig { s with msg := s.msg + 24 }).1) ::
        (readEs 1 sig { s with msg := s.msg + 24 }).1, (readEs 1 sig { s with msg := s.msg + 24 }).2) := by
    rw [sumcheckRoundPoly, dm_bind, readE_run]; rfl
  rw [e, readEs_run]
  obtain ⟨en, m, o⟩ := s
  simp only [pos_mk, List.range_one, List.map_cons, List.map_nil, sumE, List.foldl_cons,
    List.foldl_nil, zero_add, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  have e1 : en + (m + 24) + 40 = en + m + 64 := by omega
  have e2 : m + 24 + 24 = m + 48 := by omega
  rw [e1, e2]

/-! ## Fold rounds -/

theorem foldRounds_step (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    foldRounds (n + 1) st lf sig s =
      foldRounds n { st with
          runningQuad := [feAt sig (pos s + 112),
            polyEval st.runningQuad (feAt sig (pos s + 40)) + feAt sig (pos s + 136),
            feAt sig (pos s + 136)],
          folds := st.folds ++ [feAt sig (pos s + 40)] }
        (lf ++ [feAt sig (pos s + 40)]) sig ⟨pos s + 72, 48, s.ok⟩ := by
  rw [foldRounds, dm_bind, sampleE_run]
  dsimp only
  rw [dm_bind, srp3_run]
  simp only [pos_mk, Nat.add_zero, Nat.zero_add]

theorem frC_succ (sig : ByteArray) (P n : Nat) :
    frC sig P (n + 1) = feAt sig (P + 40) :: frC sig (P + 120) n := by
  simp only [frC, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero,
    List.cons.injEq, true_and]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  congr 1
  omega

theorem foldRounds_run (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    (foldRounds n st lf sig s).1 =
      ({ st with runningQuad := frQ sig (pos s) n st.runningQuad, folds := st.folds ++ frC sig (pos s) n },
        lf ++ frC sig (pos s) n) ∧
    pos (foldRounds n st lf sig s).2 = pos s + 120 * n ∧ (foldRounds n st lf sig s).2.ok = s.ok := by
  induction n generalizing st lf s with
  | zero =>
    refine ⟨?_, ?_, rfl⟩
    · show (st, lf) = _
      simp [frQ, frC]
    · show pos s = pos s + 120 * 0
      simp
  | succ n ih =>
    rw [foldRounds_step]
    obtain ⟨h1, h2, h3⟩ := ih _ _ _
    have hp : pos (⟨pos s + 72, 48, s.ok⟩ : RS) = pos s + 120 := by
      show pos s + 72 + 48 = pos s + 120; omega
    rw [hp] at h1 h2
    refine ⟨?_, ?_, h3⟩
    · rw [h1, frC_succ]
      simp only [frQ, List.append_assoc, List.singleton_append]
    · rw [h2]; ring

/-! ## Positions -/

/-- The positions of `n` answers from position `P` (`positionsAux`'s values). -/
def paF (sig : ByteArray) (h : Nat) : Nat → Nat → Nat → List Nat
  | _, 0, _ => []
  | P, n + 1, rem =>
    (List.range (min positionsPerAnswer rem)).map
        (fun j => (eToNat (feAt sig (P + 40)) >>> (j * h)) % 2 ^ h) ++
      paF sig h (P + 72) n (rem - min positionsPerAnswer rem)

theorem positionsAux_step (h n rem : Nat) (sig : ByteArray) (s : RS) :
    positionsAux h (n + 1) rem sig s =
      ((List.range (min positionsPerAnswer rem)).map
          (fun j => (eToNat (feAt sig (pos s + 40)) >>> (j * h)) % 2 ^ h) ++
        (positionsAux h n (rem - min positionsPerAnswer rem) sig ⟨pos s + 72, 0, s.ok⟩).1,
        (positionsAux h n (rem - min positionsPerAnswer rem) sig ⟨pos s + 72, 0, s.ok⟩).2) := by
  rw [positionsAux, dm_bind, sampleE_run]; rfl

theorem positionsAux_run (h : Nat) : ∀ (n rem : Nat) (sig : ByteArray) (s : RS),
    (positionsAux h n rem sig s).1 = paF sig h (pos s) n rem ∧
    pos (positionsAux h n rem sig s).2 = pos s + 72 * n ∧ (positionsAux h n rem sig s).2.ok = s.ok
  | 0, _, _, s => ⟨rfl, by show pos s = pos s + 72 * 0; simp, rfl⟩
  | n + 1, rem, sig, s => by
    rw [positionsAux_step]
    obtain ⟨h1, h2, h3⟩ := positionsAux_run h n (rem - min positionsPerAnswer rem) sig
      ⟨pos s + 72, 0, s.ok⟩
    have hp : pos (⟨pos s + 72, 0, s.ok⟩ : RS) = pos s + 72 := rfl
    rw [hp] at h1 h2
    refine ⟨?_, ?_, h3⟩
    · dsimp only
      rw [h1]; rfl
    · show pos (positionsAux h n _ sig _).2 = _
      rw [h2]; ring

theorem paF_length (sig : ByteArray) (h : Nat) : ∀ (n P rem : Nat),
    (paF sig h P n rem).length = min (positionsPerAnswer * n) rem
  | 0, _, _ => by simp [paF]
  | n + 1, P, rem => by
    rw [paF, List.length_append, List.length_map, List.length_range, paF_length sig h n]
    simp only [positionsPerAnswer]
    omega

theorem positionsR_run (L : Level) (sig : ByteArray) (s : RS) :
    (positionsR L sig s).1 = qsAt sig (pos s) L ∧
    pos (positionsR L sig s).2 = pos s + 72 * ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) ∧
    (positionsR L sig s).2.ok = s.ok := by
  obtain ⟨h1, h2, h3⟩ := positionsAux_run L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer)
    L.t sig s
  refine ⟨?_, h2, h3⟩
  show (positionsAux _ _ _ sig s).1 = (positionsAux _ _ _ sig ⟨pos s, 0, true⟩).1
  rw [h1, (positionsAux_run _ _ _ sig ⟨pos s, 0, true⟩).1]
  rfl

theorem qsAt_length (sig : ByteArray) (P : Nat) (L : Level) : (qsAt sig P L).length = L.t := by
  show (positionsAux _ _ _ sig ⟨P, 0, true⟩).1.length = L.t
  rw [(positionsAux_run _ _ _ sig ⟨P, 0, true⟩).1, paF_length]
  simp only [positionsPerAnswer]
  omega

/-! ## Openings -/

theorem openingAux_run (L : Level) (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    openingAux L n sig s = ((List.range n).map (fun j => s.ent + 8 + (40 + L.row + 104 * L.path) * j),
      { s with ent := s.ent + (40 + L.row + 104 * L.path) * n })
  | 0, s => by
    show (([] : List Nat), s) = _
    obtain ⟨en, m, o⟩ := s
    simp
  | n + 1, s => by
    have e : openingAux L (n + 1) sig s =
        ((s.ent + 8) :: (openingAux L n sig { s with ent := s.ent + 40 + L.row + 104 * L.path }).1,
          (openingAux L n sig { s with ent := s.ent + 40 + L.row + 104 * L.path }).2) := by
      rw [openingAux]; rfl
    rw [e, openingAux_run L sig n]
    obtain ⟨en, m, o⟩ := s
    refine Prod.ext ?_ ?_
    · show (en + 8) :: (List.range n).map
          (fun j => en + 40 + L.row + 104 * L.path + 8 + (40 + L.row + 104 * L.path) * j) =
        (List.range (n + 1)).map (fun j => en + 8 + (40 + L.row + 104 * L.path) * j)
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      show _ = en + 8 + (40 + L.row + 104 * L.path) * (i + 1)
      ring
    · show (⟨en + 40 + L.row + 104 * L.path + (40 + L.row + 104 * L.path) * n, m, o⟩ : RS) =
        ⟨en + (40 + L.row + 104 * L.path) * (n + 1), m, o⟩
      congr 1
      ring

theorem openingR_run (L : Level) (sig : ByteArray) (s : RS) (h : s.msg = 0) :
    openingR L sig s = ((List.range L.t).map (fun j => s.ent + 8 + (40 + L.row + 104 * L.path) * j),
      ⟨s.ent + (40 + L.row + 104 * L.path) * L.t, 0, s.ok⟩) := by
  have e : openingR L sig s = openingAux L L.t sig { s with ok := s.ok && s.msg == 0 } := rfl
  rw [e, openingAux_run]
  obtain ⟨en, m, o⟩ := s
  simp only at h
  subst h
  simp

/-! ## Tail rounds -/

theorem tailRounds_one (q : List FE) (sig : ByteArray) (s : RS) :
    tailRounds 1 q sig s = (([feAt sig (pos s + 40)], polyEval q (feAt sig (pos s + 40))),
      ⟨pos s + 72, 0, s.ok⟩) := by
  rw [tailRounds, dm_bind, sampleE_run]; rfl

theorem tailRounds_step (n : Nat) (q : List FE) (sig : ByteArray) (s : RS) :
    tailRounds (n + 2) q sig s =
      ((feAt sig (pos s + 40) :: (tailRounds (n + 1) [feAt sig (pos s + 112),
          polyEval q (feAt sig (pos s + 40)) + feAt sig (pos s + 136), feAt sig (pos s + 136)] sig
          ⟨pos s + 72, 48, s.ok⟩).1.1,
        (tailRounds (n + 1) [feAt sig (pos s + 112),
          polyEval q (feAt sig (pos s + 40)) + feAt sig (pos s + 136), feAt sig (pos s + 136)] sig
          ⟨pos s + 72, 48, s.ok⟩).1.2),
        (tailRounds (n + 1) [feAt sig (pos s + 112),
          polyEval q (feAt sig (pos s + 40)) + feAt sig (pos s + 136), feAt sig (pos s + 136)] sig
          ⟨pos s + 72, 48, s.ok⟩).2) := by
  rw [tailRounds, dm_bind, sampleE_run]
  dsimp only
  rw [if_neg (show ¬(n + 1 = 0) by omega), dm_bind, srp3_run]
  simp only [pos_mk, Nat.add_zero, Nat.zero_add]
  have e1 : pos s + 72 + 40 = pos s + 112 := by omega
  have e2 : pos s + 72 + 64 = pos s + 136 := by omega
  rw [e1, e2]
  rfl

theorem tailRounds_run' (n : Nat) : ∀ (q : List FE) (sig : ByteArray) (s : RS),
    tailRounds (n + 1) q sig s =
      ((frC sig (pos s) (n + 1), tlT sig (pos s) (n + 1) q), ⟨pos s + 120 * n + 72, 0, s.ok⟩) := by
  induction n with
  | zero =>
    intro q sig s
    rw [tailRounds_one]
    simp [frC, tlT]
  | succ n ih =>
    intro q sig s
    rw [tailRounds_step, ih]
    have hp : pos (⟨pos s + 72, 48, s.ok⟩ : RS) = pos s + 120 := by
      show pos s + 72 + 48 = pos s + 120; omega
    rw [hp, frC_succ sig (pos s) (n + 1)]
    refine Prod.ext (Prod.ext rfl rfl) ?_
    show (⟨pos s + 120 + 120 * n + 72, 0, s.ok⟩ : RS) = ⟨pos s + 120 * (n + 1) + 72, 0, s.ok⟩
    congr 1
    ring

theorem tailRounds_run (n : Nat) (hn : 1 ≤ n) (q : List FE) (sig : ByteArray) (s : RS) :
    tailRounds n q sig s = ((frC sig (pos s) n, tlT sig (pos s) n q), ⟨pos s + 120 * (n - 1) + 72, 0, s.ok⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [tailRounds_run' m]
  simp

/-! ## Simp forms -/

theorem foldRounds_fst (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    (foldRounds n st lf sig s).1 =
      ({ st with runningQuad := frQ sig (pos s) n st.runningQuad, folds := st.folds ++ frC sig (pos s) n },
        lf ++ frC sig (pos s) n) := (foldRounds_run n st lf sig s).1

theorem foldRounds_pos (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    pos (foldRounds n st lf sig s).2 = pos s + 120 * n := (foldRounds_run n st lf sig s).2.1

theorem foldRounds_ok (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    (foldRounds n st lf sig s).2.ok = s.ok := (foldRounds_run n st lf sig s).2.2

theorem positionsR_fst (L : Level) (sig : ByteArray) (s : RS) :
    (positionsR L sig s).1 = qsAt sig (pos s) L := (positionsR_run L sig s).1

theorem positionsR_pos (L : Level) (sig : ByteArray) (s : RS) :
    pos (positionsR L sig s).2 = pos s + 72 * ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) :=
  (positionsR_run L sig s).2.1

theorem positionsR_ok (L : Level) (sig : ByteArray) (s : RS) : (positionsR L sig s).2.ok = s.ok :=
  (positionsR_run L sig s).2.2

theorem frC_length (sig : ByteArray) (P n : Nat) : (frC sig P n).length = n := by simp [frC]

theorem pos_mk0 (a : Nat) (o : Bool) : pos ⟨a, 0, o⟩ = a := rfl

theorem pos_msg (s : RS) (n : Nat) : pos { s with msg := s.msg + n } = pos s + n := by
  show s.ent + (s.msg + n) = s.ent + s.msg + n; omega

theorem pos_upd (s : RS) (n : Nat) (o : Bool) : pos ⟨s.ent, s.msg + n, o⟩ = pos s + n := by
  show s.ent + (s.msg + n) = s.ent + s.msg + n; omega

theorem pos_mk48 (a : Nat) (o : Bool) : pos ⟨a, 48, o⟩ = a + 48 := rfl

theorem openingR_mk (L : Level) (sig : ByteArray) (a : Nat) (o : Bool) :
    openingR L sig ⟨a, 0, o⟩ = ((List.range L.t).map (fun j => a + 8 + (40 + L.row + 104 * L.path) * j),
      ⟨a + (40 + L.row + 104 * L.path) * L.t, 0, o⟩) := openingR_run L sig _ rfl

/-! ## The OOD items and the grinding (JB-L §3, PI-GRIND) -/

/-- The OOD point `z` of a level: `κ` samples from position `Pc`. -/
def oodZ (sig : ByteArray) (Pc κ : Nat) : List FE := (List.range κ).map fun j => feAt sig (Pc + 72 * j + 40)

/-- `F`'s OOD claims of a level (`oodStep`) from position `Pc` (after the next cap): with `ood`, the
intro polynomial `[c₀, y + c₂, c₂]` and the weight `eq(z, ·)`; none without. -/
def oodF (sig : ByteArray) (ood : Bool) (κ Pc : Nat) : List (List FE × (List FE → FE)) :=
  if ood then [([feAt sig (Pc + 72 * κ + 24 + 40), feAt sig (Pc + 72 * κ + 40) + feAt sig (Pc + 72 * κ + 24 + 64),
    feAt sig (Pc + 72 * κ + 24 + 64)], fun x => eqEval (oodZ sig Pc κ) x)] else []

/-- `F`'s proof-of-work check of a level whose grinding starts at position `Po`: the PoW challenge is the
answer at `Po + 136` (after the separator and the nonce). -/
def powF (sig : ByteArray) (g Po : Nat) : Bool := if g = 0 then true else powOKR g (feAt sig (Po + 136))

theorem samples_succ_run (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    samples (n + 1) sig s = ((List.range (n + 1)).map fun j => feAt sig (pos s + 72 * j + 40),
      ⟨pos s + 72 * (n + 1), 0, s.ok⟩)
  | 0, s => by
    rw [samples, dm_bind, sampleE_run]
    show ([feAt sig (pos s + 40)], (⟨pos s + 72, 0, s.ok⟩ : RS)) = _
    simp
  | n + 1, s => by
    have e : samples (n + 1 + 1) sig s =
        (feAt sig (pos s + 40) :: (samples (n + 1) sig ⟨pos s + 72, 0, s.ok⟩).1,
          (samples (n + 1) sig ⟨pos s + 72, 0, s.ok⟩).2) := by
      show (sampleE >>= fun x => samples (n + 1) >>= fun xs => pure (x :: xs)) sig s = _
      rw [dm_bind, sampleE_run]; rfl
    rw [e, samples_succ_run sig n, pos_mk0]
    refine Prod.ext ?_ ?_
    · show feAt sig (pos s + 40) :: _ = _
      apply List.ext_getElem (by simp)
      intro i h1 h2
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
        congr 1; ring
    · show (⟨_, _, _⟩ : RS) = ⟨_, _, _⟩
      rw [RS.mk.injEq]; exact ⟨by ring, rfl, rfl⟩

theorem oodStep_true (κ : Nat) (hκ : 1 ≤ κ) (sig : ByteArray) (s : RS) :
    oodStep true κ sig s = (oodF sig true κ (pos s), ⟨pos s + 72 * κ, 72, s.ok⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, κ = m + 1 := ⟨κ - 1, by omega⟩
  show (samples (m + 1) >>= fun z => readE >>= fun y => sumcheckRoundPoly 3 y none >>= fun intro =>
    pure [(intro, fun x => eqEval z x)]) sig s = _
  rw [dm_bind, samples_succ_run, dm_bind, readE_run, dm_bind, srp3_run, dm_pure]
  simp only [oodF, ↓reduceIte, oodZ, pos_mk0, pos_msg]
  rfl

theorem oodStep_false (κ : Nat) (sig : ByteArray) (s : RS) : oodStep false κ sig s = ([], s) := rfl

theorem grindPreR_run (g : Nat) (hg : g ≠ 0) (sig : ByteArray) (s : RS) :
    grindPreR g sig s = ((), ⟨pos s + 72, 24, s.ok⟩) := by
  simp only [grindPreR, hg, ↓reduceIte, dm_bind, sampleE_run, readE_run, dm_pure]

theorem powCheckR_run (g : Nat) (hg : g ≠ 0) (sig : ByteArray) (s : RS) :
    powCheckR g sig s = ((), ⟨pos s + 72, 0, powOKR g (feAt sig (pos s + 40)) && s.ok⟩) := by
  simp only [powCheckR, hg, ↓reduceIte, dm_bind, sampleE_run, require_runW]

theorem pos_mk72 (a : Nat) (o : Bool) : pos ⟨a, 72, o⟩ = a + 72 := rfl
theorem pos_mk24 (a : Nat) (o : Bool) : pos ⟨a, 24, o⟩ = a + 24 := rfl

theorem grindPreR_zero (sig : ByteArray) (s : RS) : grindPreR 0 sig s = ((), s) := rfl
theorem powCheckR_zero (sig : ByteArray) (s : RS) : powCheckR 0 sig s = ((), s) := rfl

/-! ## One level of `whirLevels` -/

theorem whirLevels_step (ν lf : Nat) (B : List FE → FE) (g : Nat) (ood : Bool) (L N : Level) (rest : List Level)
    (st : WhirState) (sig : ByteArray) (s : RS) (V : Nat) (hs : pos s = 8 * V) (hrow : L.row % 8 = 0)
    (hκ : L.kappa = ν - (st.folds.length + L.fold)) (hκ1 : 1 ≤ L.kappa) :
    whirLevels ν lf B false g ood (L :: N :: rest) st sig s =
      whirLevels ν lf B false g ood (N :: rest)
        (glue (feAt sig (8 * (lvLanes g ood L (some N) V).V3 + 40))
          ⟨frQ sig (8 * V) L.fold st.runningQuad, st.folds ++ frC sig (8 * V) L.fold, st.glued⟩
          (oodF sig ood L.kappa (8 * (lvLanes g ood L (some N) V).Vc) ++
          [([feAt sig (8 * (lvLanes g ood L (some N) V).V5 + 40),
              Lvm.dot (powers (feAt sig (8 * (lvLanes g ood L (some N) V).V3 + 40)) L.t)
                ((List.range L.t).map fun j =>
                  if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold))
                    (8 * ((lvLanes g ood L (some N) V).V4 + 1 + oStr L * j)) (L.row / 8)
                  else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold))
                    (8 * ((lvLanes g ood L (some N) V).V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
                feAt sig (8 * (lvLanes g ood L (some N) V).V5 + 64),
              feAt sig (8 * (lvLanes g ood L (some N) V).V5 + 64)],
            fun x => inducedWeight L.kappa
              (qsAt sig (8 * (lvLanes g ood L (some N) V).V2) L)
              (powers (feAt sig (8 * (lvLanes g ood L (some N) V).V3 + 40)) L.t) x)]))
        sig ⟨8 * (lvLanes g ood L (some N) V).V5, 48, powF sig g (8 * (lvLanes g ood L (some N) V).Vo) && s.ok⟩ := by
  have hD : 40 + L.row + 104 * L.path = 8 * oStr L := by unfold oStr; omega
  conv_lhs => rw [whirLevels]
  have hfl : ∀ (x : List FE), (st.folds ++ x).length = st.folds.length + x.length := fun x => List.length_append
  have base := fun (h1 : List (List FE × (List FE → FE)) → Prop) => h1
  cases ood <;> rcases Nat.eq_zero_or_pos g with rfl | hg
  all_goals first
    | (have hg0 : g ≠ 0 := Nat.pos_iff_ne_zero.mp hg
       simp only [oodStep_true _ hκ1, oodStep_false, grindPreR_run _ hg0, powCheckR_run _ hg0,
        dm_bind, dm_pure, skip_run, read_run, sampleE_run, srp3_run, foldRounds_fst, foldRounds_pos,
        foldRounds_ok, positionsR_fst, positionsR_pos, positionsR_ok, pos_upd, pos_mk0, pos_mk72, pos_mk24, pos_mk48,
        openingR_mk, hs, List.nil_append, hfl, frC_length, qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ]
       simp only [lvLanes, oodF, powF, nodeBytes, hg0, Bool.and_true, Bool.true_and, Bool.and_false,
        Option.isSome_some, ↓reduceIte, Bool.false_eq_true, List.nil_append, hD]
       ring_nf)
    | (simp only [oodStep_true _ hκ1, oodStep_false, grindPreR_zero, powCheckR_zero,
        dm_bind, dm_pure, skip_run, read_run, sampleE_run, srp3_run, foldRounds_fst, foldRounds_pos,
        foldRounds_ok, positionsR_fst, positionsR_pos, positionsR_ok, pos_upd, pos_mk0, pos_mk72, pos_mk24, pos_mk48,
        openingR_mk, hs, List.nil_append, hfl, frC_length, qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ]
       simp only [lvLanes, oodF, powF, nodeBytes, Bool.and_true, Bool.true_and, Bool.and_false,
        Option.isSome_some, ↓reduceIte, Bool.false_eq_true, List.nil_append, hD]
       ring_nf)

/-- The final level of `whirLevels` from position `8V`, explicitly (`m` = the message log). -/
theorem whirLevels_final (ν lf : Nat) (B : List FE → FE) (g : Nat) (ood : Bool) (L : Level) (st : WhirState)
    (sig : ByteArray) (s : RS) (V : Nat) (hs : pos s = 8 * V) (hrow : L.row % 8 = 0)
    (hκ : L.kappa = ν - (st.folds.length + L.fold)) (hm : 1 ≤ L.kappa) :
    let ll := lvLanes g ood L none V
    let lam := feAt sig (8 * ll.V3 + 40)
    let st' := glue lam ⟨frQ sig (8 * V) L.fold st.runningQuad, st.folds ++ frC sig (8 * V) L.fold, st.glued⟩
      [([feAt sig (8 * ll.V5 + 40),
          Lvm.dot (powers lam L.t) ((List.range L.t).map fun j =>
              if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold)) (8 * (ll.V4 + 1 + oStr L * j))
                (L.row / 8)
              else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold)) (8 * (ll.V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
            feAt sig (8 * ll.V5 + 64),
          feAt sig (8 * ll.V5 + 64)],
        fun x => inducedWeight L.kappa (qsAt sig (8 * ll.V2) L) (powers lam L.t) x)]
    let tf := frC sig (8 * ll.V6) L.kappa
    let point := st'.folds ++ tf
    let weight := st'.glued.foldl
      (fun w cl => w + cl.scalar * cl.weightAt (st'.folds.drop cl.foldStart ++ tf))
      (B (point.drop lf ++ point.take lf))
    whirLevels ν lf B false g ood [L] st sig s =
      ((), ⟨8 * ll.V6 + 120 * (L.kappa - 1) + 72, 0,
        (weight * multilinearEval ((List.range (2 ^ L.kappa)).map fun i => feAt sig (8 * ll.V1 + 40 + 24 * i)) tf ==
          tlT sig (8 * ll.V6) L.kappa st'.runningQuad) && (powF sig g (8 * ll.Vo) && s.ok)⟩) := by
  dsimp only
  have hD : 40 + L.row + 104 * L.path = 8 * oStr L := by unfold oStr; omega
  conv_lhs => rw [whirLevels]
  have hfl : ∀ (x : List FE), (st.folds ++ x).length = st.folds.length + x.length := fun x => List.length_append
  rcases Nat.eq_zero_or_pos g with rfl | hg
  all_goals first
    | (have hg0 : g ≠ 0 := Nat.pos_iff_ne_zero.mp hg
       simp only [grindPreR_run _ hg0, powCheckR_run _ hg0, dm_bind, dm_pure, read_run, sampleE_run, srp3_run,
        readEs_run, require_runW, foldRounds_fst, foldRounds_pos, foldRounds_ok, positionsR_fst, positionsR_pos,
        positionsR_ok, pos_upd, pos_mk0, pos_mk24, pos_mk48, openingR_mk, hs, List.nil_append, hfl, frC_length,
        qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ, tailRounds_run L.kappa hm,
        Bool.false_eq_true, ↓reduceIte, pos_msg]
       simp only [lvLanes, powF, hg0, Bool.and_false, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hD]
       ring_nf)
    | (simp only [grindPreR_zero, powCheckR_zero, dm_bind, dm_pure, read_run, sampleE_run, srp3_run,
        readEs_run, require_runW, foldRounds_fst, foldRounds_pos, foldRounds_ok, positionsR_fst, positionsR_pos,
        positionsR_ok, pos_upd, pos_mk0, pos_mk24, pos_mk48, openingR_mk, hs, List.nil_append, hfl, frC_length,
        qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ, tailRounds_run L.kappa hm,
        Bool.false_eq_true, ↓reduceIte, pos_msg]
       simp only [lvLanes, powF, Bool.and_false, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hD, Bool.true_and]
       ring_nf)
end Lvm.Har
