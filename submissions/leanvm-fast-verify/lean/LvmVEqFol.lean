-- New for lvm (WP-14a, H0): `Fol` (LvmVEqShape) for the verifier language's combinators against the
-- schedule's builders (LvmSchedule): sumcheck rounds, the grand-product GKR, the Keccak GKR, ring
-- switching, the unique-decoding WHIR opening; and the event kinds of an accepted run (`fol_after`).
import LvmVEqShape
import LvmWhirProg
import LvmCertSExqKinds

/-!
# The verifier language's combinators follow the schedule's builders

**`FolP cap shp idx P as R`**: from every pending-position list `pp`, the program `P` follows the
atoms `as` (`Fol`), leaves `pp` as it was and returns `a` with `R a`. Every phase but the WHIR
openings (whose positions and openings read and set `pp`) is of this form; `FolP.bind` composes.

* `folP_sumcheck`, `folP_sumcheckRoundPoly`: `sumcheck` against `sumcheckI`;
* `folP_gkrLayers`, `folP_verifyGkrGrandProducts`: the grand-product GKR against `gpLayersI`, `gpI`
  (the same recursion: one level when the remaining depth is odd, two otherwise);
* `folP_verifyKeccakLayer`, `folP_keccakLayers`, `folP_verifyKeccak`: against `keccakLayerI`,
  `keccakI`; `folP_ringSwitch`: against `smp ringStages`;
* `fol_samplePositions`: the positions item (a `pclr`, then `⌈t/8⌉` position samples) sets `pp` to
  the positions the program returns;
* `fol_whirLevelsUd`, `fol_verifyStackedUd`: the WHIR opening against `whirLevelsI`, `whirI`, given
  `LvMatch` (the configuration's levels are the schedule's, with the commitment table);
* `fol_after`: the event kinds of an accepted run of a program that follows `as` are `as`'s kinds
  (`atomKinds`); `atomKinds_atomsOf`: on reads and samples they are the items' (`itemKinds`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## Atoms of the builders -/

section Atoms

variable (p : Params)

@[simp] theorem atomsOf_rd (m : ℕ) : atomsOf p (rd m) = List.replicate m .rd := by
  unfold rd; split <;> simp_all [atomsOf, itemAtoms]

@[simp] theorem atomsOf_smp (n : ℕ) : atomsOf p (smp n) = List.replicate n .sm := by
  induction n with
  | zero => rfl
  | succ n ih => rw [smp, List.replicate_succ, atomsOf_cons, ← smp, ih]; rfl

theorem atomsOf_flatten (l : List (List Item)) : atomsOf p l.flatten = (l.map (atomsOf p)).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatten_cons, atomsOf_append, ih]; rfl

theorem atomsOf_replicate (n : ℕ) (l : List Item) :
    atomsOf p (List.replicate n l).flatten = (List.replicate n (atomsOf p l)).flatten := by
  rw [atomsOf_flatten, List.map_replicate]

@[simp] theorem atomsOf_sample : atomsOf p [.sample] = [.sm] := rfl

@[simp] theorem atomsOf_opening (r : Ref) : atomsOf p [.opening r] = [.op r] := rfl

@[simp] theorem atomsOf_capI (c : ℕ) (r : Ref) : atomsOf p [.cap c r] = [.cap c r] := rfl

theorem atomsOf_positions (r : Ref) :
    atomsOf p [.positions r] =
      .pclr :: posAtoms (p.level r).height (p.level r).nPosQ (p.level r).t := by
  simp [atomsOf, itemAtoms]

theorem atomsOf_sumcheckI_succ (n d : ℕ) :
    atomsOf p (sumcheckI (n + 1) d) = List.replicate d .rd ++ (.sm :: atomsOf p (sumcheckI n d)) := by
  show atomsOf p ((rd d ++ [.sample]) ++ sumcheckI n d) = _
  rw [atomsOf_append, atomsOf_append, atomsOf_rd, atomsOf_sample, List.append_assoc]; rfl

theorem atomsOf_sumcheckI_zero (d : ℕ) : atomsOf p (sumcheckI 0 d) = [] := rfl

end Atoms

/-! ## `FolP`: following without the positions -/

section FolP

variable (cap : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (idx : Ref → ℕ)

/-- From every `pp`, `P` follows `as`, keeps `pp` and returns `a` with `R a` (a structure, so that
the elaborator never unfolds it into `Fol` on concrete atoms). -/
structure FolP {α : Type} (P : VerifierProgram α) (as : List Atom) (R : α → Prop) : Prop where
  /-- Unfold. -/
  run : ∀ pp, Fol cap shp idx P as pp fun a pp' ↦ pp' = pp ∧ R a

variable {cap shp idx}

theorem FolP.ret {α : Type} {a : α} {R : α → Prop} (h : R a) : FolP cap shp idx (.ret a) [] R :=
  ⟨fun _ ↦ ⟨rfl, h⟩⟩

theorem FolP.fail {α : Type} (as : List Atom) (R : α → Prop) : FolP cap shp idx .fail as R :=
  ⟨fun _ ↦ fol_fail _ _ _⟩

theorem FolP.mono {α : Type} {P : VerifierProgram α} {as : List Atom} {R S : α → Prop}
    (h : FolP cap shp idx P as R) (hRS : ∀ a, R a → S a) : FolP cap shp idx P as S :=
  ⟨fun pp ↦ (h.run pp).mono fun _ _ h ↦ ⟨h.1, hRS _ h.2⟩⟩

theorem FolP.bind {α β : Type} {P : VerifierProgram α} {f : α → VerifierProgram β} {as bs : List Atom}
    {R : α → Prop} {S : β → Prop} (hP : FolP cap shp idx P as R)
    (hf : ∀ a, R a → FolP cap shp idx (f a) bs S) : FolP cap shp idx (P.bind f) (as ++ bs) S :=
  ⟨fun pp ↦ Fol.bind ((hP.run pp).mono fun a pp' h ↦ by obtain ⟨rfl, h2⟩ := h; exact (hf a h2).run _)⟩

/-- Composition with a step that reads nothing. -/
theorem FolP.bind_nil {α β : Type} {P : VerifierProgram α} {f : α → VerifierProgram β} {as : List Atom}
    {R : α → Prop} {S : β → Prop} (hP : FolP cap shp idx P as R)
    (hf : ∀ a, R a → FolP cap shp idx (f a) [] S) : FolP cap shp idx (P.bind f) as S := by
  simpa using FolP.bind hP hf

theorem FolP.bind_ret {α β : Type} {P : VerifierProgram α} {g : α → β} {as : List Atom}
    {R : α → Prop} {S : β → Prop} (hP : FolP cap shp idx P as R) (hg : ∀ a, R a → S (g a)) :
    FolP cap shp idx (P.bind fun a ↦ .ret (g a)) as S :=
  hP.bind_nil fun a ha ↦ FolP.ret (hg a ha)

/-- `FolP` as `Fol`. -/
theorem FolP.fol {α : Type} {P : VerifierProgram α} {as : List Atom} {R : α → Prop}
    (h : FolP cap shp idx P as R) (pp : List ℕ) : Fol cap shp idx P as pp fun _ pp' ↦ pp' = pp :=
  (h.run pp).mono fun _ _ h ↦ h.1

theorem FolP.read {α : Type} {k : E → VerifierProgram α} {as : List Atom} {R : α → Prop}
    (h : ∀ y, FolP cap shp idx (k y) as R) : FolP cap shp idx (.read k) (.rd :: as) R :=
  ⟨fun pp y ↦ (h y).run pp⟩

theorem FolP.sample {α : Type} {k : E → VerifierProgram α} {as : List Atom} {R : α → Prop}
    (h : ∀ y, FolP cap shp idx (k y) as R) : FolP cap shp idx (.sample k) (.sm :: as) R :=
  ⟨fun pp y ↦ (h y).run pp⟩

theorem FolP.commit {α : Type} {ht w c : ℕ} {r : Ref} {k : VerifierProgram α} {as : List Atom}
    {R : α → Prop} (hc : cap ht w = c) (hs : shp (idx r) = (ht, w)) (h : FolP cap shp idx k as R) :
    FolP cap shp idx (.commit ht w k) (.cap c r :: as) R :=
  ⟨fun pp ↦ ⟨hc, hs, h.run pp⟩⟩

theorem folP_readScalars (n : ℕ) :
    FolP cap shp idx (VerifierProgram.readScalars n) (List.replicate n .rd) fun xs ↦ xs.length = n :=
  ⟨fun pp ↦ (fol_readScalars n pp).mono fun _ _ h ↦ ⟨h.2, h.1⟩⟩

theorem folP_sampleChallenges (n : ℕ) :
    FolP cap shp idx (VerifierProgram.sampleChallenges n) (List.replicate n .sm)
      fun xs ↦ xs.length = n :=
  ⟨fun pp ↦ (fol_sampleChallenges n pp).mono fun _ _ h ↦ ⟨h.2, h.1⟩⟩

theorem folP_readScalar : FolP cap shp idx VerifierProgram.readScalar [.rd] fun _ ↦ True :=
  FolP.read fun _ ↦ FolP.ret trivial

theorem folP_sampleChallenge : FolP cap shp idx VerifierProgram.sampleChallenge [.sm] fun _ ↦ True :=
  FolP.sample fun _ ↦ FolP.ret trivial

theorem folP_require (c : Prop) [Decidable c] :
    FolP cap shp idx (VerifierProgram.require c) [] fun _ ↦ c := by
  refine ⟨fun pp ↦ ?_⟩
  unfold VerifierProgram.require
  split
  · exact ⟨rfl, by assumption⟩
  · trivial

theorem folP_readCommitment {ht w c : ℕ} {r : Ref} (hc : cap ht w = c) (hs : shp (idx r) = (ht, w)) :
    FolP cap shp idx (VerifierProgram.readCommitment ht w) [.cap c r] fun _ ↦ True :=
  FolP.commit hc hs (FolP.ret trivial)

end FolP

/-! ## Sumcheck rounds and the grand-product GKR -/

section Rounds

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- A round polynomial of `d + 1` coefficients: `d` scalars, in either mode. -/
theorem folP_sumcheckRoundPoly {count d : ℕ} (hc : count = d + 1) (hd : 1 ≤ d) (claim : E)
    (e : Option E) :
    FolP cap shp idx (Verifier.sumcheckRoundPoly count claim e) (List.replicate d .rd) fun _ ↦ True := by
  subst hc
  cases e with
  | none =>
    obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
    exact folP_readScalar.bind fun _ _ ↦ (folP_readScalars c).bind_ret fun _ _ ↦ trivial
  | some r => exact (folP_readScalars d).bind_ret fun _ _ ↦ trivial

/-- **`sumcheck` against `sumcheckI`**: `n` rounds of `d` scalars and a challenge. -/
theorem folP_sumcheck {count d : ℕ} (hc : count = d + 1) (hd : 1 ≤ d) :
    ∀ (eqs : List (Option E)) (n : ℕ) (claim : E), eqs.length = n →
      FolP cap shp idx (Verifier.sumcheck claim count eqs) (atomsOf p (sumcheckI n d))
        fun r ↦ r.1.length = n
  | [], _, _, rfl => FolP.ret rfl
  | e :: es, _, claim, rfl => by
    rw [List.length_cons, atomsOf_sumcheckI_succ]
    exact (folP_sumcheckRoundPoly hc hd claim e).bind fun m _ ↦ folP_sampleChallenge.bind fun c _ ↦
      (folP_sumcheck hc hd es _ _ rfl).bind_nil fun r hr ↦ FolP.ret (by simp [hr])

theorem sumcheckI_smp (n d : ℕ) : (List.replicate n (rd d ++ smp 1)).flatten = sumcheckI n d := rfl

/-- The items of one step of the grand-product GKR. -/
def gpStepI (step point : ℕ) : List Item :=
  List.flatten [smp 1, (List.replicate point (rd (2 ^ step) ++ smp 1)).flatten,
    rd (3 * 2 ^ step), smp step]

theorem folP_gkrStep (step : ℕ) (s : Verifier.GkrState) :
    FolP cap shp idx (Verifier.gkrStep step s) (atomsOf p (gpStepI step s.point.length))
      fun s' ↦ s'.point.length = s.point.length + step := by
  have h3 : List.replicate (3 * 2 ^ step) Atom.rd = List.replicate (2 ^ step) .rd ++
      (List.replicate (2 ^ step) .rd ++ List.replicate (2 ^ step) .rd) := by
    rw [← List.replicate_add, ← List.replicate_add]; congr 1; ring
  simp only [gpStepI, sumcheckI_smp, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append,
    atomsOf_rd, atomsOf_smp, h3, List.append_assoc]
  unfold Verifier.gkrStep
  exact folP_sampleChallenge.bind fun _ _ ↦
    (folP_sumcheck p rfl (Nat.one_le_two_pow) _ _ _ (List.length_map _)).bind fun x hx ↦
    (folP_readScalars _).bind fun _ _ ↦ (folP_readScalars _).bind fun _ _ ↦
    (folP_readScalars _).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_sampleChallenges step).bind_ret fun y hy ↦ by simp [hy, hx, Nat.add_comm]

theorem gpLayersI_zero (fuel point : ℕ) : gpLayersI fuel 0 point = [] := by cases fuel <;> rfl

theorem gpLayersI_succ (fuel layer point : ℕ) (h : layer ≠ 0) :
    gpLayersI (fuel + 1) layer point =
      gpStepI (if layer % 2 = 1 then 1 else 2) point ++
        gpLayersI fuel (layer - if layer % 2 = 1 then 1 else 2) (point + if layer % 2 = 1 then 1 else 2) := by
  simp only [gpLayersI, h, ↓reduceIte, gpStepI]

/-- **The GKR layers against `gpLayersI`** (the same recursion). -/
theorem folP_gkrLayers : ∀ (fuel n : ℕ) (s : Verifier.GkrState), n ≤ fuel →
    FolP cap shp idx (Verifier.gkrLayers n s) (atomsOf p (gpLayersI fuel n s.point.length))
      fun s' ↦ s'.point.length = s.point.length + n
  | 0, 0, s, _ => FolP.ret rfl
  | fuel + 1, 0, s, _ => by rw [gpLayersI_zero]; exact FolP.ret rfl
  | fuel + 1, 1, s, _ => by
    rw [gpLayersI_succ _ _ _ (by omega)]
    simp only [show 1 % 2 = 1 from rfl, ↓reduceIte, Nat.sub_self, gpLayersI_zero, List.append_nil]
    exact (folP_gkrStep p 1 s).bind_nil fun s' hs ↦ FolP.ret hs
  | fuel + 1, m + 2, s, hm => by
    rw [gpLayersI_succ _ _ _ (by omega), atomsOf_append]
    by_cases h : m % 2 = 1
    · have h' : (m + 2) % 2 = 1 := by omega
      simp only [h', ↓reduceIte]
      show FolP cap shp idx (if m % 2 = 1 then _ else _) _ _
      rw [ite_cond_eq_true _ _ (eq_true h)]
      exact (folP_gkrStep p 1 s).bind fun s' hs ↦ by
        rw [show m + 2 - 1 = m + 1 by omega, ← hs]
        exact (folP_gkrLayers fuel (m + 1) s' (by omega)).mono fun s'' h'' ↦ by omega
    · have h' : ¬ (m + 2) % 2 = 1 := by omega
      simp only [h', ↓reduceIte]
      show FolP cap shp idx (if m % 2 = 1 then _ else _) _ _
      rw [ite_cond_eq_false _ _ (eq_false h)]
      exact (folP_gkrStep p 2 s).bind fun s' hs ↦ by
        rw [show m + 2 - 2 = m by omega, ← hs]
        exact (folP_gkrLayers fuel m s' (by omega)).mono fun s'' h'' ↦ by omega
  | 0, _ + 1, _, h => absurd h (by omega)

/-- **`verify_gkr_grand_products` against `gpI`.** -/
theorem folP_verifyGkrGrandProducts (depth : ℕ) :
    FolP cap shp idx (Verifier.verifyGkrGrandProducts depth) (atomsOf p (gpI depth))
      fun r ↦ r.2.1.length = depth := by
  rw [gpI, atomsOf_append, atomsOf_rd]
  unfold Verifier.verifyGkrGrandProducts
  exact folP_readScalar.bind fun _ _ ↦ folP_readScalar.bind fun _ _ ↦
    (folP_gkrLayers p depth depth _ le_rfl).bind_ret fun s hs ↦ by simpa using hs

end Rounds

/-! ## The Keccak GKR and ring switching -/

section Keccak

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

theorem folP_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    FolP cap shp idx (Verifier.keccakPackRounds rs value scale) (atomsOf p (sumcheckI rs.length 2))
      fun r ↦ r.2.2.length = rs.length
  | [], _, _ => FolP.ret rfl
  | r :: rs, value, scale => by
    rw [List.length_cons, atomsOf_sumcheckI_succ]
    exact (folP_sumcheckRoundPoly rfl (by norm_num) value (some r)).bind fun m _ ↦
      folP_sampleChallenge.bind fun c _ ↦
      (folP_keccakPackRounds rs _ _).bind_nil fun x hx ↦ FolP.ret (by simp [hx])

/-- **A Keccak layer against `keccakLayerI`.** -/
theorem folP_verifyKeccakLayer (logSteps step : ℕ) (claim : Verifier.KeccakClaim) :
    FolP cap shp idx (Verifier.verifyKeccakLayer logSteps step claim)
      (atomsOf p (keccakLayerI claim.point.length)) fun c ↦ c.point.length = claim.point.length := by
  simp only [keccakLayerI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append,
    atomsOf_rd, atomsOf_smp]
  unfold Verifier.verifyKeccakLayer
  exact (folP_readScalars _).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    folP_sampleChallenge.bind fun _ _ ↦ (folP_keccakPackRounds p claim.point _ _).bind fun x hx ↦
    (folP_sumcheck p rfl (by norm_num) _ localBits _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 3).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    folP_sampleChallenge.bind_ret fun _ _ ↦ hx

theorem folP_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : Verifier.KeccakClaim),
    FolP cap shp idx (Verifier.keccakLayers logSteps steps claim)
      (List.replicate steps.length (atomsOf p (keccakLayerI claim.point.length))).flatten
      fun c ↦ c.point.length = claim.point.length
  | [], _ => FolP.ret rfl
  | st :: steps, claim => by
    rw [List.length_cons, List.replicate_succ, List.flatten_cons]
    exact (folP_verifyKeccakLayer p logSteps st claim).bind fun c hc ↦ by
      rw [← hc]
      exact folP_keccakLayers logSteps steps c

theorem folP_keccakOpen (logSteps : ℕ) (claim : Verifier.KeccakClaim) (first count : ℕ) (value : E) :
    FolP cap shp idx (Verifier.keccakOpen logSteps claim first count value) (atomsOf p (sumcheckI slotLog 2))
      fun _ ↦ True := by
  unfold Verifier.keccakOpen
  exact (folP_sumcheck p rfl (by norm_num) _ slotLog _ (by simp; decide)).bind_nil fun _ _ ↦ FolP.ret trivial

/-- **`verify_keccak` against `keccakI`**, the instance point of `logSteps` coordinates. -/
theorem folP_verifyKeccak (logSteps : ℕ) (inst output : List E) (hinst : inst.length = logSteps) :
    FolP cap shp idx (Verifier.verifyKeccak logSteps inst output) (atomsOf p (keccakI logSteps))
      fun _ ↦ True := by
  have hseg : (1 < Verifier.keccakSegments) := by decide
  have h6 : List.replicate (segmentBits + laneBits) Atom.sm =
      List.replicate Verifier.keccakSegmentBits .sm ++ List.replicate Verifier.keccakLaneBits .sm := by
    rw [← List.replicate_add]; rfl
  simp only [keccakI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append,
    atomsOf_rd, atomsOf_smp, h6, List.append_assoc, atomsOf_replicate]
  unfold Verifier.verifyKeccak
  simp only [hseg, ↓reduceIte, pure_bind]
  refine (folP_sampleChallenges _).bind fun seg hseg' ↦ (folP_sampleChallenges _).bind fun lp _ ↦
    folP_readScalar.bind fun cm _ ↦ ?_
  have hpt : (Verifier.keccakFirstClaim inst seg lp output cm).point.length =
      logSteps - packBits + segmentBits := by
    simp only [Verifier.keccakFirstClaim, List.length_append, List.length_drop, hinst, hseg']; rfl
  rw [← hpt, show gkrDepth = (List.range Verifier.keccakDepth).length by simp; rfl]
  exact (folP_keccakLayers p logSteps _ _).bind fun _ _ ↦
    (folP_keccakOpen p _ _ _ _ _).bind fun _ _ ↦ folP_readScalar.bind fun _ _ ↦
    (folP_require _).bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) _ packBits _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_keccakOpen p _ _ _ _ _).bind fun _ _ ↦ (folP_readScalars _).bind fun _ _ ↦
    (folP_require _).bind_nil fun _ _ ↦ FolP.ret trivial

/-- **Ring switching**: six challenges. -/
theorem folP_ringSwitch (point s : List E) :
    FolP cap shp idx (Verifier.ringSwitch point s) (List.replicate ringStages .sm) fun _ ↦ True := by
  unfold Verifier.ringSwitch
  exact (folP_sampleChallenges _).bind_ret fun _ _ ↦ trivial

end Keccak

/-! ## Positions and the WHIR opening -/

section Whir

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- Composition after a step that keeps `pp`. -/
theorem Fol.bindP {α β : Type} {P : VerifierProgram α} {f : α → VerifierProgram β} {as bs : List Atom}
    {R : α → Prop} {pp : List ℕ} {Q : β → List ℕ → Prop} (hP : FolP cap shp idx P as R)
    (hf : ∀ a, R a → Fol cap shp idx (f a) bs pp Q) : Fol cap shp idx (P.bind f) (as ++ bs) pp Q :=
  Fol.bind ((hP.run pp).mono fun a pp' h ↦ by obtain ⟨rfl, h2⟩ := h; exact hf a h2)

/-- Composition, general. -/
theorem Fol.bindQ {α β : Type} {P : VerifierProgram α} {f : α → VerifierProgram β} {as bs : List Atom}
    {pp : List ℕ} {R : α → List ℕ → Prop} {Q : β → List ℕ → Prop} (hP : Fol cap shp idx P as pp R)
    (hf : ∀ a pp', R a pp' → Fol cap shp idx (f a) bs pp' Q) : Fol cap shp idx (P.bind f) (as ++ bs) pp Q :=
  Fol.bind (hP.mono hf)

/-- An opening of the pending positions. -/
theorem fol_queryBind {β : Type} {i : ℕ} {ps : List ℕ} {f : List (List K) → VerifierProgram β} {r : Ref}
    {as : List Atom} {pp : List ℕ} {Q : β → List ℕ → Prop} (hi : i = idx r) (hps : ps = pp)
    (h : ∀ rows, Fol cap shp idx (f rows) as pp Q) :
    Fol cap shp idx ((VerifierProgram.queryOpenings i ps).bind f) (.op r :: as) pp Q :=
  ⟨hi, hps, h⟩

theorem fol_samplePositionsAux (h : ℕ) : ∀ (fuel rem : ℕ) (pp : List ℕ), (rem + 7) / 8 ≤ fuel →
    Fol cap shp idx (Verifier.samplePositionsAux 8 h fuel rem) (posAtoms h ((rem + 7) / 8) rem) pp
      fun qs pp' ↦ pp' = pp ++ qs
  | 0, 0, pp, _ => (List.append_nil pp).symm
  | _ + 1, 0, pp, _ => (List.append_nil pp).symm
  | 0, _ + 1, _, hf => absurd hf (by omega)
  | fuel + 1, rem + 1, pp, hf => by
    have hn : (rem + 1 + 7) / 8 = (rem + 1 - min 8 (rem + 1) + 7) / 8 + 1 := by omega
    rw [hn]
    show Fol cap shp idx (if rem + 1 = 0 then _ else _)
      (.ps h (min 8 (rem + 1)) :: posAtoms h _ (rem + 1 - min 8 (rem + 1))) pp _
    rw [ite_cond_eq_false _ _ (eq_false (by omega))]
    intro y
    rw [← List.append_nil (posAtoms h _ _)]
    dsimp only [VerifierProgram.ret_bind]
    exact Fol.bind ((fol_samplePositionsAux h fuel _ _ (by omega)).mono fun qs pp' hq ↦ by
      rw [hq, List.append_assoc]; rfl)

/-- **The positions item**: a `pclr`, then `⌈t/8⌉` position samples; the pending positions are
then the positions returned. -/
theorem fol_samplePositions (h t : ℕ) (pp : List ℕ) :
    Fol cap shp idx (Verifier.samplePositions 8 h t) (.pclr :: posAtoms h ((t + 7) / 8) t) pp
      fun qs pp' ↦ pp' = qs := by
  rw [fol_pclr]
  exact (fol_samplePositionsAux h t t [] (by omega)).mono fun qs pp' hq ↦ by simpa using hq

theorem folP_foldRoundsT : ∀ (n : ℕ) (s : Verifier.WhirStateT) (lf : List E),
    FolP cap shp idx (Verifier.foldRoundsT n s lf)
      (List.replicate n (List.replicate 1 .sm ++ List.replicate 2 .rd)).flatten
      fun r ↦ r.1.folds.length = s.folds.length + n
  | 0, s, lf => FolP.ret rfl
  | n + 1, s, lf => by
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
    unfold Verifier.foldRoundsT
    exact folP_sampleChallenge.bind fun _ _ ↦ (folP_sumcheckRoundPoly rfl (by norm_num) _ none).bind
      fun _ _ ↦ (folP_foldRoundsT n _ _).mono fun r hr ↦ by simp [hr]; omega

theorem folP_tailRoundsT : ∀ (n : ℕ) (t : E) (q : List E),
    FolP cap shp idx (Verifier.tailRoundsT n t q) (atomsOf p (tailI n)) fun _ ↦ True
  | 0, _, _ => FolP.ret trivial
  | 1, _, _ => by
    unfold Verifier.tailRoundsT
    exact folP_sampleChallenge.bind_nil fun _ _ ↦ FolP.ret trivial
  | n + 2, _, q => by
    rw [tailI, atomsOf_cons, atomsOf_cons]
    unfold Verifier.tailRoundsT
    simp only [show n + 1 ≠ 0 by omega, ↓reduceIte]
    exact folP_sampleChallenge.bind fun _ _ ↦ (folP_sumcheckRoundPoly rfl (by norm_num) _ none).bind
      fun _ _ ↦ (folP_tailRoundsT (n + 1) _ _).bind_nil fun _ _ ↦ FolP.ret trivial

theorem foldl_folds {β : Type} (F : Verifier.WhirStateT × E → β → Verifier.WhirStateT × E)
    (hF : ∀ acc x, (F acc x).1.folds = acc.1.folds) :
    ∀ (l : List β) (acc : Verifier.WhirStateT × E), (l.foldl F acc).1.folds = acc.1.folds
  | [], _ => rfl
  | x :: l, acc => by rw [List.foldl_cons, foldl_folds F hF l, hF]

theorem glueT_folds (lam : E) (s : Verifier.WhirStateT) (pending : List (E × List E × (List E → E))) :
    (Verifier.glueT lam s pending).folds = s.folds := by
  unfold Verifier.glueT
  refine foldl_folds _ ?_ _ _
  intro acc x
  rfl

end Whir

/-! ## The WHIR levels against the schedule's levels -/

section WhirLevels

variable (p : Params) (cap : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (idx : Ref → ℕ)

/-- One level of a WHIR configuration is the schedule's level `L` of commitment `com`: its fold, the
height and query count of the oracle it opens (`p.level`), and the commitment it opens; `f`
variables were folded before it. -/
def LvOne (com : Com) (logN c₀ n₀ index f : ℕ) (w : Whir.Level) (L : Level) : Prop :=
  w.fold = L.fold ∧ (p.level ⟨com, L.level⟩).height = logN - (f + w.fold) + w.logInvRate ∧
    (p.level ⟨com, L.level⟩).t = w.queries ∧ Verifier.cidx c₀ n₀ index = idx ⟨com, L.level⟩

/-- **The configuration's levels are the schedule's**, from level `index` with `f` variables folded:
level by level `LvOne`, the next commitment's shape and cap level as the table records them, and the
final message log. -/
def LvMatch (com : Com) (logN c₀ n₀ finalLog : ℕ) : ℕ → ℕ → List Whir.Level → List Level → Prop
  | index, f, [w], [L] => LvOne p idx com logN c₀ n₀ index f w L ∧ logN - (f + w.fold) = finalLog
  | index, f, w :: w' :: ws, L :: L' :: Ls => LvOne p idx com logN c₀ n₀ index f w L ∧
      cap (logN - (f + w.fold) - w'.fold + w'.logInvRate) (3 * 2 ^ w'.fold) = L'.cap ∧
      shp (idx ⟨com, L.level + 1⟩) = (logN - (f + w.fold) - w'.fold + w'.logInvRate, 3 * 2 ^ w'.fold) ∧
      LvMatch com logN c₀ n₀ finalLog (index + 1) (f + w.fold) (w' :: ws) (L' :: Ls)
  | _, _, _, _ => False

variable {p cap shp idx}

theorem nPosQ_eq {L : Level} {t : ℕ} (h : L.t = t) : L.nPosQ = (t + 7) / 8 := by
  simp only [Level.nPosQ, h, positionsPerAnswer]
  omega

/-- **The WHIR levels against `whirLevelsI`.** -/
theorem fol_whirLevelsUd (com : Com) (logN laneFolds c₀ n₀ finalLog : ℕ) (direct : Bool)
    (eB : List E → E) : ∀ (Ls : List Level) (ws : List Whir.Level) (index : ℕ) (s : Verifier.WhirStateT),
      LvMatch p cap shp idx com logN c₀ n₀ finalLog index s.folds.length ws Ls → ∀ pp,
      Fol cap shp idx (Verifier.whirLevelsUd logN laneFolds 8 c₀ n₀ direct eB index ws s)
        (atomsOf p (whirLevelsI com finalLog Ls)) pp fun _ _ ↦ True
  | [L], [w], index, s, h, pp => by
    obtain ⟨⟨hfold, hh, ht, hc⟩, hfin⟩ := h
    simp only [whirLevelsI, levelI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append,
      atomsOf_cons, itemAtoms, atomsOf_rd, atomsOf_smp, atomsOf_replicate, List.cons_append,
      List.nil_append]
    rw [nPosQ_eq ht, hh, ht, hfin, ← hfold]
    rw [Verifier.whirLevelsUd]
    refine Fol.bindP (folP_foldRoundsT w.fold s []) fun ⟨s', lf⟩ hx ↦ ?_
    dsimp only at hx ⊢
    rw [hx, hfin]
    refine Fol.bindP (folP_readScalars _) fun res _ ↦ ?_
    refine Fol.bindQ (fol_samplePositions _ _ pp) fun qs pp' hq ↦ ?_
    subst hq
    refine Fol.bindP folP_sampleChallenge fun lam _ ↦ ?_
    refine fol_queryBind hc rfl fun rows ↦ ?_
    refine Fol.bindP (folP_sumcheckRoundPoly rfl (by norm_num) _ none) fun intro _ ↦ ?_
    rw [← List.nil_append (atomsOf p (tailI finalLog))]
    refine Fol.bindP (R := fun _ ↦ True) ?_ fun _ _ ↦ ?_
    · cases direct
      · exact FolP.ret trivial
      · exact (folP_require _).mono fun _ _ ↦ trivial
    rw [← List.append_nil (atomsOf p (tailI finalLog))]
    exact Fol.bindP (folP_tailRoundsT p _ _ _) fun _ _ ↦ (fol_require _ _).mono fun _ _ _ ↦ trivial
  | L :: L' :: Ls, w :: w' :: ws, index, s, h, pp => by
    obtain ⟨⟨hfold, hh, ht, hc⟩, hcap, hshp, hrest⟩ := h
    rw [whirLevelsI, atomsOf_append]
    simp only [levelI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append,
      atomsOf_cons, itemAtoms, atomsOf_rd, atomsOf_smp, atomsOf_replicate, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [nPosQ_eq ht, hh, ht, ← hfold]
    rw [Verifier.whirLevelsUd]
    refine Fol.bindP (folP_foldRoundsT w.fold s []) fun ⟨s', lf⟩ hx ↦ ?_
    dsimp only at hx ⊢
    rw [hx]
    refine Fol.bindP (folP_readCommitment hcap hshp) fun _ _ ↦ ?_
    refine Fol.bindP (as := []) (R := fun _ ↦ True) (FolP.ret trivial) fun res _ ↦ ?_
    refine Fol.bindQ (fol_samplePositions _ _ pp) fun qs pp' hq ↦ ?_
    subst hq
    refine Fol.bindP folP_sampleChallenge fun lam _ ↦ ?_
    refine fol_queryBind hc rfl fun rows ↦ ?_
    refine Fol.bindP (folP_sumcheckRoundPoly rfl (by norm_num) _ none) fun intro _ ↦ ?_
    refine fol_whirLevelsUd com logN laneFolds c₀ n₀ finalLog direct eB (L' :: Ls) (w' :: ws) (index + 1) _ ?_ _
    rw [glueT_folds, hx]
    exact hrest
  | [], [], _, _, h, _ => (h : False).elim
  | [], [_], _, _, h, _ => (h : False).elim
  | [], _ :: _ :: _, _, _, h, _ => (h : False).elim
  | [_], [], _, _, h, _ => (h : False).elim
  | _ :: _ :: _, [], _, _, h, _ => (h : False).elim
  | [_], _ :: _ :: _, _, _, h, _ => (h : False).elim
  | _ :: _ :: _, [_], _, _, h, _ => (h : False).elim

/-- **`verify_whir` (unique decoding) against `whirI`.** -/
theorem fol_verifyWhirUd (cfg : Verifier.UdConfig) (hper : cfg.per = 8) (com : Com) (Ls : List Level)
    (finalLog : ℕ) (h : LvMatch p cap shp idx com cfg.μ cfg.c₀ cfg.n₀ finalLog 0 0 cfg.levels Ls)
    (target : E) (eB : List E → E) (pp : List ℕ) :
    Fol cap shp idx (Verifier.verifyWhirUd cfg target eB) (atomsOf p (whirI com Ls finalLog)) pp
      fun _ _ ↦ True := by
  rw [whirI, atomsOf_append, atomsOf_rd]
  unfold Verifier.verifyWhirUd
  rw [hper]
  exact Fol.bindP (folP_sumcheckRoundPoly rfl (by norm_num) _ none) fun _ _ ↦
    fol_whirLevelsUd com _ _ _ _ finalLog _ eB Ls cfg.levels 0 _ h pp

/-- **The stacked opening against `smp 1 ++ whirI`** (the schedule's opening phases). -/
theorem fol_verifyStackedUd (cfg : Verifier.UdConfig) (hper : cfg.per = 8) (com : Com) (Ls : List Level)
    (finalLog : ℕ) (h : LvMatch p cap shp idx com cfg.μ cfg.c₀ cfg.n₀ finalLog 0 0 cfg.levels Ls)
    (claims : List Verifier.StackClaim) (pp : List ℕ) :
    Fol cap shp idx (Verifier.verifyStackedUd cfg claims) (atomsOf p (smp 1 ++ whirI com Ls finalLog)) pp
      fun _ _ ↦ True := by
  rw [atomsOf_append, atomsOf_smp]
  unfold Verifier.verifyStackedUd
  exact Fol.bindP folP_sampleChallenge fun _ _ ↦ fol_verifyWhirUd cfg hper com Ls finalLog h _ _ pp

/-- **The root commitment** against its cap item. -/
theorem folP_commitRootUd (cfg : Verifier.UdConfig) {w : Whir.Level} {ws : List Whir.Level}
    (hl : cfg.levels = w :: ws) {c : ℕ} {r : Ref}
    (hc : cap (cfg.μ - w.fold + w.logInvRate) (2 ^ w.fold) = c)
    (hs : shp (idx r) = (cfg.μ - w.fold + w.logInvRate, 2 ^ w.fold)) :
    FolP cap shp idx (Verifier.commitRootUd cfg) [.cap c r] fun _ ↦ True := by
  unfold Verifier.commitRootUd
  rw [hl]
  exact folP_readCommitment hc hs

end WhirLevels

/-! ## The event kinds of an accepted run -/

section After

open Lvm.ASM

/-- The event kinds the atoms stand for (a `pclr` stands for none). -/
def atomKinds : List Atom → List EvK
  | [] => []
  | .pclr :: as => atomKinds as
  | .rd :: as => .read :: atomKinds as
  | .sm :: as => .sample :: atomKinds as
  | .ps _ _ :: as => .sample :: atomKinds as
  | .cap _ _ :: as => .other :: atomKinds as
  | .op _ :: as => .other :: atomKinds as

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **The events of an accepted run follow the atoms**: a program that follows `as` and has
accepted after the history `l` has met exactly `as`'s kinds, and its value meets the
postcondition. -/
theorem fol_after {α : Type} : ∀ {as : List Atom} {P : VerifierProgram α} {pp : List ℕ}
    {Q : α → List ℕ → Prop}, Fol cap shp idx P as pp Q → ∀ {l : List Ev} {a : α},
      P.after l = some (.ret a) → l.map kindOf = atomKinds as ∧ ∃ pp', Q a pp'
  | [], P, pp, Q, h, l, a, hl => by
    cases P with
    | ret b =>
      cases l with
      | nil =>
        simp only [VerifierProgram.after, Option.some.injEq, VerifierProgram.ret.injEq] at hl
        subst hl; exact ⟨rfl, pp, h⟩
      | cons e es => cases e <;> simp [VerifierProgram.after] at hl
    | fail => cases l with
      | nil => simp [VerifierProgram.after] at hl
      | cons e es => cases e <;> simp [VerifierProgram.after] at hl
    | _ => exact h.elim
  | x :: as, P, pp, Q, h, l, a, hl => by
    cases x with
    | pclr => rw [fol_pclr] at h; exact fol_after h hl
    | rd =>
      cases P with
      | read k =>
        cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es =>
          cases e with
          | read y =>
            obtain ⟨h1, h2⟩ := fol_after (h y) hl
            exact ⟨by simp [kindOf, atomKinds, h1], h2⟩
          | _ => simp [VerifierProgram.after] at hl
      | fail => cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es => cases e <;> simp [VerifierProgram.after] at hl
      | _ => exact h.elim
    | sm =>
      cases P with
      | sample k =>
        cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es =>
          cases e with
          | sample y =>
            obtain ⟨h1, h2⟩ := fol_after (h y) hl
            exact ⟨by simp [kindOf, atomKinds, h1], h2⟩
          | _ => simp [VerifierProgram.after] at hl
      | fail => cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es => cases e <;> simp [VerifierProgram.after] at hl
      | _ => exact h.elim
    | ps hh n =>
      cases P with
      | sample k =>
        cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es =>
          cases e with
          | sample y =>
            obtain ⟨h1, h2⟩ := fol_after (h y) hl
            exact ⟨by simp [kindOf, atomKinds, h1], h2⟩
          | _ => simp [VerifierProgram.after] at hl
      | fail => cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es => cases e <;> simp [VerifierProgram.after] at hl
      | _ => exact h.elim
    | cap c r =>
      cases P with
      | commit ht w k =>
        cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es =>
          cases e with
          | commit ht' w' word =>
            simp only [VerifierProgram.after] at hl
            split at hl
            · obtain ⟨h1, h2⟩ := fol_after h.2.2 hl
              exact ⟨by simp [kindOf, atomKinds, h1], h2⟩
            · simp at hl
          | _ => simp [VerifierProgram.after] at hl
      | fail => cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es => cases e <;> simp [VerifierProgram.after] at hl
      | _ => exact h.elim
    | op r =>
      cases P with
      | query i ps k =>
        cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es =>
          cases e with
          | query rows =>
            obtain ⟨h1, h2⟩ := fol_after (h.2.2 rows) hl
            exact ⟨by simp [kindOf, atomKinds, h1], h2⟩
          | _ => simp [VerifierProgram.after] at hl
      | fail => cases l with
        | nil => simp [VerifierProgram.after] at hl
        | cons e es => cases e <;> simp [VerifierProgram.after] at hl
      | _ => exact h.elim

theorem atomKinds_append (as bs : List Atom) : atomKinds (as ++ bs) = atomKinds as ++ atomKinds bs := by
  induction as with
  | nil => rfl
  | cons x as ih => cases x <;> simp [atomKinds, ih]

theorem atomKinds_replicate_rd (m : ℕ) : atomKinds (List.replicate m .rd) = List.replicate m .read := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, atomKinds, ih]

/-- **On items without positions, the atoms' kinds are the items'.** -/
theorem atomKinds_atomsOf (p : Params) :
    ∀ its : List Item, (∀ it ∈ its, ∀ r, it ≠ .positions r) → atomKinds (atomsOf p its) = itemKinds its
  | [], _ => rfl
  | it :: its, h => by
    have ih := atomKinds_atomsOf p its fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    rw [atomsOf_cons, atomKinds_append, ih]
    cases it with
    | read m => simp [itemAtoms, itemKinds, atomKinds_replicate_rd]
    | cap c r => rfl
    | sample => rfl
    | positions r => exact absurd rfl (h _ List.mem_cons_self r)
    | opening r => rfl

end After

end Lvm.VEq
