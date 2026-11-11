-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean` (formal rev 40f877dc) as `LvmWhirSpec` for
-- lvm (WP-7). Changed for the unique-decoding regime and lvm's openings: `whirSpec`/`stackedSpec` become
-- `whirUdSpec`/`stackedUdSpec` for `verifyWhirUd`/`verifyStackedUd` (no out-of-domain step, no proof of work, the
-- levels given by the configuration, positions `per` per challenge, the root `c₀` of `n₀` commitments);
-- `LadderArith`/`levelEps` become `LadderArithUd`/`levelEpsUd` (no `eOod`, `eQueryUd`, no `2^-17` discount, the
-- positions' width, the next code's list bound `≤ 1`); `card_batch_bad_le` reads the root's word. `anyT`, the
-- batching lemmas and the proof structure are leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.Spec

  The round-by-round soundness of lvm's WHIR opening (unique decoding) as a specification of the
  verifier program: `whirUdSpec` for `verifyWhirUd` from "every candidate violates the claim", and
  `stackedUdSpec` for `verifyStackedUd` from "every candidate violates one of the pooled claims",
  with the explicit escape bound `whirEpsUd`.
-/

import LvmWhirProg
import LvmWhirStart

/-!
# The specification of the WHIR opening (unique decoding)

For an opening `cfg : UdConfig` (stack variables `μ`, levels `ℓ_i, R_i, t_i`, `per` positions per
challenge, root `c₀` of the `n₀` commitments present at its start) and a code `codes i` per level
(`LevelCode`: `κ_i`, `R_i`, threshold `A_i`, list bound `L_i`, MCA count `E_i`; lvm:
`LevelCode.ud`, `L_i = 1`):

* `LadderArithUd`: the arithmetic of the levels (`κ_i` is the number of variables left after
  level `i`'s folds, `R_i` the level's rate), the query groups' escapes below `1` (the hypothesis
  of `Spec.ofNoMove`), the positions' width `per·(κ_i + R_i) ≤ 192`, and `L_{i+1} ≤ 1` at every
  level with a next one (the query step's one candidate);
* `levelEpsUd codes i levels`, `whirEpsUd codes levels`: the largest group escape, **the `εmax` of
  the opening**:

  `max_i max( (2·L_i + 2^(ℓ_i−1)·E_i)/|E|,  ((A_i − 1)/n_i)^{t_i} + t_i·L_{i+1}/|E| )`
  over the levels with a next level, and for the final level
  `max( (2·L + 2^(ℓ−1)·E)/|E|, ((A − 1)/n)^t + t/|E|, 2/|E| )`, `n_i = 2^(κ_i+R_i)`;
* `whirUdSpec`: **`verifyWhirUd cfg t w` from `WhirPreUd`**: the history has the `n₀` commitments,
  the root `c₀` is shaped as level 0, and every candidate of its word at the level-0 threshold
  violates `(w, t)`, for `w` multiaffine. Post `False`: the program does not return in doom.
  Lead `0` (it starts with a round polynomial).
* `stackedUdSpec`: **`verifyStackedUd cfg claims` from "every candidate violates one of the
  claims"**, with the batching challenge's escape `eBatch J P₀ = (J − 1)·L₀/|E|` as lead.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

section

/-! ## The levels' arithmetic and escapes -/

section Ladder

variable (μ per : ℕ) (codes : ℕ → LevelCode)

/-- The arithmetic of the levels, the query groups' escapes below `1`, the positions' width and
the next codes' list bound. -/
def LadderArithUd : ℕ → ℕ → List Whir.Level → Prop
  | _, _, [] => True
  | i, pre, [level] => (codes i).κ + pre + level.fold = μ ∧ (codes i).R = level.logInvRate ∧
      eQueryFinal (codes i) level.queries < 1 ∧ per * ((codes i).κ + (codes i).R) ≤ 192
  | i, pre, level :: next :: rest => (codes i).κ + pre + level.fold = μ ∧
      (codes i).R = level.logInvRate ∧ eQueryUd (codes i) (codes (i + 1)) level.queries < 1 ∧
      per * ((codes i).κ + (codes i).R) ≤ 192 ∧ (codes (i + 1)).listMax ≤ 1 ∧
      LadderArithUd (i + 1) (pre + level.fold) (next :: rest)

end Ladder

section Eps

variable (codes : ℕ → LevelCode)

/-- **The largest group escape** of the levels from level `i`. -/
noncomputable def levelEpsUd : ℕ → List Whir.Level → ENNReal
  | _, [] => 0
  | i, [level] => max (eFold (codes i) level.fold)
      (max (eQueryFinal (codes i) level.queries) eTail)
  | i, level :: next :: rest => max (max (eFold (codes i) level.fold)
      (eQueryUd (codes i) (codes (i + 1)) level.queries)) (levelEpsUd (i + 1) (next :: rest))

/-- **The `εmax` of the WHIR opening.** -/
noncomputable def whirEpsUd (levels : List Whir.Level) : ENNReal := levelEpsUd codes 0 levels

end Eps

/-- The doom at the start of the levels from `i`. -/
def LevelPreL (μ : ℕ) (codes : ℕ → LevelCode) (ℓ₀ : ℕ) (w : List E → E) :
    ℕ → ℕ → List Whir.Level → WhirStateT → List (ℕ × ℕ × Word) → Prop
  | _, _, [], _, _ => True
  | i, pre, level :: _, s, cs => LevelPre μ ℓ₀ w i (codes i) level.fold pre s cs

/-! ## A return in doom is impossible -/

/-- A specification whose program never returns in doom admits any follower's allowance. -/
def anyT {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop} {εmax L T : ENNReal}
    (S : Spec p Pre (fun _ _ ↦ False) εmax L T) (T' : ENNReal) :
    Spec p Pre (fun _ _ ↦ False) εmax L T' :=
  { S with retDoom := fun hl ha hD ↦ (S.post hl ha hD).elim }

/-! ## The levels -/

variable {μ ℓ₀ per c₀ n₀ : ℕ} {dir : Bool} {w : List E → E} {codes : ℕ → LevelCode} {εmax : ENNReal}

/-- **The levels' specification.** -/
noncomputable def levelsSpec (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (hc : c₀ < n₀)
    (hper : 1 ≤ per) :
    (levels : List Whir.Level) → (i pre : ℕ) → LadderArithUd μ per codes i pre levels →
      levelEpsUd codes i levels ≤ εmax → (s : WhirStateT) →
      Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ dir w i levels s)
        (fun h ↦ LevelPreL μ codes ℓ₀ w i pre levels s (viewC c₀ n₀ (commits h)))
        (fun _ _ ↦ False) εmax εmax 0
  | [], i, pre, _, _, s => (Spec.fail (Pre := fun h ↦ LevelPreL μ codes ℓ₀ w i pre [] s
        (viewC c₀ n₀ (commits h))) (Post := fun _ _ ↦ False)).mono (fun _ h ↦ h)
        (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | [level], i, pre, hA, hε, s =>
    finSpec ⟨hw, hℓ₀, hA.1, hA.2.1, hc, hper, hA.2.2.2⟩ ((le_max_left _ _).trans hε) hA.2.2.1
      ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hε)) s
  | level :: next :: rest, i, pre, hA, hε, s =>
    midSpec ⟨hw, hℓ₀, hA.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.1, hA.2.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.2.1, hc, hper, hA.2.2.2.1, hA.2.2.2.2.1⟩
      ((le_max_left _ _).trans ((le_max_left _ _).trans hε)) hA.2.2.1
      ((le_max_right _ _).trans ((le_max_left _ _).trans hε))
      (fun s' ↦ levelsSpec hw hℓ₀ hc hper (next :: rest) (i + 1) (pre + level.fold)
        hA.2.2.2.2.2 ((le_max_right _ _).trans hε) s') s

/-! ## The opening -/

/-- `verifyWhirUd` on a configuration with levels: the first round polynomial, then the levels. -/
theorem verifyWhirUd_eq {cfg : UdConfig} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hc : cfg.levels = level :: rest) :
    verifyWhirUd cfg t w = (sumcheckRoundPoly 3 t none).bind fun quad ↦
      whirLevelsUd cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ cfg.direct w 0 (level :: rest)
        ⟨t, quad, [], []⟩ := by
  rw [verifyWhirUd, hc]
  rfl

/-- **The specification of the unique-decoding WHIR opening.** From `WhirPreUd` (the history has the
`n₀` commitments the opening starts with, its root `c₀` is shaped as level `0`, and every
candidate of the root's word violates `(w, t)`), the opening's groups escape with probability at
most `εmax ≥ whirEpsUd codes cfg.levels` each, and it never returns in doom. -/
noncomputable def whirUdSpec {cfg : UdConfig} {t : E} {level : Whir.Level}
    {rest : List Whir.Level} (hc : cfg.levels = level :: rest) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits) (hcn : cfg.c₀ < cfg.n₀)
    (hper : 1 ≤ cfg.per) (hw : IsMultiaffine cfg.μ w)
    (hA : LadderArithUd cfg.μ cfg.per codes 0 0 (level :: rest))
    (hε : whirEpsUd codes (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyWhirUd cfg t w) (fun h ↦ WhirPreUd cfg (codes 0) w t (commits h))
      (fun _ _ ↦ False) εmax 0 T :=
  anyT (Spec.congr (p' := verifyWhirUd cfg t w) (by rw [verifyWhirUd_eq hc, hℓ]; rfl)
    ((roundPolyInv (WhirPreUd cfg (codes 0) w t) t (T := εmax) le_rfl).bind' fun quad ↦
      (levelsSpec (ℓ₀ := laneBits) hw hμ hcn hper (level :: rest) 0 0 hA hε
          ⟨t, quad, [], []⟩).mono
        (fun h hp ↦ by
          show LevelPre cfg.μ laneBits w 0 (codes 0) level.fold 0 _ _
          rw [hℓ]
          exact levelPre_zero (codes 0) hκ₀ rfl hμ w t quad _ (whirPre_of_ud hp.2) hp.1)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)) T

/-! ## The stacked opening -/

/-- The batching challenge's escape: `(J − 1)·L₀ / |E|`. -/
noncomputable def eBatch (J : ℕ) (P₀ : LevelCode) : ENNReal :=
  (((J - 1) * P₀.listMax : ℕ) : ENNReal) / Fintype.card E

/-- The opening's pooled relation: the history has the `n₀` commitments, the root has the right
shape and every candidate of its word violates at least one of the claims. -/
def StackedPreUd (cfg : UdConfig) (P₀ : LevelCode) (claims : List StackClaim)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  cfg.c₀ < cfg.n₀ ∧ cs.length = cfg.n₀ ∧
    (∃ W, cs[cfg.c₀]? = some (P₀.κ + P₀.R, 2 ^ laneBits, W) ∧ WellShaped (2 ^ laneBits) W) ∧
    ∀ q ∈ Candidates cfg.μ P₀.R P₀.thr (wordOf cs cfg.c₀), ∃ c ∈ claims,
      ¬ StackClaim.Holds cfg.μ c q

/-- `dot (powersFrom acc ρ J) (l.map f)` is `Σ_t acc ρ^t f(l_t)`. -/
theorem dot_powersFrom_map {α : Type*} (ρ : E) (f : α → E) :
    ∀ (l : List α) (acc : E), dot (powersFrom acc ρ l.length) (l.map f) =
      ∑ k : Fin l.length, acc * ρ ^ (k : ℕ) * f l[k]
  | [], acc => by simp [dot, powersFrom]
  | x :: l, acc => by
    have ih := dot_powersFrom_map ρ f l (acc * ρ)
    rw [dot, foldl_add_eq, zero_add] at ih ⊢
    simp only [List.length_cons, powersFrom, List.map_cons, List.zipWith_cons_cons,
      List.sum_cons, ih, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    exact congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun k _ ↦ by
      simp only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ]; ring)

/-- `dot (powers ρ J) (l.map f)` is `Σ_t ρ^t f(l_t)`. -/
theorem dot_powers_map {α : Type*} (ρ : E) (f : α → E) (l : List α) :
    dot (powers ρ l.length) (l.map f) = ∑ k : Fin l.length, ρ ^ (k : ℕ) * f l[k] := by
  rw [powers, dot_powersFrom_map]
  simp

/-- The batched weight of multiaffine claims is multiaffine. -/
theorem isMultiaffine_batched {μ : ℕ} (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) (ρ : E) :
    IsMultiaffine μ fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point) := by
  simp only [dot_powers_map]
  exact IsMultiaffine.sum _ _ fun k _ ↦ (hcl _ (List.getElem_mem _)).const_mul _

/-- The batched claim holds exactly when the discrepancies' power combination vanishes. -/
theorem batch_iff {J N : ℕ} (A : Fin J → Fin N → E) (g : Fin N → E) (c : Fin J → E) (ρ : E) :
    (∑ j : Fin N, (∑ k : Fin J, ρ ^ (k : ℕ) * A k j) * g j = ∑ k : Fin J, ρ ^ (k : ℕ) * c k) ↔
      ∑ k : Fin J, ((∑ j : Fin N, A k j * g j) - c k) * ρ ^ (k : ℕ) = 0 := by
  have h : ∑ k : Fin J, ((∑ j : Fin N, A k j * g j) - c k) * ρ ^ (k : ℕ) =
      (∑ j : Fin N, (∑ k : Fin J, ρ ^ (k : ℕ) * A k j) * g j) -
        ∑ k : Fin J, ρ ^ (k : ℕ) * c k := by
    calc ∑ k : Fin J, ((∑ j : Fin N, A k j * g j) - c k) * ρ ^ (k : ℕ)
        = ∑ k : Fin J, (∑ j : Fin N, A k j * g j) * ρ ^ (k : ℕ) -
            ∑ k : Fin J, c k * ρ ^ (k : ℕ) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ = _ := by
          refine congrArg₂ (· - ·) ?_ (Finset.sum_congr rfl fun k _ ↦ by ring)
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  rw [h, sub_eq_zero]

open Classical in
/-- **The batching step**: at most `(J − 1)·listMax₀` challenges `ρ` let a candidate satisfy the
batched claim when every candidate violates one of the claims. -/
theorem card_batch_bad_le {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (hμ : laneBits ≤ μ) (claims : List StackClaim) (W₀ : Word)
    (hviol : ∀ q ∈ Candidates μ R P₀.thr W₀, ∃ c ∈ claims, ¬ StackClaim.Holds μ c q) :
    (univ.filter fun ρ : E ↦ ∃ q ∈ Candidates μ R P₀.thr W₀,
        StackClaim.Holds μ (fun point ↦ dot (powers ρ claims.length)
          (claims.map fun c ↦ c.1 point), dot (powers ρ claims.length) (claims.map (·.2))) q).card ≤
      P₀.listMax * (claims.length - 1) := by
  rcases P₀ with ⟨κ, R', h64, hκ1, hR1, thr, lM, mM, facts⟩
  simp only at hκ hR
  subst hκ hR
  set P₀ : LevelCode := ⟨μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩
  set L := iList (rsCode (domain (μ - laneBits) R' h64) (2 ^ (μ - laneBits))) P₀.thr
    (laneWord μ R' W₀)
  -- The discrepancy of a candidate.
  let d : Column μ → Fin claims.length → E := fun q k ↦
    (∑ j : Fin (2 ^ μ), claims[k].1 (boolPoint μ j) * ofK (q.values.getD j 0)) - claims[k].2
  have hhold : ∀ ρ q, StackClaim.Holds μ (fun point ↦ dot (powers ρ claims.length)
      (claims.map fun c ↦ c.1 point), dot (powers ρ claims.length) (claims.map (·.2))) q ↔
      ∑ k : Fin claims.length, d q k * ρ ^ (k : ℕ) = 0 := by
    intro ρ q
    simp only [StackClaim.Holds, dot_powers_map]
    exact batch_iff (fun k j ↦ claims[k].1 (boolPoint μ j)) (fun j ↦ ofK (q.values.getD j 0))
      (fun k ↦ claims[k].2) ρ
  refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans ((card_filter_exists_le L (fun
      (V : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R')) → E) (ρ : E) ↦
      ∃ q ∈ Candidates μ R' P₀.thr W₀, encStack μ R' q = V ∧
        ∑ k : Fin claims.length, d q k * ρ ^ (k : ℕ) = 0) (N := claims.length - 1)
      fun V _ ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    obtain ⟨q, hq, hh⟩ := hρ
    exact ⟨encStack μ R' q, mem_iList_of_candidate h64 hq, q, hq, rfl, (hhold ρ q).mp hh⟩
  · by_cases hex : ∃ q ∈ Candidates μ R' P₀.thr W₀, encStack μ R' q = V
    · obtain ⟨q₀, hq₀, rfl⟩ := hex
      obtain ⟨c, hc, hnot⟩ := hviol q₀ hq₀
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
      have hd : ∃ k, d q₀ k ≠ 0 := ⟨⟨k, hk⟩, by
        simp only [d, sub_ne_zero]
        exact hnot⟩
      refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans (card_powerBatch_eq_zero_le (d q₀) hd)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      obtain ⟨q, -, hqV, hz⟩ := hρ
      rwa [encStack_injective hμ h64 hqV] at hz
    · refine le_trans (Finset.card_le_card (t := ∅) fun ρ hρ ↦ ?_) (by simp)
      rw [Finset.mem_filter] at hρ
      obtain ⟨q, hq, hqV, -⟩ := hρ.2
      exact absurd ⟨q, hq, hqV⟩ hex
  · exact Nat.mul_le_mul_right _ (P₀.card_iList_le _)

/-- `verifyStackedUd`: the batching challenge, then the opening. -/
theorem verifyStackedUd_eq (cfg : UdConfig) (claims : List StackClaim) :
    verifyStackedUd cfg claims = VerifierProgram.sampleChallenge.bind fun ρ ↦
      verifyWhirUd cfg (dot (powers ρ claims.length) (claims.map (·.2)))
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point)) := rfl

open Classical in
/-- **The specification of the stacked opening** (unique decoding). From `StackedPreUd` (every
candidate of the root violates one of the `J` claims), the batching challenge escapes with
probability at most `eBatch J P₀ = (J − 1)·L₀/|E|` and the opening (`whirUdSpec`) follows. -/
noncomputable def stackedUdSpec {cfg : UdConfig} {level : Whir.Level} {rest : List Whir.Level}
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfg.μ c.1)
    (hc : cfg.levels = level :: rest) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits) (hcn : cfg.c₀ < cfg.n₀)
    (hper : 1 ≤ cfg.per) (hA : LadderArithUd cfg.μ cfg.per codes 0 0 (level :: rest))
    (hε : whirEpsUd codes (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyStackedUd cfg claims)
      (fun h ↦ StackedPreUd cfg (codes 0) claims (commits h)) (fun _ _ ↦ False) εmax
      (eBatch claims.length (codes 0)) T :=
  by
  have S0 : Spec VerifierProgram.sampleChallenge (fun h ↦ StackedPreUd cfg (codes 0) claims
      (commits h))
      (fun ρ h ↦ WhirPreUd cfg (codes 0)
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
        (dot (powers ρ claims.length) (claims.map (·.2))) (commits h)) εmax
      (eBatch claims.length (codes 0) + 0) 0 :=
    Spec.sampleE (eBatch claims.length (codes 0)) fun h₀ hp ↦ by
      have hb := card_batch_bad_le (codes 0) hκ₀ rfl hμ claims _ hp.2.2.2
      rw [eBatch, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((Finset.card_le_card fun ρ hρ ↦ ?_).trans
        (hb.trans (le_of_eq (mul_comm _ _)))))
      rw [Finset.mem_filter] at hρ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hρ2 := hρ.2
      simp only [commits_sample] at hρ2
      by_contra hno
      exact hρ2 ⟨hp.1, hp.2.1, hp.2.2.1, fun q hq hh ↦ hno ⟨q, hq, hh⟩⟩
  have F0 := fun ρ : E ↦
    whirUdSpec (w := fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
      (t := dot (powers ρ claims.length) (claims.map (·.2))) hc hℓ hμ hκ₀ hcn hper
      (isMultiaffine_batched claims hcl ρ) hA hε 0
  have S1 := Spec.bind S0 F0
  exact anyT (Spec.congr (p' := verifyStackedUd cfg claims)
    (verifyStackedUd_eq cfg claims).symm
    (S1.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl)) T

end
end LeanVM.Protocol.Whir.Sound
