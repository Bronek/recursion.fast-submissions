-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/LJPin.lean` @ 1b74a2a2 (archive/pcs/S1P) (Flock LJ1/LJ2, on the
-- longfellow port `LvmJB*`, Apache License 2.0, see `LICENSE-longfellow`). Changed: imports `JB*`/`LJ*`
-- renamed `LvmJB*`/`LvmLJ*`; nothing else.
-- LJ2: SJ §5.1 (I2), the pinned element and the K-only good-event potential `μ_G` at one Johnson level.
-- Level-generic: the level's reads from a transcript prefix are a `JView`; the entry's instance supplies the
-- view (`wordK`, `oodPt`, `oodY`, `sAt`, the round polynomials) and the stability facts (`Same`-style).
import LvmLJDefs
import LvmLJOod
import LvmLJInterleave
import LvmLJFold

open Polynomial Finset JBAgreement

namespace LJ

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Part A: the list `Λ_i`, the OOD functional `ψ_i`, the pinned element `V*_i` (SJ §2.1) -/

/-- A row is a codeword of `RS[K, dom, k]`. -/
def IsCW (dom : ι → K) (k : ℕ) (v : ι → K) : Prop :=
  ∃ p : K[X], p.natDegree < k ∧ ∀ x, v x = p.eval (dom x)

open Classical in
/-- **`Λ_i`**: the codeword tuples jointly `e`-close to the committed word `U` (column distance). -/
noncomputable def lamL {m : ℕ} (dom : ι → K) (k e : ℕ) (U : Fin m → ι → K) : Finset (Fin m → ι → K) :=
  univ.filter fun V => (∀ r, IsCW dom k (V r)) ∧ (colDisagree U V).card ≤ e

/-- **`ψ_i`**: the OOD functional `V ↦ P_{M(V)}(ζ) = Σ_j M(V)_j · B_j(ζ)` for a message map `msg`
(the entry's `packMsg`) and a basis `B` (the novel basis, `gWK` at `ζ`). -/
def psiL {m N : ℕ} (msg : (Fin m → ι → K) → Fin N → K) (B : Fin N → K[X]) (ζ : K)
    (V : Fin m → ι → K) : K :=
  ∑ j, msg V j * (B j).eval ζ

section Pin
variable {α : Type*} [DecidableEq α]

/-- **`Λ^ŷ_i`**: the OOD-consistent list elements. -/
def pinS (lam : Finset α) (ψ : α → K) (y : K) : Finset α := lam.filter fun V => ψ V = y

/-- **`far^J_i`**: no list element is OOD-consistent. -/
def farJ (lam : Finset α) (ψ : α → K) (y : K) : Prop := pinS lam ψ y = ∅

open Classical in
/-- **The pinned element `V*_i`** (SJ's `decodeLJ`): the OOD-consistent element; `0` when `far^J_i`. -/
noncomputable def pinV [Zero α] (lam : Finset α) (ψ : α → K) (y : K) : α :=
  if h : (pinS lam ψ y).Nonempty then h.choose else 0

theorem mem_pinS {lam : Finset α} {ψ : α → K} {y : K} {V : α} :
    V ∈ pinS lam ψ y ↔ V ∈ lam ∧ ψ V = y := mem_filter

/-- **Uniqueness under separation**: `Sep_i ⇒ |Λ^ŷ_i| ≤ 1`. -/
theorem pinS_card_le_one {lam : Finset α} {ψ : α → K} (hS : Set.InjOn ψ ↑lam) (y : K) :
    (pinS lam ψ y).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [mem_pinS] at ha hb
  exact hS ha.1 hb.1 (ha.2.trans hb.2.symm)

theorem pinV_mem [Zero α] {lam : Finset α} {ψ : α → K} {y : K} (h : ¬ farJ lam ψ y) :
    pinV lam ψ y ∈ pinS lam ψ y := by
  have hne : (pinS lam ψ y).Nonempty := nonempty_iff_ne_empty.2 h
  simp only [pinV, hne, ↓reduceDIte]
  exact hne.choose_spec

/-- The pinned element is a list element with `ψ_i(V*_i) = ŷ_i` (SJ's `decodeL_spec` for `V*_i`). -/
theorem pinV_spec [Zero α] {lam : Finset α} {ψ : α → K} {y : K} (h : ¬ farJ lam ψ y) :
    pinV lam ψ y ∈ lam ∧ ψ (pinV lam ψ y) = y :=
  mem_pinS.1 (pinV_mem h)

/-- **Every OOD-consistent element is the pinned one** under `Sep_i`. -/
theorem eq_pinV [Zero α] {lam : Finset α} {ψ : α → K} {y : K} (hS : Set.InjOn ψ ↑lam) {V : α}
    (hV : V ∈ pinS lam ψ y) : V = pinV lam ψ y := by
  have hnf : ¬ farJ lam ψ y := fun h => by rw [farJ] at h; rw [h] at hV; exact absurd hV (by simp)
  exact Finset.card_le_one.1 (pinS_card_le_one hS y) _ hV _ (pinV_mem hnf)

/-- Under `Sep_i`, `Λ^ŷ_i` is `{V*_i}` or empty. -/
theorem pinS_eq [Zero α] {lam : Finset α} {ψ : α → K} {y : K} (hS : Set.InjOn ψ ↑lam) :
    pinS lam ψ y = ∅ ∨ pinS lam ψ y = {pinV lam ψ y} := by
  by_cases h : farJ lam ψ y
  · exact Or.inl h
  · refine Or.inr (Finset.eq_singleton_iff_unique_mem.2 ⟨pinV_mem h, fun V hV => eq_pinV hS hV⟩)

/-- A non-pinned list element has a non-zero OOD defect `d_0(V) = ŷ_i − ψ_i(V)`. -/
theorem d0_ne {lam : Finset α} {ψ : α → K} {y : K} {V : α} (hV : V ∈ lam) (hn : V ∉ pinS lam ψ y) :
    y - ψ V ≠ 0 := fun h => hn (mem_pinS.2 ⟨hV, (sub_eq_zero.1 h).symm⟩)

/-! ## Part B: the charges at `ζ` (separation) and at `γ` (non-pinned elements) -/

/-- **`NoSw_i`**: no non-pinned element's batched claim is true. The claim is `c_i = cb + γ·ŷ`, the
truth for `V` is `Tr_i(V) = tb V + γ·ψ(V)` (SJ §1.2: `cb = c1 + Σ_q eq(κ_c,q)·y_q`,
`tb V = ⟨foldW, M V⟩ + Σ_q eq(κ_c,q)·Enc(M V)(p_q)`). -/
def NoSw (lam : Finset α) (ψ : α → K) (y cb : K) (tb : α → K) (γ : K) : Prop :=
  ∀ V ∈ lam, V ∉ pinS lam ψ y → cb + γ * y ≠ tb V + γ * ψ V

/-- At the pinned element the `γ` term cancels: `D_γ` at `V*` is the `κ_c` doom (no `μ_D` escape at `γ`). -/
theorem pinned_gamma_cancel {lam : Finset α} {ψ : α → K} {y cb : K} {tb : α → K} (γ : K) {V : α}
    (hV : V ∈ pinS lam ψ y) : (cb + γ * y) - (tb V + γ * ψ V) = cb - tb V := by
  rw [(mem_pinS.1 hV).2]; ring

open Classical in
/-- **The `γ` charge** (SJ `gamma_count`): at most `|Λ_i \ Λ^ŷ_i|` values of `γ` break `NoSw_i`. -/
theorem gamma_count (lam : Finset α) (ψ : α → K) (y cb : K) (tb : α → K) :
    (univ.filter fun γ : K => ¬ NoSw lam ψ y cb tb γ).card ≤ (lam \ pinS lam ψ y).card := by
  refine le_trans (card_le_card ?_) (gamma_bad (lam \ pinS lam ψ y) (fun V => cb - tb V)
    (fun V => y - ψ V) fun V hV => d0_ne (mem_sdiff.1 hV).1 (mem_sdiff.1 hV).2)
  intro γ hγ
  simp only [NoSw, mem_filter, mem_univ, true_and, not_forall, not_not, exists_prop] at hγ ⊢
  obtain ⟨V, hV, hn, h⟩ := hγ
  exact ⟨V, mem_sdiff.2 ⟨hV, hn⟩, by linear_combination h⟩

end Pin

/-- **The separation charge** (SJ `sep_count`): at most `C(L,2)·(D − 1)` values of `ζ` leave `ψ_ζ`
non-injective on the list, for a list of size `≤ L`, an injective message map, and a linearly
independent basis of degree `< D` (`ood_sep`). -/
theorem sep_count {m N D Lb : ℕ} (dom : ι → K) (k e : ℕ) (U : Fin m → ι → K)
    (hL : (lamL dom k e U).card ≤ Lb) (msg : (Fin m → ι → K) → Fin N → K)
    (hmsg : Set.InjOn msg ↑(lamL dom k e U)) (B : Fin N → K[X]) (hB : LinearIndependent K B)
    (hdeg : ∀ j, (B j).natDegree < D) :
    (univ.filter fun ζ : K => ¬ Set.InjOn (psiL msg B ζ) ↑(lamL dom k e U)).card ≤
      Lb.choose 2 * (D - 1) := by
  have hS : ((lamL dom k e U).image msg).card ≤ Lb := card_image_le.trans hL
  refine le_trans (card_le_card ?_) (ood_sep _ hS B hB hdeg)
  intro ζ hζ
  simp only [mem_filter, mem_univ, true_and, Set.InjOn, not_forall, exists_prop, mem_coe] at hζ ⊢
  obtain ⟨V, hV, V', hV', hψ, hne⟩ := hζ
  exact ⟨msg V, mem_image_of_mem _ hV, msg V', mem_image_of_mem _ hV',
    fun h => hne (hmsg (mem_coe.2 hV) (mem_coe.2 hV') h), hψ⟩

/-! ## Part C: the P1.i rounds: MCA explanation (L1, L2) and the non-pinned sumcheck escapes -/

/-- **`Expl_i(l)`'s good event**: no fold challenge in `ss` (in order) lies in the JB bad set of its
round's interleaved line `(evens, odds − evens)` of the fold so far (`pf(i, l)`). -/
def NoMCA (dom : ι → K) (k e : ℕ) : List K → (n : ℕ) → (Fin (2 ^ n) → ι → K) → Prop
  | [], _, _ => True
  | _ :: _, 0, _ => True
  | s :: ss, n + 1, W =>
      ¬ iHasUnexplainedProximate dom (evens W) (fun r x => odds W r x - evens W r x) k e s ∧
        NoMCA dom k e ss n (foldRows s W)

/-- The word folded by all of `ss` down to one row (`foldN`); row `0` once no rows are left to fold. -/
def foldAll : List K → (n : ℕ) → (Fin (2 ^ n) → ι → K) → ι → K
  | [], n, W => W ⟨0, Nat.two_pow_pos n⟩
  | _ :: _, 0, W => W ⟨0, Nat.two_pow_pos 0⟩
  | s :: ss, n + 1, W => foldAll ss n (foldRows s W)

/-- The same fold on polynomial rows. -/
noncomputable def foldAllP : List K → (n : ℕ) → (Fin (2 ^ n) → K[X]) → K[X]
  | [], n, Q => Q ⟨0, Nat.two_pow_pos n⟩
  | _ :: _, 0, Q => Q ⟨0, Nat.two_pow_pos 0⟩
  | s :: ss, n + 1, Q => foldAllP ss n (foldPolys s Q)

/-- **`expl_target`** (SJ §5.1 L2's corollary, generic): off the MCA bad sets of every round, an
`e`-close codeword `p` of the full fold is the fold of a codeword tuple `V` whose disagreement with
the committed word lies inside the fold's disagreement with `p` (`consSet ⊆ jointAgree`). The word
`W` explained by `U` through `fold` is the induction's carrier (`explBy_refl` starts it). -/
theorem expl_target_gen {a : ℕ} (dom : ι → K) (U : Fin a → ι → K) (k e : ℕ) :
    ∀ (ss : List K) (n : ℕ) (W : Fin (2 ^ n) → ι → K) (fold : (Fin a → K[X]) → (Fin (2 ^ n) → K[X])),
      ExplBy dom U W fold k e → NoMCA dom k e ss n W → ss.length = n →
      ∀ p : K[X], p.natDegree < k →
        (univ.filter fun x => foldAll ss n W x ≠ p.eval (dom x)).card ≤ e →
        ∃ V : Fin a → K[X], (∀ r, (V r).natDegree < k) ∧ foldAllP ss n (fold V) = p ∧
          colDisagree U (evalRows dom V) ⊆ univ.filter fun x => foldAll ss n W x ≠ p.eval (dom x)
  | [], n, W, fold, hE, _, hl, p, hp, hc => by
      obtain rfl : n = 0 := by simpa using hl.symm
      have hcol : colDisagree W (evalRows dom fun _ => p) =
          univ.filter fun x => foldAll [] 0 W x ≠ p.eval (dom x) := by
        ext x
        rw [mem_colDisagree, mem_filter]
        simp only [foldAll, evalRows]
        simp only [mem_univ, true_and]
        constructor
        · rintro ⟨r, hr⟩
          have : r = ⟨0, Nat.two_pow_pos 0⟩ := Fin.ext (by have := r.isLt; simp at this; omega)
          subst this; exact hr
        · intro h; exact ⟨_, h⟩
      obtain ⟨V, hV, hf, hsub⟩ := hE (fun _ => p) (fun _ => hp) (hcol ▸ hc)
      exact ⟨V, hV, by simp only [foldAllP, hf], hcol ▸ hsub⟩
  | _ :: _, 0, _, _, _, _, hl, _, _, _ => by simp at hl
  | s :: ss, n + 1, W, fold, hE, hN, hl, p, hp, hc => by
      obtain ⟨hz, hN'⟩ := hN
      exact expl_target_gen dom U k e ss n (foldRows s W) (fun V => foldPolys s (fold V))
        (explBy_step dom U W fold k e hE s hz) hN' (by simpa using hl) p hp hc

/-- **`expl_target`** from the committed word itself (`explBy_refl`). -/
theorem expl_target {n : ℕ} (dom : ι → K) (U : Fin (2 ^ n) → ι → K) (k e : ℕ) (ss : List K)
    (hN : NoMCA dom k e ss n U) (hl : ss.length = n) (p : K[X]) (hp : p.natDegree < k)
    (hc : (univ.filter fun x => foldAll ss n U x ≠ p.eval (dom x)).card ≤ e) :
    ∃ V : Fin (2 ^ n) → K[X], (∀ r, (V r).natDegree < k) ∧ foldAllP ss n V = p ∧
      colDisagree U (evalRows dom V) ⊆ univ.filter fun x => foldAll ss n U x ≠ p.eval (dom x) :=
  expl_target_gen dom U k e ss n U id (explBy_refl dom U k e) hN hl p hp hc

section MCA
variable (dom : ι → K) (hdom : Function.Injective dom) (k e : ℕ) (η : ℝ)
    (hk2 : 2 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4) (hηn : 1 ≤ η * (Fintype.card ι))
    (ht4 : 4 * η * (Fintype.card ι) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hJ : ((k - 1 : ℕ) : ℝ) * (Fintype.card ι)
        ≤ (((Fintype.card ι - e : ℕ) : ℝ) - 4 * η * (Fintype.card ι)) ^ 2)
include hdom hk2 hη hη4 hηn ht4 hJ

open Classical in
theorem johnsonThreshold_pos : 0 < johnsonThreshold k (Fintype.card ι) e η :=
  lt_of_le_of_lt (Nat.cast_nonneg _) (strong_mutual_johnson_interleaved (m := 0) dom hdom
    (fun _ _ => 0) (fun _ _ => 0) k e η hk2 hη hη4 hηn ht4 hJ)

open Classical in
/-- **The MCA charge of one P1 round** (L1 + L2): whatever challenges `ss` came before, fewer than
`T = johnsonThreshold` values of the next challenge break `NoMCA`. -/
theorem mca_round_card : ∀ (ss : List K) (n : ℕ) (W : Fin (2 ^ n) → ι → K),
    ((univ.filter fun s : K => NoMCA dom k e ss n W ∧ ¬ NoMCA dom k e (ss ++ [s]) n W).card : ℝ) <
      johnsonThreshold k (Fintype.card ι) e η
  | [], 0, W => by
      have : (univ.filter fun s : K => NoMCA dom k e [] 0 W ∧ ¬ NoMCA dom k e ([] ++ [s]) 0 W) = ∅ :=
        filter_false_of_mem fun s _ h => h.2 (by simp [NoMCA])
      rw [this, card_empty, Nat.cast_zero]
      exact johnsonThreshold_pos dom hdom k e η hk2 hη hη4 hηn ht4 hJ
  | [], n + 1, W => by
      refine lt_of_le_of_lt ?_ (strong_mutual_johnson_interleaved dom hdom (evens W)
        (fun r x => odds W r x - evens W r x) k e η hk2 hη hη4 hηn ht4 hJ)
      exact_mod_cast card_le_card fun s hs => by
        simp only [mem_filter, mem_univ, true_and, List.nil_append, NoMCA, and_true, not_not] at hs ⊢
        exact hs
  | t :: ss, 0, W => by
      have : (univ.filter fun s : K => NoMCA dom k e (t :: ss) 0 W ∧
          ¬ NoMCA dom k e ((t :: ss) ++ [s]) 0 W) = ∅ :=
        filter_false_of_mem fun s _ h => h.2 (by simp [NoMCA])
      rw [this, card_empty, Nat.cast_zero]
      exact johnsonThreshold_pos dom hdom k e η hk2 hη hη4 hηn ht4 hJ
  | t :: ss, n + 1, W => by
      refine lt_of_le_of_lt ?_ (mca_round_card ss n (foldRows t W))
      exact_mod_cast card_le_card fun s hs => by
        simp only [mem_filter, mem_univ, true_and, List.cons_append, NoMCA] at hs ⊢
        exact ⟨hs.1.2, fun h => hs.2 ⟨hs.1.1, h⟩⟩

end MCA

/-- **The non-pinned escapes of one round**: each element `V` with `g ≠ h V` (degree `≤ d`) has at most
`d` challenges with `g(s) = h_V(s)`. -/
theorem esc_count {α : Type*} (S : Finset α) (g : K[X]) (h : α → K[X]) (d : ℕ)
    (hg : g.natDegree ≤ d) (hh : ∀ V ∈ S, (h V).natDegree ≤ d) :
    (univ.filter fun s : K => ∃ V ∈ S, g ≠ h V ∧ g.eval s = (h V).eval s).card ≤ d * S.card := by
  classical
  calc _ ≤ (S.biUnion fun V => univ.filter fun s : K => g ≠ h V ∧ (g - h V).eval s = 0).card :=
        card_le_card (by
          intro s hs
          simp only [mem_filter, mem_univ, true_and, mem_biUnion] at hs ⊢
          obtain ⟨V, hV, hne, he⟩ := hs
          exact ⟨V, hV, hne, by rw [eval_sub, he, sub_self]⟩)
    _ ≤ ∑ V ∈ S, (univ.filter fun s : K => g ≠ h V ∧ (g - h V).eval s = 0).card := card_biUnion_le
    _ ≤ ∑ _V ∈ S, d := sum_le_sum fun V hV => by
        by_cases hne : g = h V
        · simp [hne]
        · have : (univ.filter fun s : K => g ≠ h V ∧ (g - h V).eval s = 0) =
              univ.filter fun s : K => (g - h V).eval s = 0 := by
            ext s; simp [hne]
          rw [this]
          have h1 := card_filter_eval_eq_zero_le (sub_ne_zero.2 hne) (D := d + 1) (by
            have := natDegree_sub_le g (h V); have := hh V hV; omega)
          simpa using h1
    _ = d * S.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **The round-check induction** (SJ §2.2): if every round check passes for the prover's polynomials
`g` against the running claim `cl`, the true polynomials `h` sum to the truth `tr`, and no round escapes
(`g l ≠ h l → g l (s l) ≠ h l (s l)`), then a false claim stays false through `ell` rounds. -/
theorem claim_ne_of_noEsc (ell : ℕ) (cl tr : ℕ → K) (g h : ℕ → K[X]) (s : ℕ → K)
    (hchk : ∀ l < ell, (g l).eval 0 + (g l).eval 1 = cl l)
    (hcl : ∀ l < ell, cl (l + 1) = (g l).eval (s l))
    (htr : ∀ l < ell, (h l).eval 0 + (h l).eval 1 = tr l)
    (htr' : ∀ l < ell, tr (l + 1) = (h l).eval (s l))
    (hesc : ∀ l < ell, g l ≠ h l → (g l).eval (s l) ≠ (h l).eval (s l)) (h0 : cl 0 ≠ tr 0) :
    cl ell ≠ tr ell := by
  suffices ∀ l ≤ ell, cl l ≠ tr l from this ell le_rfl
  intro l
  induction l with
  | zero => exact fun _ => h0
  | succ l ih =>
      intro hl hEq
      have hl' : l < ell := by omega
      have hgh : g l ≠ h l := fun hg => ih (by omega) (by rw [← hchk l hl', ← htr l hl', hg])
      exact hesc l hl' hgh (by rw [← hcl l hl', ← htr' l hl', hEq])

/-! ## Part D: the good event `Good_i` of one level and its per-squeeze charges (`hsingle` form) -/

/-- **What level `i`'s good event reads** from a transcript prefix (SJ §2.1–§2.2). `stage` counts the
level's K challenges answered: `0` before `ζ_i`, `1` after `ζ_i`, `2` after `γ_i`, `2 + l` after `l`
P1.i rounds; `ss` are the answered P1.i challenges (`sList`). -/
structure JView (K ι : Type*) [Semiring K] (n : ℕ) where
  /-- the committed word `u_i` (absorbed at `C.(i−1)`) -/
  word : Fin (2 ^ n) → ι → K
  /-- `ζ_i` -/
  zeta : K
  /-- `ŷ_i` -/
  yhat : K
  /-- the `γ`-free part of the batched claim `c_i` -/
  cb : K
  /-- the `γ`-free part of `Tr_i(V)` -/
  tb : (Fin (2 ^ n) → ι → K) → K
  /-- `γ_i` -/
  gam : K
  /-- the answered P1.i challenges `s_0, …` -/
  ss : List K
  /-- the prover's round polynomial `g_l` -/
  g : ℕ → K[X]
  /-- `V`'s true round polynomial `h_{V,l}` -/
  h : ℕ → (Fin (2 ^ n) → ι → K) → K[X]
  /-- the level's K challenges answered -/
  stage : ℕ

section Good
variable {n N : ℕ} (dom : ι → K) (k e : ℕ) (msg : (Fin (2 ^ n) → ι → K) → Fin N → K) (B : Fin N → K[X])

/-- The level's list `Λ_i` and non-pinned elements, read through a view. -/
noncomputable abbrev lamV (v : JView K ι n) : Finset (Fin (2 ^ n) → ι → K) := lamL dom k e v.word

/-- **`NoEsc_i`**: no answered round lets a non-pinned element's false round polynomial agree. -/
def NoEsc (v : JView K ι n) : Prop :=
  ∀ V ∈ lamV dom k e v, V ∉ pinS (lamV dom k e v) (psiL msg B v.zeta) v.yhat →
    ∀ l < v.ss.length, v.g l ≠ v.h l V → (v.g l).eval (v.ss.getD l 0) ≠ (v.h l V).eval (v.ss.getD l 0)

/-- **`Good_i`** (SJ §2.2): `Sep_i ∧ NoSw_i ∧ ⋀_l (Expl_i(l) ∧ NoEsc_i(l))`, each conjunct present once
its challenge is answered. -/
def GoodLv (v : JView K ι n) : Prop :=
  (1 ≤ v.stage → Set.InjOn (psiL msg B v.zeta) ↑(lamV dom k e v)) ∧
  (2 ≤ v.stage → NoSw (lamV dom k e v) (psiL msg B v.zeta) v.yhat v.cb v.tb v.gam) ∧
  NoMCA dom k e v.ss n v.word ∧ NoEsc dom k e msg B v

/-- **`Good_i`'s payoff on a passing chain** (SJ §2.2, used by §2.4's descent): after all rounds, with
the round checks passing, every non-pinned element's final claim is false. -/
theorem goodLv_claim_ne (v : JView K ι n) (hG : GoodLv dom k e msg B v) (hst : 2 ≤ v.stage)
    (cl : ℕ → K) (tr : ℕ → K) (V : Fin (2 ^ n) → ι → K) (hV : V ∈ lamV dom k e v)
    (hn : V ∉ pinS (lamV dom k e v) (psiL msg B v.zeta) v.yhat)
    (h0 : cl 0 = v.cb + v.gam * v.yhat) (ht0 : tr 0 = v.tb V + v.gam * psiL msg B v.zeta V)
    (hchk : ∀ l < v.ss.length, (v.g l).eval 0 + (v.g l).eval 1 = cl l)
    (hcl : ∀ l < v.ss.length, cl (l + 1) = (v.g l).eval (v.ss.getD l 0))
    (htr : ∀ l < v.ss.length, (v.h l V).eval 0 + (v.h l V).eval 1 = tr l)
    (htr' : ∀ l < v.ss.length, tr (l + 1) = (v.h l V).eval (v.ss.getD l 0)) :
    cl v.ss.length ≠ tr v.ss.length :=
  claim_ne_of_noEsc _ cl tr v.g (fun l => v.h l V) (fun l => v.ss.getD l 0) hchk hcl htr htr'
    (fun l hl => by have h4 := hG.2.2.2; unfold NoEsc at h4; exact h4 V hV hn l hl)
    (by have h2 := hG.2.1 hst; unfold NoSw at h2; rw [h0, ht0]; exact h2 V hV hn)

variable {Tr Dg : Type*} [Fintype Dg] (ext1 : Tr → Dg → Tr) (ch : Dg → K) (view : Tr → JView K ι n)

omit [DecidableEq ι] in
theorem card_fiber_le (hfib : ∀ S : Finset K, (univ.filter fun a => ch a ∈ S).card ≤ S.card)
    (P : K → Prop) [DecidablePred P] :
    (univ.filter fun a => P (ch a)).card ≤ (univ.filter P).card := by
  have := hfib (univ.filter P); simpa using this

open Classical in
/-- **The charge at `ζ_i`** (`hsingle` at `OODζ.i`): only `ζ` and the stage move, so `Good_i` breaks only
by `¬ Sep_i`: at most `C(L,2)·(D − 1)` answers. -/
theorem good_charge_zeta {D Lb : ℕ}
    (hfib : ∀ S : Finset K, (univ.filter fun a => ch a ∈ S).card ≤ S.card) (es : Tr)
    (hw : ∀ a, (view (ext1 es a)).word = (view es).word)
    (hz : ∀ a, (view (ext1 es a)).zeta = ch a)
    (hst' : ∀ a, (view (ext1 es a)).stage = 1) (hss' : ∀ a, (view (ext1 es a)).ss = [])
    (hL : (lamL dom k e (view es).word).card ≤ Lb) (hmsg : Set.InjOn msg ↑(lamL dom k e (view es).word))
    (hB : LinearIndependent K B) (hdeg : ∀ j, (B j).natDegree < D) :
    (univ.filter fun a => GoodLv dom k e msg B (view es) ∧ ¬ GoodLv dom k e msg B (view (ext1 es a))).card ≤
      Lb.choose 2 * (D - 1) := by
  refine le_trans (card_le_card ?_) ((card_fiber_le ch hfib (fun ζ => ¬ Set.InjOn (psiL msg B ζ)
    ↑(lamL dom k e (view es).word))).trans (sep_count dom k e _ hL msg hmsg B hB hdeg))
  intro a ha
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  refine fun hS => ha.2 ⟨fun _ => ?_, fun h2 => by rw [hst'] at h2; omega, ?_, ?_⟩
  · rw [lamV, hw, hz]; exact hS
  · rw [hss']; trivial
  · unfold NoEsc; intro V _ _ l hl; rw [hss'] at hl; simp at hl

open Classical in
/-- **The charge at `γ_i`** (`hsingle` at `Pγ.i`): only `γ` and the stage move, so `Good_i` breaks only by
`¬ NoSw_i`: at most `|Λ_i \ Λ^ŷ_i| ≤ L` answers (all of `Λ_i` when `far^J_i`). -/
theorem good_charge_gamma {Lb : ℕ}
    (hfib : ∀ S : Finset K, (univ.filter fun a => ch a ∈ S).card ≤ S.card) (es : Tr) (hst : (view es).stage = 1)
    (hw : ∀ a, (view (ext1 es a)).word = (view es).word)
    (hz : ∀ a, (view (ext1 es a)).zeta = (view es).zeta)
    (hy : ∀ a, (view (ext1 es a)).yhat = (view es).yhat)
    (hcb : ∀ a, (view (ext1 es a)).cb = (view es).cb) (htb : ∀ a, (view (ext1 es a)).tb = (view es).tb)
    (hg : ∀ a, (view (ext1 es a)).gam = ch a) (hss' : ∀ a, (view (ext1 es a)).ss = [])
    (hL : (lamL dom k e (view es).word).card ≤ Lb) :
    (univ.filter fun a => GoodLv dom k e msg B (view es) ∧ ¬ GoodLv dom k e msg B (view (ext1 es a))).card ≤
      Lb := by
  set v := view es
  refine le_trans (card_le_card ?_) ((card_fiber_le ch hfib (fun γ => ¬ NoSw (lamV dom k e v)
    (psiL msg B v.zeta) v.yhat v.cb v.tb γ)).trans ((gamma_count _ _ _ _ _).trans
    ((card_le_card sdiff_subset).trans hL)))
  intro a ha
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  obtain ⟨⟨hS, -, -, -⟩, hn⟩ := ha
  refine fun hW => hn ⟨fun _ => ?_, fun _ => ?_, ?_, ?_⟩
  · rw [lamV, hw, hz]; exact hS (by rw [hst])
  · rw [lamV, hw, hz, hy, hcb, htb, hg]; exact hW
  · rw [hss']; trivial
  · unfold NoEsc; intro V _ _ l hl; rw [hss'] at hl; simp at hl

open Classical in
/-- **The charge at P1.i round `l`** (`hsingle` at the round's squeeze): the round appends `s_l` to `ss`;
`Good_i` breaks only by the MCA bad set of the round's line (`< T`, L1 + L2) or a non-pinned element's
escape (`≤ d` each). So at most `⌈T⌉ + d·L` answers (SJ `p1J_good_count`, `d = 2`). -/
theorem good_charge_round {Lb d : ℕ}
    (hfib : ∀ S : Finset K, (univ.filter fun a => ch a ∈ S).card ≤ S.card) (hdom : Function.Injective dom) (η : ℝ)
    (hk2 : 2 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4) (hηn : 1 ≤ η * (Fintype.card ι))
    (ht4 : 4 * η * (Fintype.card ι) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hJ : ((k - 1 : ℕ) : ℝ) * (Fintype.card ι)
        ≤ (((Fintype.card ι - e : ℕ) : ℝ) - 4 * η * (Fintype.card ι)) ^ 2)
    (es : Tr) (hst : 2 ≤ (view es).stage)
    (hw : ∀ a, (view (ext1 es a)).word = (view es).word)
    (hz : ∀ a, (view (ext1 es a)).zeta = (view es).zeta)
    (hy : ∀ a, (view (ext1 es a)).yhat = (view es).yhat)
    (hcb : ∀ a, (view (ext1 es a)).cb = (view es).cb) (htb : ∀ a, (view (ext1 es a)).tb = (view es).tb)
    (hgm : ∀ a, (view (ext1 es a)).gam = (view es).gam)
    (hst' : ∀ a, (view (ext1 es a)).stage = (view es).stage + 1)
    (hss' : ∀ a, (view (ext1 es a)).ss = (view es).ss ++ [ch a])
    (hg : ∀ a, ∀ l ≤ (view es).ss.length, (view (ext1 es a)).g l = (view es).g l)
    (hh : ∀ a, ∀ l ≤ (view es).ss.length, (view (ext1 es a)).h l = (view es).h l)
    (hdg : ((view es).g (view es).ss.length).natDegree ≤ d)
    (hdh : ∀ V, ((view es).h (view es).ss.length V).natDegree ≤ d)
    (hL : (lamL dom k e (view es).word).card ≤ Lb) :
    (univ.filter fun a => GoodLv dom k e msg B (view es) ∧ ¬ GoodLv dom k e msg B (view (ext1 es a))).card ≤
      ⌈johnsonThreshold k (Fintype.card ι) e η⌉₊ + d * Lb := by
  set v := view es
  set l := v.ss.length
  set S := lamV dom k e v \ pinS (lamV dom k e v) (psiL msg B v.zeta) v.yhat
  -- the two bad sets, over the challenge
  set A := univ.filter fun s : K => NoMCA dom k e v.ss n v.word ∧ ¬ NoMCA dom k e (v.ss ++ [s]) n v.word
  set E := univ.filter fun s : K => ∃ V ∈ S, v.g l ≠ v.h l V ∧ (v.g l).eval s = (v.h l V).eval s
  have hA : (A.card : ℝ) < johnsonThreshold k (Fintype.card ι) e η :=
    mca_round_card dom hdom k e η hk2 hη hη4 hηn ht4 hJ v.ss n v.word
  have hA' : A.card ≤ ⌈johnsonThreshold k (Fintype.card ι) e η⌉₊ := by
    exact_mod_cast hA.le.trans (Nat.le_ceil _)
  have hE : E.card ≤ d * Lb :=
    (esc_count S (v.g l) (fun V => v.h l V) d hdg fun V _ => hdh V).trans
      (Nat.mul_le_mul_left _ ((card_le_card sdiff_subset).trans hL))
  refine le_trans (card_le_card ?_) ((card_fiber_le ch hfib (fun s => s ∈ A ∪ E)).trans
    ((card_le_card (by intro s hs; simpa using hs)).trans ((card_union_le A E).trans (add_le_add hA' hE))))
  intro a ha
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  obtain ⟨⟨hS, hW, hM, hEsc⟩, hn⟩ := ha
  by_contra hAE
  rw [mem_union, not_or] at hAE
  obtain ⟨hnA, hnE⟩ := hAE
  apply hn
  have hlam : lamV dom k e (view (ext1 es a)) = lamV dom k e v := by rw [lamV, lamV, hw]
  refine ⟨fun _ => ?_, fun _ => ?_, ?_, ?_⟩
  · rw [hlam, hz]; exact hS (by omega)
  · rw [hlam, hz, hy, hcb, htb, hgm]; exact hW hst
  · rw [hss', hw]
    by_contra h
    exact hnA (by simp only [A, mem_filter, mem_univ, true_and]; exact ⟨hM, h⟩)
  · unfold NoEsc; intro V hV hnp l' hl' hne
    rw [hlam] at hV hnp; rw [hz, hy] at hnp
    rw [hss', List.length_append, List.length_singleton] at hl'
    rw [hg a l' (by omega), hh a l' (by omega)] at hne ⊢
    rw [hss']
    rcases Nat.lt_or_ge l' l with hlt | hge
    · have hgd : (v.ss ++ [ch a]).getD l' 0 = v.ss.getD l' 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hgd]; exact hEsc V hV hnp l' hlt hne
    · have hl'l : l' = l := by omega
      have hgd : (v.ss ++ [ch a]).getD l' 0 = ch a := by
        simp [List.getD_eq_getElem?_getD, hl'l, l]
      rw [hgd]
      intro heq
      subst hl'l
      exact hnE (by simp only [E, mem_filter, mem_univ, true_and]
                    exact ⟨V, mem_sdiff.2 ⟨hV, hnp⟩, hne, heq⟩)

end Good

/-! ## Part E: `V*_i` of a transcript, uniqueness off the separation event, the list dooms, the zero-charge
steps, the composition of levels, and the descent (SJ §2.3 A/C, §2.4) -/

section Use
variable {n N : ℕ} (dom : ι → K) (k e : ℕ) (msg : (Fin (2 ^ n) → ι → K) → Fin N → K) (B : Fin N → K[X])

/-- **`V*_i` of a transcript** (SJ's `decodeLJ κ L es i`): the pinned element of the level's view
`v = view es`. It reads `u_i` (fixed at `C.(i−1)`), `ζ_i` and `ŷ_i` only. -/
noncomputable def pinnedJ (v : JView K ι n) : Fin (2 ^ n) → ι → K :=
  pinV (lamV dom k e v) (psiL msg B v.zeta) v.yhat

/-- **`far^J_i` of a transcript** (SJ's `farLJ κ L es i`). -/
def farJV (v : JView K ι n) : Prop := farJ (lamV dom k e v) (psiL msg B v.zeta) v.yhat

/-- SJ's text of `farLJ`: no list element is OOD-consistent. -/
theorem farJ_iff {α : Type*} [DecidableEq α] {lam : Finset α} {ψ : α → K} {y : K} :
    farJ lam ψ y ↔ ¬ ∃ V ∈ lam, ψ V = y := by
  simp [farJ, pinS, filter_eq_empty_iff]

/-- `V*_i` is a list element with `ψ_i(V*_i) = ŷ_i` unless `far^J_i`. -/
theorem pinnedJ_spec (v : JView K ι n) (h : ¬ farJV dom k e msg B v) :
    pinnedJ dom k e msg B v ∈ lamV dom k e v ∧ psiL msg B v.zeta (pinnedJ dom k e msg B v) = v.yhat :=
  pinV_spec h

/-- **Uniqueness on `Good_i`**: once `ζ_i` is answered and `Good_i` holds, every OOD-consistent list element
is `V*_i`. -/
theorem eq_pinnedJ_of_good (v : JView K ι n) (hG : GoodLv dom k e msg B v) (hst : 1 ≤ v.stage)
    {V : Fin (2 ^ n) → ι → K} (hV : V ∈ lamV dom k e v) (hψ : psiL msg B v.zeta V = v.yhat) :
    V = pinnedJ dom k e msg B v :=
  eq_pinV (hG.1 hst) (mem_pinS.2 ⟨hV, hψ⟩)

/-- `V*_i` moves only with `u_i`, `ζ_i`, `ŷ_i`. -/
theorem pinnedJ_congr {v v' : JView K ι n} (hw : v'.word = v.word) (hz : v'.zeta = v.zeta)
    (hy : v'.yhat = v.yhat) : pinnedJ dom k e msg B v' = pinnedJ dom k e msg B v := by
  unfold pinnedJ lamV; rw [hw, hz, hy]

end Use

/-- **Uniqueness except on the separation bad event** (SJ §2.1): at most `C(L,2)·(D − 1)` values of `ζ`
leave some `ŷ` with two OOD-consistent list elements. -/
theorem pin_unique_count {m N D Lb : ℕ} (dom : ι → K) (k e : ℕ) (U : Fin m → ι → K)
    (hL : (lamL dom k e U).card ≤ Lb) (msg : (Fin m → ι → K) → Fin N → K)
    (hmsg : Set.InjOn msg ↑(lamL dom k e U)) (B : Fin N → K[X]) (hB : LinearIndependent K B)
    (hdeg : ∀ j, (B j).natDegree < D) :
    (univ.filter fun ζ : K => ∃ y, 1 < (pinS (lamL dom k e U) (psiL msg B ζ) y).card).card ≤
      Lb.choose 2 * (D - 1) := by
  refine le_trans (card_le_card fun ζ hζ => ?_) (sep_count dom k e U hL msg hmsg B hB hdeg)
  simp only [mem_filter, mem_univ, true_and] at hζ ⊢
  obtain ⟨y, hy⟩ := hζ
  exact fun hS => absurd (pinS_card_le_one hS y) (by omega)

section Dooms
variable {α : Type*} [DecidableEq α] {lam : Finset α} {ψ : α → K} {y : K} {Bad : α → Prop}

/-- **`D_C`** (SJ §2.3 A, the doom after `C.(i−1)`): every list element is bad. -/
def DCl (lam : Finset α) (Bad : α → Prop) : Prop := ∀ V ∈ lam, Bad V

/-- **`D_y`** (SJ §2.3 C, the doom after `OODy.i`): every OOD-consistent list element is bad. -/
def Dyl (lam : Finset α) (ψ : α → K) (y : K) (Bad : α → Prop) : Prop := ∀ V ∈ pinS lam ψ y, Bad V

/-- Step C costs nothing: `D_C ⇒ D_y` (a restriction), whatever `ŷ` the prover absorbs. -/
theorem dyl_of_dcl (h : DCl lam Bad) : Dyl lam ψ y Bad := fun V hV => h V (mem_pinS.1 hV).1

/-- Under `Sep_i`, `D_y` is pinned-only: **doomed iff the pinned element, if any, is bad**. -/
theorem dyl_iff [Zero α] (hS : Set.InjOn ψ ↑lam) : Dyl lam ψ y Bad ↔ farJ lam ψ y ∨ Bad (pinV lam ψ y) := by
  constructor
  · intro h
    by_cases hf : farJ lam ψ y
    · exact Or.inl hf
    · exact Or.inr (h _ (pinV_mem hf))
  · rintro (hf | hb) V hV
    · rw [farJ] at hf; rw [hf] at hV; simp at hV
    · rw [eq_pinV hS hV]; exact hb

end Dooms

section Zero
variable {n N : ℕ} (dom : ι → K) (k e : ℕ) (msg : (Fin (2 ^ n) → ι → K) → Fin N → K) (B : Fin N → K[X])

/-- Before `ζ_i` (`C.(i−1)` and earlier) `Good_i` holds: no charge, whatever `u_i` is absorbed. -/
theorem goodLv_pre (v : JView K ι n) (h0 : v.stage = 0) (hss : v.ss = []) : GoodLv dom k e msg B v := by
  refine ⟨fun h => by omega, fun h => by omega, by rw [hss]; trivial, ?_⟩
  unfold NoEsc; intro V _ _ l hl; rw [hss] at hl; simp at hl

/-- Between `ζ_i` and `γ_i`, `Good_i` is `Sep_i`. -/
theorem goodLv_s1_iff (v : JView K ι n) (hs : v.stage = 1) (hss : v.ss = []) :
    GoodLv dom k e msg B v ↔ Set.InjOn (psiL msg B v.zeta) ↑(lamV dom k e v) := by
  constructor
  · intro h; exact h.1 (by omega)
  · intro h
    refine ⟨fun _ => h, fun h2 => by omega, by rw [hss]; trivial, ?_⟩
    unfold NoEsc; intro V _ _ l hl; rw [hss] at hl; simp at hl

/-- So `OODy.i` (`ŷ_i`), P2.(i−1), Q.(i−1) and P3.(i−1) cost `Good_i` nothing: they leave `u_i`, `ζ_i`. -/
theorem goodLv_congr_s1 {v v' : JView K ι n} (hs : v.stage = 1) (hs' : v'.stage = 1) (hss : v.ss = [])
    (hss' : v'.ss = []) (hw : v'.word = v.word) (hz : v'.zeta = v.zeta) :
    GoodLv dom k e msg B v' ↔ GoodLv dom k e msg B v := by
  rw [goodLv_s1_iff dom k e msg B v' hs' hss', goodLv_s1_iff dom k e msg B v hs hss, lamV, lamV, hw, hz]

/-- An absorb inside P1.i (the prover's next round polynomial `g_l`, `l = |ss|`) costs `Good_i` nothing:
`Good_i` reads `g`, `h` only at answered rounds. -/
theorem goodLv_congr {v v' : JView K ι n} (hw : v'.word = v.word) (hz : v'.zeta = v.zeta)
    (hy : v'.yhat = v.yhat) (hcb : v'.cb = v.cb) (htb : v'.tb = v.tb) (hgm : v'.gam = v.gam)
    (hss : v'.ss = v.ss) (hst : v'.stage = v.stage)
    (hg : ∀ l < v.ss.length, v'.g l = v.g l) (hh : ∀ l < v.ss.length, v'.h l = v.h l) :
    GoodLv dom k e msg B v' ↔ GoodLv dom k e msg B v := by
  unfold GoodLv NoEsc lamV
  rw [hw, hz, hy, hcb, htb, hgm, hss, hst]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun V hV hn l hl => ?_⟩
    have := h4 V hV hn l hl
    rwa [hg l hl, hh l hl] at this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun V hV hn l hl => ?_⟩
    rw [hg l hl, hh l hl]; exact h4 V hV hn l hl

end Zero

open Classical in
/-- **Levels compose** (`μ_G`'s `hsingle` for `Good = ⋀_i Good_i`): one squeeze's escape count is at most the
sum of the levels' counts (each other level's count is `0` by the zero-charge lemmas above). -/
theorem conj_charge {Dg β : Type*} [Fintype Dg] (S : Finset β) (G0 : β → Prop) (G1 : β → Dg → Prop) :
    (univ.filter fun a => (∀ i ∈ S, G0 i) ∧ ¬ ∀ i ∈ S, G1 i a).card ≤
      ∑ i ∈ S, (univ.filter fun a => G0 i ∧ ¬ G1 i a).card := by
  refine (card_le_card ?_).trans card_biUnion_le
  intro a ha
  simp only [mem_filter, mem_univ, true_and, mem_biUnion, not_forall] at ha ⊢
  obtain ⟨h0, i, hi, h1⟩ := ha
  exact ⟨i, hi, h0 i hi, h1⟩

/-- The descent's agreement form (SJ §2.4 4.): `consSet ⊆ jointAgree(u_i, V)` from the disagreement form. -/
theorem cons_sub_jointAgree {m : ℕ} {U V : Fin m → ι → K} {f g : ι → K}
    (h : colDisagree U V ⊆ univ.filter fun x => f x ≠ g x) :
    (univ.filter fun x => f x = g x) ⊆ univ.filter fun x => ∀ r, U r x = V r x := by
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  intro r
  by_contra hne
  have := h ((mem_colDisagree U V x).2 ⟨r, hne⟩)
  simp only [mem_filter, mem_univ, true_and] at this
  exact this hx

/-- …and the cardinality the extractor's `⊆` form needs: `k ≤ |consSet|` once `e + k ≤ n`. -/
theorem k_le_cons {f g : ι → K} {e k : ℕ} (hc : (univ.filter fun x => f x ≠ g x).card ≤ e)
    (hek : e + k ≤ Fintype.card ι) : k ≤ (univ.filter fun x => f x = g x).card := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun x => f x = g x)
  have hc' : (univ.filter fun x => ¬ f x = g x).card ≤ e := hc
  rw [card_univ] at h
  omega

section Descent
variable {n N : ℕ} (dom : ι → K) (k e : ℕ) (msg : (Fin (2 ^ n) → ι → K) → Fin N → K) (B : Fin N → K[X])

/-- **The descent step** (SJ §2.4 step 2, and transition A's non-pinned case): at the end of P1.i, with
`Good_i` and passing round checks, a codeword `p` that is `e`-close to the full fold, and whose final claim is
the truth of every tuple folding to it, is the fold of the **pinned** element `V*_i`, with the disagreement of
`u_i` and `V*_i` inside the fold's disagreement with `p`. -/
theorem descent_pinned (v : JView K ι n) (hG : GoodLv dom k e msg B v) (hst : 2 ≤ v.stage)
    (hlen : v.ss.length = n) (cl : ℕ → K) (tr : (Fin (2 ^ n) → ι → K) → ℕ → K)
    (h0 : cl 0 = v.cb + v.gam * v.yhat)
    (ht0 : ∀ V, tr V 0 = v.tb V + v.gam * psiL msg B v.zeta V)
    (hchk : ∀ l < n, (v.g l).eval 0 + (v.g l).eval 1 = cl l)
    (hcl : ∀ l < n, cl (l + 1) = (v.g l).eval (v.ss.getD l 0))
    (htr : ∀ V, ∀ l < n, (v.h l V).eval 0 + (v.h l V).eval 1 = tr V l)
    (htr' : ∀ V, ∀ l < n, tr V (l + 1) = (v.h l V).eval (v.ss.getD l 0))
    (p : K[X]) (hp : p.natDegree < k)
    (hc : (univ.filter fun x => foldAll v.ss n v.word x ≠ p.eval (dom x)).card ≤ e)
    (hfin : ∀ V : Fin (2 ^ n) → K[X], (∀ r, (V r).natDegree < k) → foldAllP v.ss n V = p →
      cl n = tr (evalRows dom V) n) :
    ∃ V : Fin (2 ^ n) → K[X], (∀ r, (V r).natDegree < k) ∧ foldAllP v.ss n V = p ∧
      colDisagree v.word (evalRows dom V) ⊆
        (univ.filter fun x => foldAll v.ss n v.word x ≠ p.eval (dom x)) ∧
      evalRows dom V ∈ pinS (lamV dom k e v) (psiL msg B v.zeta) v.yhat := by
  obtain ⟨V, hV, hf, hsub⟩ := expl_target dom v.word k e v.ss hG.2.2.1 hlen p hp hc
  refine ⟨V, hV, hf, hsub, ?_⟩
  have hmem : evalRows dom V ∈ lamV dom k e v := by
    simp only [lamV, lamL, mem_filter, mem_univ, true_and]
    exact ⟨fun r => ⟨V r, hV r, fun x => rfl⟩, (card_le_card hsub).trans hc⟩
  by_contra hn
  have hne := goodLv_claim_ne dom k e msg B v hG hst cl (tr (evalRows dom V)) (evalRows dom V) hmem hn h0
    (ht0 _) (fun l hl => hchk l (hlen ▸ hl)) (fun l hl => hcl l (hlen ▸ hl))
    (fun l hl => htr _ l (hlen ▸ hl)) (fun l hl => htr' _ l (hlen ▸ hl))
  rw [hlen] at hne
  exact hne (hfin V hV hf)

/-- **Transition A's core** (SJ §2.3 A, `dC_of_p1End`): at the end of P1.i, with `Good_i`, passing round checks
and the main doom `D1J(4)` (`far^J_i` or the final claim is false for `V*_i`), no codeword `p` that is `e`-close
to the full fold has a true final claim for every tuple folding to it. In the instance, `p = Enc(M V)` for a
`V ∈ Λ_{i+1}` with `TP2(V)`, every such tuple has truth `⟨foldW_i, M V⟩`, and this is `d_c(V) ≠ 0`. -/
theorem p1End_doom (v : JView K ι n) (hG : GoodLv dom k e msg B v) (hst : 2 ≤ v.stage)
    (hlen : v.ss.length = n) (cl : ℕ → K) (tr : (Fin (2 ^ n) → ι → K) → ℕ → K)
    (h0 : cl 0 = v.cb + v.gam * v.yhat)
    (ht0 : ∀ V, tr V 0 = v.tb V + v.gam * psiL msg B v.zeta V)
    (hchk : ∀ l < n, (v.g l).eval 0 + (v.g l).eval 1 = cl l)
    (hcl : ∀ l < n, cl (l + 1) = (v.g l).eval (v.ss.getD l 0))
    (htr : ∀ V, ∀ l < n, (v.h l V).eval 0 + (v.h l V).eval 1 = tr V l)
    (htr' : ∀ V, ∀ l < n, tr V (l + 1) = (v.h l V).eval (v.ss.getD l 0))
    (hD : farJV dom k e msg B v ∨ cl n ≠ tr (pinnedJ dom k e msg B v) n)
    (p : K[X]) (hp : p.natDegree < k)
    (hc : (univ.filter fun x => foldAll v.ss n v.word x ≠ p.eval (dom x)).card ≤ e) :
    ¬ ∀ V : Fin (2 ^ n) → K[X], (∀ r, (V r).natDegree < k) → foldAllP v.ss n V = p →
      cl n = tr (evalRows dom V) n := by
  intro hfin
  obtain ⟨V, hV, hf, -, hpin⟩ := descent_pinned dom k e msg B v hG hst hlen cl tr h0 ht0 hchk hcl htr htr'
    p hp hc hfin
  have heq : evalRows dom V = pinnedJ dom k e msg B v := eq_pinV (hG.1 (by omega)) hpin
  rcases hD with h | h
  · unfold farJV farJ at h; rw [h] at hpin; simp at hpin
  · have := hfin V hV hf; rw [heq] at this; exact h this

/-- **`descent_pinned` in SJ's form** (§2.4 step 2): the final truth of a tuple is a function `F` of its fold
(`⟨foldW_i, ·⟩` of the folded message), and the final claim is `F p` (`c1_i = ⟨foldW_i, M(V*_{i+1})⟩`). -/
theorem descent_pinned_F (v : JView K ι n) (hG : GoodLv dom k e msg B v) (hst : 2 ≤ v.stage)
    (hlen : v.ss.length = n) (cl : ℕ → K) (tr : (Fin (2 ^ n) → ι → K) → ℕ → K)
    (h0 : cl 0 = v.cb + v.gam * v.yhat)
    (ht0 : ∀ V, tr V 0 = v.tb V + v.gam * psiL msg B v.zeta V)
    (hchk : ∀ l < n, (v.g l).eval 0 + (v.g l).eval 1 = cl l)
    (hcl : ∀ l < n, cl (l + 1) = (v.g l).eval (v.ss.getD l 0))
    (htr : ∀ V, ∀ l < n, (v.h l V).eval 0 + (v.h l V).eval 1 = tr V l)
    (htr' : ∀ V, ∀ l < n, tr V (l + 1) = (v.h l V).eval (v.ss.getD l 0))
    (F : K[X] → K) (hF : ∀ V : Fin (2 ^ n) → K[X], tr (evalRows dom V) n = F (foldAllP v.ss n V))
    (p : K[X]) (hp : p.natDegree < k)
    (hc : (univ.filter fun x => foldAll v.ss n v.word x ≠ p.eval (dom x)).card ≤ e) (hclF : cl n = F p) :
    ∃ V : Fin (2 ^ n) → K[X], (∀ r, (V r).natDegree < k) ∧ foldAllP v.ss n V = p ∧
      colDisagree v.word (evalRows dom V) ⊆
        (univ.filter fun x => foldAll v.ss n v.word x ≠ p.eval (dom x)) ∧
      evalRows dom V ∈ pinS (lamV dom k e v) (psiL msg B v.zeta) v.yhat :=
  descent_pinned dom k e msg B v hG hst hlen cl tr h0 ht0 hchk hcl htr htr' p hp hc
    fun V _ hf => by rw [hF, hf, hclF]

/-- **`p1End_doom` in SJ's form**: with the final truth a function `F` of the fold, `cl n ≠ F p`
(`d_c ≠ 0` for every `TP2` element of the next list). -/
theorem p1End_doom_F (v : JView K ι n) (hG : GoodLv dom k e msg B v) (hst : 2 ≤ v.stage)
    (hlen : v.ss.length = n) (cl : ℕ → K) (tr : (Fin (2 ^ n) → ι → K) → ℕ → K)
    (h0 : cl 0 = v.cb + v.gam * v.yhat)
    (ht0 : ∀ V, tr V 0 = v.tb V + v.gam * psiL msg B v.zeta V)
    (hchk : ∀ l < n, (v.g l).eval 0 + (v.g l).eval 1 = cl l)
    (hcl : ∀ l < n, cl (l + 1) = (v.g l).eval (v.ss.getD l 0))
    (htr : ∀ V, ∀ l < n, (v.h l V).eval 0 + (v.h l V).eval 1 = tr V l)
    (htr' : ∀ V, ∀ l < n, tr V (l + 1) = (v.h l V).eval (v.ss.getD l 0))
    (hD : farJV dom k e msg B v ∨ cl n ≠ tr (pinnedJ dom k e msg B v) n)
    (F : K[X] → K) (hF : ∀ V : Fin (2 ^ n) → K[X], tr (evalRows dom V) n = F (foldAllP v.ss n V))
    (p : K[X]) (hp : p.natDegree < k)
    (hc : (univ.filter fun x => foldAll v.ss n v.word x ≠ p.eval (dom x)).card ≤ e) :
    cl n ≠ F p := fun hclF =>
  p1End_doom dom k e msg B v hG hst hlen cl tr h0 ht0 hchk hcl htr htr' hD p hp hc
    fun V _ hf => by rw [hF, hf, hclF]

end Descent

end LJ
