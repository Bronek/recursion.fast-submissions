-- lvm2 X-REC2 (helper DEC): the level-1 decoder's correctness from the two-level extraction facts
-- (`LvmWhirDoom2.ud_extract_rec20`). Adapted from this entry's `LvmXDecUd.lean` (v1's
-- `decodeRec_of_ud`: `wdOf`, `alphaN`, `fNr`, the bridges `eqW_eq_eqA`, `laneRows_eq`, `encRows_eq`).
import LvmXDec1
import LvmXDecUd
import LvmWhirDoom2

/-!
# The level-1 decoder returns the level-1 list member's message

`ud_extract_rec20` (two levels, lvm2 S4) gives, at a good history, the unique member `V` of the
level-1 list of the rows `Q' = rows1 4 n W₁` of the level-1 word, with
`joinMsg (decode V) = foldMsg α₀ q` (the level-0 candidate's fold), `f₂ = Σ_u eq(α₁, u)·decode V u`,
and the luck event `FoldAllLuck α₁ Q' V`.

**`decodeRec1_of_ud`**: for such a member (any `V` in the level-1 list with `f₂` its fold), off the
luck event, the pure decoder on the word's leaf words (`wdOf W₁`), the challenges (`alphaN1 α₁`)
and the residual's coefficients (`fN2 f₂`) returns `fNr (joinMsg (decode V))`: v1's level-0
residual input. With `joinMsg (decode V) = foldMsg α₀ q`, v1's `decodeRec_of_ud` then runs on
`fNr (foldMsg α₀ q)` (`not_finalDoomUd_foldMsg`). The leaves are assumed to hold 48 words.
-/

namespace Lvm.X

open Finset Lvm.Nb CompPoly.Extension BF64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd

/-- The level-1 fold challenges, `ℕ`-indexed. -/
def alphaN1 (α : Fin 4 → E) (i : ℕ) : Ext3 := if h : i < 4 then α ⟨i, h⟩ else 0

/-- The final residual's coefficients, `ℕ`-indexed (`v ↦ f(bits v)`, `v < 2^9`). -/
noncomputable def fN2 (f : (Fin (codesRec20 1).κ → Bool) → E) (v : ℕ) : Ext3 :=
  if h : v < 2 ^ 9 then f ((bitsEquiv (codesRec20 1).κ).symm ⟨v, h⟩) else 0

/-! ## The bridges -/

/-- The level-1 split of the level-0 message bits (`ud_extract_rec20`'s `by rfl`). -/
theorem hκ1 : 19 - laneBits = 4 + (codesRec20 1).κ := rfl

/-- An `extRow` of `3m` words: lane `j < m` is the `E` scalar of words `3j, 3j+1, 3j+2`. -/
theorem extRow_getD : ∀ (m : ℕ) (l : List K), l.length = 3 * m → ∀ j < m,
    (LeanVM.Protocol.Verifier.extRow l).getD j 0 =
      mkE (l.getD (3 * j) 0) (l.getD (3 * j + 1) 0) (l.getD (3 * j + 2) 0)
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, [], h, _, _ => by simp only [List.length_nil] at h; omega
  | m + 1, [_], h, _, _ => by simp only [List.length_cons, List.length_nil] at h; omega
  | m + 1, [_, _], h, _, _ => by simp only [List.length_cons, List.length_nil] at h; omega
  | m + 1, c0 :: c1 :: c2 :: rest, h, j, hj => by
    rw [LeanVM.Protocol.Verifier.extRow]
    cases j with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, extRow_getD m rest (by simp at h; omega) j (by omega)]
      have hs : ∀ k, (c0 :: c1 :: c2 :: rest).getD (k + 3) 0 = rest.getD k 0 := fun k => rfl
      rw [show 3 * (j + 1) + 2 = (3 * j + 2) + 3 by ring, show 3 * (j + 1) + 1 = (3 * j + 1) + 3 by ring,
        show 3 * (j + 1) = 3 * j + 3 by ring, hs, hs, hs]

/-- **The level-1 rows are `row1` of the leaf words** (leaves of 48 words). -/
theorem rows1_eq (W : Compile.Word) (hW : ∀ v < 2 ^ 12, (W v).length = 48)
    (u : Fin 4 → Bool) (x : Fin (codesRec20 1).n) :
    rows1 4 (codesRec20 1).n W u x = row1 (wdOf W) (bitsToNat u) x := by
  have hx : (x : ℕ) < 2 ^ 12 := x.isLt
  rw [rows1, lanesOf, if_neg one_ne_zero,
    extRow_getD 16 (W x) (hW x hx) _ (bitsToNat_lt u)]
  rfl

/-- **The level-1 fold weights**: `eqW α u = eq(α, ⟨u⟩)`. -/
theorem eqW_eq_eqA1 (α : Fin 4 → E) (u : Fin 4 → Bool) :
    eqW α u = eqA1 (alphaN1 α) (bitsToNat u) := by
  rw [eqW, eqA1, eqBits, bitSel, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [testBit_bitsToNat u i]
  simp [alphaN1, i.isLt]

theorem cube_sum16 {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ u : Fin 4 → Bool, F (bitsToNat u) = ∑ l ∈ range 16, F l := sum_cube 4 F

/-- **The joined message at `⟨u⟩ + 16⟨w⟩`** is `g u w` (lane bits low). -/
theorem fNr_joinMsg (g : (Fin 4 → Bool) → (Fin (codesRec20 1).κ → Bool) → E)
    (u : Fin 4 → Bool) (w : Fin (codesRec20 1).κ → Bool) :
    fNr (joinMsg hκ1 g)
      (bitsToNat u + 16 * bitsToNat w) = g u w := by
  have hw : bitsToNat w < 2 ^ 9 := bitsToNat_lt w
  have hv : bitsToNat u + 16 * bitsToNat w < 2 ^ 13 := by
    have := bitsToNat_lt u; omega
  have happ : bitsToNat (Fin.append u w) = bitsToNat u + 16 * bitsToNat w := bitsToNat_append u w
  rw [fNr, dif_pos hv]
  simp only [joinMsg]
  congr 1
  · funext i
    rw [bitsEquiv_symm_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.val_mk, ← happ]
    have := testBit_bitsToNat (Fin.append u w) (Fin.castAdd _ i)
    rw [Fin.coe_castAdd, Fin.append_left] at this
    exact this
  · funext i
    rw [bitsEquiv_symm_apply, Fin.coe_cast, Fin.coe_natAdd, Fin.val_mk, ← happ]
    have := testBit_bitsToNat (Fin.append u w) (Fin.natAdd 4 i)
    rw [Fin.coe_natAdd, Fin.append_right] at this
    exact this

/-- **A level-1 codeword row is `cw1` of the joined message.** -/
theorem enc_decode_cw1 (V : (Fin 4 → Bool) → Fin (codesRec20 1).n → E)
    (hcw : IsInterleavedCodeword (codesRec20 1).code V) (u : Fin 4 → Bool)
    (x : Fin (codesRec20 1).n) :
    V u x = cw1 (fNr (joinMsg hκ1
      (decode (codesRec20 1) V))) (bitsToNat u) x := by
  rw [← enc_decode (codesRec20 1) hcw u, enc_apply, cw1,
    show (2 : ℕ) ^ 9 = 2 ^ (codesRec20 1).κ from rfl,
    ← sum_cube (codesRec20 1).κ (fun v => fNr (joinMsg hκ1
      (decode (codesRec20 1) V)) (bitsToNat u + 16 * v) * Lvm.X.ofK (nbAt v x))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [fNr_joinMsg, nbAt_eq_novelAt ((bitsToNat_lt w).trans (by show (2 : ℕ) ^ 9 < 2 ^ 64; norm_num)),
    ofK_eq]

/-- **The level-1 decoder returns the level-1 member's message** in v1's residual layout. The
membership `V ∈ iList (codesRec20 1).code (codesRec20 1).thr Q'` is taken in its two parts
(`mem_iList`): a local hypothesis of the membership type at the concrete code trips Lean's
`constructorNameAsVariable` linter (maximum recursion depth); `decodeRec1_of_mem` is the
membership form. -/
theorem decodeRec1_of_ud (W₁ : Compile.Word) (hW : ∀ v < 2 ^ 12, (W₁ v).length = 48)
    (α₁ : Fin 4 → E) (f₂ : (Fin (codesRec20 1).κ → Bool) → E)
    (V : (Fin 4 → Bool) → Fin (codesRec20 1).n → E)
    (hcw : IsInterleavedCodeword (codesRec20 1).code V)
    (hcl : IsClose (codesRec20 1).thr (rows1 4 (codesRec20 1).n W₁) V)
    (hf : f₂ = ∑ u, eqW α₁ u • decode (codesRec20 1) V u)
    (hL : ¬ FoldAllLuck α₁ (rows1 4 (codesRec20 1).n W₁) V) :
    decodeRec1 (wdOf W₁) (alphaN1 α₁) (fN2 f₂) =
      some (fNr (joinMsg (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ) (decode (codesRec20 1) V))) := by
  set msg := fNr (joinMsg (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ) (decode (codesRec20 1) V))
    with hmsg
  -- the residual is the fold of the message
  have hf' : ∀ v < 2 ^ 9, fN2 f₂ v = ∑ u ∈ range 16, eqA1 (alphaN1 α₁) u * msg (u + 16 * v) := by
    intro v hv
    subst hf
    rw [fN2, dif_pos hv, Finset.sum_apply, ← cube_sum16]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, eqW_eq_eqA1, hmsg]
    congr 1
    have hb : bitsToNat ((bitsEquiv (codesRec20 1).κ).symm ⟨v, hv⟩) = v := by
      rw [← bitsEquiv_val, Equiv.apply_symm_apply]
    conv_rhs => rw [← hb]
    exact (fNr_joinMsg _ u _).symm
  -- rows and codeword rows
  have hrow : ∀ (x : Fin (codesRec20 1).n), (∀ u, rows1 4 (codesRec20 1).n W₁ u x = V u x) →
      ∀ u' < 16, row1 (wdOf W₁) u' x = cw1 msg u' x := by
    intro x hx u' hu'
    have hb : bitsToNat ((bitsEquiv 4).symm ⟨u', hu'⟩) = u' := by
      rw [← bitsEquiv_val, Equiv.apply_symm_apply]
    have := hx ((bitsEquiv 4).symm ⟨u', hu'⟩)
    rw [rows1_eq W₁ hW, enc_decode_cw1 V hcw, hb] at this
    exact this
  have hdec := decodeRec1_correct (wdOf W₁) (alphaN1 α₁) (fN2 f₂) msg ?_ hf' ?_
  · rw [hdec]
    refine congrArg some (funext fun i => ?_)
    split_ifs with hi
    · rfl
    · rw [hmsg, fNr, dif_neg hi]
  · -- closeness
    have hthr := (isClose_iff_le_card_agreeSet _ _ _).mp hcl
    refine le_trans (by show 2 ^ 9 ≤ udThr 9 3; simp only [udThr]; norm_num) (hthr.trans ?_)
    refine Finset.card_le_card_of_injOn (fun x => (x : ℕ)) ?_ (fun a _ b _ h => Fin.ext h)
    intro x hx
    rw [Finset.mem_coe, mem_agreeSet] at hx
    simp only [close1Set, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    exact ⟨x.isLt, hrow x hx⟩
  · -- no luck
    intro q hq hfold u' hu'
    have hsub : agreeSet (foldAll α₁ (rows1 4 (codesRec20 1).n W₁)) (foldAll α₁ V) ⊆
        agreeSet (rows1 4 (codesRec20 1).n W₁) V := not_not.mp hL
    let x : Fin (codesRec20 1).n := ⟨q, hq⟩
    have hx : x ∈ agreeSet (foldAll α₁ (rows1 4 (codesRec20 1).n W₁)) (foldAll α₁ V) := by
      rw [mem_agreeSet]
      intro r
      rw [foldAll_eq_sum, foldAll_eq_sum]
      have e1 : ∑ u, eqW α₁ u * rows1 4 (codesRec20 1).n W₁ u x = fold1At (alphaN1 α₁) (wdOf W₁) q := by
        rw [fold1At, ← cube_sum16 (fun l => eqA1 (alphaN1 α₁) l * row1 (wdOf W₁) l q)]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [rows1_eq W₁ hW, eqW_eq_eqA1]
      have e2 : ∑ u, eqW α₁ u * V u x = enc1 (fN2 f₂) q := by
        rw [show enc1 (fN2 f₂) q = enc1 (fun v => ∑ u ∈ range 16,
            eqA1 (alphaN1 α₁) u * msg (u + 16 * v)) q from
          Finset.sum_congr rfl fun v hv => by rw [hf' v (Finset.mem_range.1 hv)],
          ← fold_cw1, ← cube_sum16 (fun l => eqA1 (alphaN1 α₁) l * cw1 msg l q)]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [enc_decode_cw1 V hcw, eqW_eq_eqA1]
      rw [e1, e2, hfold]
    have := hsub hx
    rw [mem_agreeSet] at this
    exact hrow x this u' hu'

/-- **`decodeRec1_of_ud` for a member of the level-1 list** (`ud_extract_rec20`'s `V`). -/
theorem decodeRec1_of_mem (W₁ : Compile.Word) (hW : ∀ v < 2 ^ 12, (W₁ v).length = 48)
    (α₁ : Fin 4 → E) (f₂ : (Fin (codesRec20 1).κ → Bool) → E) :
    ∀ V ∈ iList (codesRec20 1).code (codesRec20 1).thr (rows1 4 (codesRec20 1).n W₁),
      f₂ = ∑ u, eqW α₁ u • decode (codesRec20 1) V u →
      ¬ FoldAllLuck α₁ (rows1 4 (codesRec20 1).n W₁) V →
      decodeRec1 (wdOf W₁) (alphaN1 α₁) (fN2 f₂) =
        some (fNr (joinMsg (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ)
          (decode (codesRec20 1) V))) := by
  simp only [mem_iList]
  intro V hV hf hL
  exact decodeRec1_of_ud W₁ hW α₁ f₂ V hV.1 hV.2 hf hL

end Lvm.X
