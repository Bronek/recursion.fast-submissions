-- lvm2 X-REC2 (helper DEC): the pure decoder of `C_rec`'s level-1 word and its correctness. Adapted from
-- this entry's `LvmXDec.lean` (v1's level-0 decoder `decodeRec`, `decodeRec_correct`): the rows are
-- `E` lanes (three `K` words) here, the fold has 4 challenges, the code is `κ = 9`, `R = 3`.
import LvmXDecBr
import LvmFieldFacts

/-!
# Decoding `C_rec`'s level 1: the pure specification and its correctness

`C_rec`'s second WHIR level (lvm2 S4; `codesRec20 1 = LevelCode.ud 9 3`) commits a word `W₁` of
`2^12` positions; the leaf at position `q` holds `48` `K` words, lane `u < 16` being the `E`
scalar of words `3u, 3u+1, 3u+2` (`extRow`). Row `u` of the word is lane `u` across the
positions; position `q` is the point `x_q = K.ofBits q` (`ptK q`). The extractor reads the word
(`wd q t` = leaf word `t` at `q`), the level-1 fold challenges `α ∈ E^4` and the final residual
`f₂` (`2^9` `E` coefficients):

* `row1 wd u q = mkE (wd q (3u)) (wd q (3u+1)) (wd q (3u+2))`;
* `fold1At α wd q = Σ_{u<16} eq(α, u)·row_u(q)`, `eq(α, u) = eqBits α 4 u` (bit 0 first);
* `enc1 f₂ q = Σ_{v<2^9} f₂(v)·X_v(x_q)` (`Enc₁`, the novel basis at `κ = 9`);
* `agree1L`: the positions `q < 2^12`, increasing, where the fold equals `Enc₁(f₂)`;
  `sel1J`: its first `2^9`;
* `coef1 t v`: `K` lane `t < 48` interpolated on `sel1J` (`interpF`), coefficient `v` of the
  inverse additive NTT (`coeffsAt ptK nLog 9 0`);
* **`decodeRec1 wd α f₂ : Option (ℕ → Ext3)`**: `none` if fewer than `2^9` positions agree, else
  `f₁` with `f₁(u + 16 v) = mkE (coef1 (3u) v) (coef1 (3u+1) v) (coef1 (3u+2) v)` for
  `u < 16`, `v < 2^9`, and `0` from `2^13` on. The index order is `joinMsg`'s (lane bits low),
  so `f₁` is v1's level-0 residual input (`LvmXDecUd.fNr`).

**`decodeRec1_correct`**: if at least `2^9` positions agree with the codeword `cw1 msg` of a
message `msg` (row `u` = `Enc₁(msg(u + 16·))`) on every row, `f₂` is the fold of `msg` by `α`,
and no position where the fold of the word agrees with `Enc₁(f₂)` disagrees with `cw1 msg` (no
luck), then `decodeRec1 = some msg` (cut at `2^13`).
-/

namespace Lvm.X

open Finset Lvm.Nb CompPoly.Extension BF64

/-! ## The objects of the decoder -/

/-- **Row `u` of the level-1 word at position `q`**: the `E` scalar of leaf words `3u … 3u+2`. -/
def row1 (wd : ℕ → ℕ → BF64) (u q : ℕ) : Ext3 :=
  mkE (wd q (3 * u)) (wd q (3 * u + 1)) (wd q (3 * u + 2))

/-- `eq(α, u) = Π_{i<4} (u_i ? α_i : 1 − α_i)`, bit 0 of the row index first. -/
def eqA1 (α : ℕ → Ext3) (u : ℕ) : Ext3 := eqBits α 4 u

/-- **The fold** of the level-1 word at position `q`: `Σ_{u<16} eq(α, u)·row_u(q)`. -/
def fold1At (α : ℕ → Ext3) (wd : ℕ → ℕ → BF64) (q : ℕ) : Ext3 :=
  ∑ u ∈ range 16, eqA1 α u * row1 wd u q

/-- **`Enc₁`** of the final residual `f₂` (`2^9` `E` coefficients) at position `q`. -/
noncomputable def enc1 (f₂ : ℕ → Ext3) (q : ℕ) : Ext3 :=
  ∑ v ∈ range (2 ^ 9), f₂ v * ofK (nbAt v q)

/-- **The agreement list**: the positions `q < 2^12`, increasing, where the fold agrees with
`Enc₁(f₂)`. -/
noncomputable def agree1L (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) : List ℕ :=
  (List.range (2 ^ 12)).filter fun q => decide (fold1At α wd q = enc1 f₂ q)

/-- The interpolation positions: the first `2^9` of the agreement list. -/
noncomputable def sel1J (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) : List ℕ :=
  (agree1L wd α f₂).take (2 ^ 9)

/-- `K` lane `t` (leaf word `t`) at position `q`. -/
def lane1 (wd : ℕ → ℕ → BF64) (t q : ℕ) : BF64 := wd q t

/-- **Coefficient `v` of `K` lane `t`**: the lane interpolated on `sel1J` at the points `x_s`,
`s < 2^9`, then the inverse additive NTT. -/
noncomputable def coef1 (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) (t v : ℕ) : BF64 :=
  coeffsAt ptK nLog 9 0 (interpF ptK (sel1J wd α f₂).toFinset (lane1 wd t)) v

/-- **Entry `i = u + 16 v` of the decoded message**: coefficient `v` of row `u`'s three lanes. -/
noncomputable def dec1At (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) (i : ℕ) : Ext3 :=
  mkE (coef1 wd α f₂ (3 * (i % 16)) (i / 16)) (coef1 wd α f₂ (3 * (i % 16) + 1) (i / 16))
    (coef1 wd α f₂ (3 * (i % 16) + 2) (i / 16))

/-- **The level-1 decoder**: `none` when fewer than `2^9` positions agree, else the `2^13`
entries of the level-1 message (index `u + 16 v`, lane bits low), `0` from `2^13` on. -/
noncomputable def decodeRec1 (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) : Option (ℕ → Ext3) :=
  if 2 ^ 9 ≤ (agree1L wd α f₂).length then
    some fun i => if i < 2 ^ 13 then dec1At wd α f₂ i else 0
  else none

/-! ## Correctness -/

/-- **The level-1 codeword of a message** (`2^13` `E` entries, index `u + 16 v`): row `u` at
position `q` is `Enc₁(msg(u + 16·))[q]`. -/
noncomputable def cw1 (msg : ℕ → Ext3) (u q : ℕ) : Ext3 :=
  ∑ v ∈ range (2 ^ 9), msg (u + 16 * v) * ofK (nbAt v q)

open Classical in
/-- The positions where the read word agrees with the codeword on all 16 rows. -/
noncomputable def close1Set (wd : ℕ → ℕ → BF64) (msg : ℕ → Ext3) : Finset ℕ :=
  (range (2 ^ 12)).filter fun q => ∀ u < 16, row1 wd u q = cw1 msg u q

/-- Limb `c` of an `E` scalar (`c < 3`; the coefficient of `y^c`). -/
def limbN (x : Ext3) (c : ℕ) : BF64 := LeanVM.Parameters.E.limb x ⟨c % 3, Nat.mod_lt _ (by norm_num)⟩

theorem mkE_limbN (x : Ext3) : mkE (limbN x 0) (limbN x 1) (limbN x 2) = x :=
  LeanVM.Parameters.ofLimbs_limb x

/-- A sum over `range (2^9)` against the novel basis is `encN` (FR's `encN`). -/
theorem sum_nbAt_eq_encN (g : ℕ → BF64) (q : ℕ) :
    ∑ v ∈ range (2 ^ 9), g v * nbAt v q = encN ptK (fun x : Fin (2 ^ 9) => g x) q := by
  rw [encN, ← Fin.sum_univ_eq_sum_range (fun v => g v * nbAt v q)]
  rfl

/-- **Row `u` of the codeword in coordinates**: limb `c` is `Enc` over `K` of the message's
limb `c`. -/
theorem cw1_coords (msg : ℕ → Ext3) (u q : ℕ) :
    cw1 msg u q = mkE (encN ptK (fun x : Fin (2 ^ 9) => limbN (msg (u + 16 * x)) 0) q)
      (encN ptK (fun x : Fin (2 ^ 9) => limbN (msg (u + 16 * x)) 1) q)
      (encN ptK (fun x : Fin (2 ^ 9) => limbN (msg (u + 16 * x)) 2) q) := by
  rw [← sum_nbAt_eq_encN (fun v => limbN (msg (u + 16 * v)) 0),
    ← sum_nbAt_eq_encN (fun v => limbN (msg (u + 16 * v)) 1),
    ← sum_nbAt_eq_encN (fun v => limbN (msg (u + 16 * v)) 2), ← mkE_sum, cw1]
  refine sum_congr rfl fun v _ => ?_
  rw [← mkE_mul_ofK, mkE_limbN]

/-- **A close lane is a `K` codeword**: where row `u` agrees with the codeword, lane `3u + c` is
`Enc` of the message's limb `c`. -/
theorem lane1_close {wd : ℕ → ℕ → BF64} {msg : ℕ → Ext3} {u c q : ℕ} (hc : c < 3)
    (h : row1 wd u q = cw1 msg u q) :
    lane1 wd (3 * u + c) q = encN ptK (fun x : Fin (2 ^ 9) => limbN (msg (u + 16 * x)) c) q := by
  rw [row1, cw1_coords] at h
  obtain ⟨h0, h1, h2⟩ := mkE_inj h
  interval_cases c
  · exact h0
  · exact h1
  · exact h2

/-- **`Enc₁` is linear**: the fold of the codeword is `Enc₁` of the folded message. -/
theorem fold_cw1 (α : ℕ → Ext3) (msg : ℕ → Ext3) (q : ℕ) :
    ∑ u ∈ range 16, eqA1 α u * cw1 msg u q =
      enc1 (fun v => ∑ u ∈ range 16, eqA1 α u * msg (u + 16 * v)) q := by
  simp only [cw1, enc1, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  ring

theorem nodup_agree1L (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) : (agree1L wd α f₂).Nodup :=
  List.nodup_range.filter _

theorem mem_agree1L {wd : ℕ → ℕ → BF64} {α f₂ : ℕ → Ext3} {q : ℕ} :
    q ∈ agree1L wd α f₂ ↔ q < 2 ^ 12 ∧ fold1At α wd q = enc1 f₂ q := by
  simp [agree1L]

/-- **Correctness of the level-1 decoder**: close, folded, and not lucky ⇒ the message. -/
theorem decodeRec1_correct (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) (msg : ℕ → Ext3)
    (hclose : 2 ^ 9 ≤ (close1Set wd msg).card)
    (hf : ∀ v < 2 ^ 9, f₂ v = ∑ u ∈ range 16, eqA1 α u * msg (u + 16 * v))
    (hluck : ∀ q < 2 ^ 12, fold1At α wd q = enc1 f₂ q → ∀ u < 16, row1 wd u q = cw1 msg u q) :
    decodeRec1 wd α f₂ = some fun i => if i < 2 ^ 13 then msg i else 0 := by
  -- the agreement set contains the close set
  have henc : ∀ q, enc1 f₂ q =
      enc1 (fun v => ∑ u ∈ range 16, eqA1 α u * msg (u + 16 * v)) q := fun q =>
    Finset.sum_congr rfl fun v hv => by rw [hf v (mem_range.1 hv)]
  have hsub : close1Set wd msg ⊆ (agree1L wd α f₂).toFinset := by
    intro q hq
    simp only [close1Set, mem_filter, mem_range] at hq
    rw [List.mem_toFinset, mem_agree1L]
    refine ⟨hq.1, ?_⟩
    rw [henc, ← fold_cw1, fold1At]
    exact Finset.sum_congr rfl fun u hu => by rw [hq.2 u (mem_range.1 hu)]
  have hlen : 2 ^ 9 ≤ (agree1L wd α f₂).length := by
    have := (card_le_card hsub).trans (List.toFinset_card_le _)
    omega
  rw [decodeRec1, if_pos hlen]
  refine congrArg some (funext fun i => ?_)
  split_ifs with hi
  · -- the interpolation positions
    set J := (sel1J wd α f₂).toFinset with hJ
    have hJsub : ∀ q ∈ J, q ∈ agree1L wd α f₂ := fun q hq =>
      List.mem_of_mem_take (List.mem_toFinset.1 hq)
    have hJcard : J.card = 2 ^ 9 := by
      rw [hJ, sel1J, List.toFinset_card_of_nodup
        ((nodup_agree1L wd α f₂).sublist (List.take_sublist _ _)), List.length_take,
        Nat.min_eq_left hlen]
    have hJlt : ∀ q ∈ J, q < 2 ^ nLog := fun q hq => by
      have := (mem_agree1L.1 (hJsub q hq)).1
      simp only [nLog]; omega
    have hcoef : ∀ u < 16, ∀ c < 3, ∀ v < 2 ^ 9,
        coef1 wd α f₂ (3 * u + c) v = limbN (msg (u + 16 * v)) c := by
      intro u hu c hc v hv
      have hrow : ∀ q ∈ J, lane1 wd (3 * u + c) q =
          encN ptK (fun x : Fin (2 ^ 9) => limbN (msg (u + 16 * x)) c) q := fun q hq => by
        obtain ⟨hq12, hfq⟩ := mem_agree1L.1 (hJsub q hq)
        exact lane1_close hc (hluck q hq12 hfq u hu)
      have hdec := decode_row ptK_xor ptK_injOn15 (ℓ := 9) (by decide)
        (fun a ha b hb h => ptK_injOn15 (hJlt a ha) (hJlt b hb) h) hJcard _ (lane1 wd (3 * u + c))
        hrow
      have := congrFun hdec ⟨v, hv⟩
      simp only [coeffsOfValues] at this
      rw [coef1]
      exact this
    have hu : i % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have hv : i / 16 < 2 ^ 9 := by omega
    rw [dec1At, show 3 * (i % 16) = 3 * (i % 16) + 0 from rfl, hcoef _ hu 0 (by norm_num) _ hv,
      hcoef _ hu 1 (by norm_num) _ hv, hcoef _ hu 2 (by norm_num) _ hv,
      show i % 16 + 16 * (i / 16) = i by omega, mkE_limbN]
  · rfl

/-- **Correctness in the unique-decoding regime**: closeness at `udThr 9 3 = 2304`. -/
theorem decodeRec1_correct_ud (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) (msg : ℕ → Ext3)
    (hclose : LeanVM.Protocol.Whir.udThr 9 3 ≤ (close1Set wd msg).card)
    (hf : ∀ v < 2 ^ 9, f₂ v = ∑ u ∈ range 16, eqA1 α u * msg (u + 16 * v))
    (hluck : ∀ q < 2 ^ 12, fold1At α wd q = enc1 f₂ q → ∀ u < 16, row1 wd u q = cw1 msg u q) :
    decodeRec1 wd α f₂ = some fun i => if i < 2 ^ 13 then msg i else 0 :=
  decodeRec1_correct wd α f₂ msg
    (le_trans (by norm_num [LeanVM.Protocol.Whir.udThr]) hclose) hf hluck

/-- **Non-vacuity**: the zero word with `α = 0`, `f₂ = 0` meets the hypotheses of
`decodeRec1_correct` and decodes to the zero message. -/
theorem decodeRec1_correct_zero :
    decodeRec1 (fun _ _ => 0) (fun _ => 0) (fun _ => 0) = some fun _ => 0 := by
  have hcw : ∀ u q, cw1 (fun _ => (0 : Ext3)) u q = 0 := fun u q => by simp [cw1]
  have hrow : ∀ u q, row1 (fun _ _ => (0 : BF64)) u q = 0 := fun u q => mkE_zero
  have h := decodeRec1_correct (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) ?_ ?_ ?_
  · rw [h]; simp only [ite_self]
  · have : close1Set (fun _ _ => (0 : BF64)) (fun _ => 0) = range (2 ^ 12) := by
      ext q; simp [close1Set, hrow, hcw]
    rw [this, card_range]; norm_num
  · intro v _; simp
  · intro q _ _ u _; rw [hrow, hcw]

end Lvm.X
