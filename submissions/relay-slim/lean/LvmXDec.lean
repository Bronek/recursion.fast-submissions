-- WP-13b: the pure decoder of `C_rec` (BLUEPRINT §6.2 steps 5–6) and its correctness. New on the model of
-- rf-k/submissions/flock-recursive/lean/FRXLevel.lean@8bff272b (`level_decode`: interpolate on the first `k`
-- agreeing positions, then the butterflies) and FRXBaryDefs.lean (`decode_agree`); the proof uses the ported
-- `Lvm.Nb.decode_row` (FR `decode_row`).
import LvmXEnc
import LvmMcaUd
import CompPoly.Fields.Binary.BF64.Ext3

/-!
# Decoding `C_rec`: the pure specification and its correctness

`C_rec` (BLUEPRINT §3.1, §11 A11) commits `2^19` words of `K = BF64` as 64 lane blocks ("rows")
of `k = 2^13` novel-basis coefficients; row `l` is words `l·2^13 + v`, `v < 2^13`. Its codeword
has `n₀ = 2^15` positions (rate `1/4`): position `q` is the point `x_q = K.ofBits q` (`ptK q`), and
the leaf at `q` holds 64 words, **leaf word `t` = row `63 − t`** (`rowW`). The extractor reads a
word `wd` (`wd q t` = leaf word `t` at position `q`; a missing leaf reads as zeros, as in WP-5's
`wordOf`) and decodes it with the fold challenges `α ∈ E^6` and the final `f₁` (`2^13` `E`
coefficients) of the proof:

* `foldAt α wd q = Σ_{l<64} eq(α, l)·w[l, q]`, `eq(α, l) = Π_i (l_i ? α_i : 1 − α_i)` (bit 0
  first: the first fold challenge is on the lowest lane bit, WP-0);
* `enc0 f₁ q = Σ_{v<2^13} f₁(v)·X_v(x_q)` (`Enc₀`, leanVM's novel-basis encoder);
* `agreeL`: the positions `q < 2^15`, increasing, with `foldAt α wd q = enc0 f₁ q`;
  `selJ`: its first `2^13`;
* `decWord i`: row `l = i / 2^13`, interpolated on `selJ` at the points `x_s`, `s < 2^13`
  (`interpF`), then converted to novel-basis coefficients by the inverse additive NTT
  (`coeffsAt`); `decWord i` is coefficient `i % 2^13`;
* **`decodeRec wd α f₁`**: `none` if fewer than `2^13` positions agree, else the `2^19` words
  `decWord 0, …, decWord (2^19 − 1)`.

## Correctness (`decodeRec_correct`, what WP-14 consumes)

Let `msg` be a message (`2^19` words) with codeword `cwRec msg` (row `l` = `Enc(row l of msg)`).
If

* (`hclose`) at least `2^13` positions agree with `cwRec msg` on all 64 rows (WP-6: in the UD regime
  the close codeword has `udThr 13 2 = 20480 ≥ 2^13` such positions, `decodeRec_correct_ud`),
* (`hf`) `f₁` is the fold of `msg` by `α`: `f₁(v) = Σ_l eq(α, l)·msg(l·2^13 + v)`,
* (`hluck`) the luck event fails: every position where the fold of `wd` agrees with `Enc₀(f₁)`
  agrees with `cwRec msg` on all rows (WP-6's `Ud.card_foldAllLuck_le` prices its complement),

then `decodeRec wd α f₁ = some [msg 0, …, msg (2^19 − 1)]`. Proof: the agreement set contains the
close positions (`Enc₀` is linear, so `fold(cwRec msg) = Enc₀(f₁)`), so it has `≥ 2^13` members;
it is contained in them (`hluck`); interpolation on `2^13` agreeing points and the inverse NTT
return the message (`Lvm.Nb.decode_row`).

## Equality with leanVM's encoder

`lvNovelAt` is leanVM's `novelAt` (`Protocol/Whir/NovelBasis.lean`, with `Subspace.lean`'s
`vanishingAt`, `normVanishingAt`, `basisVec`), transcribed; **`nbAt_eq_lvNovelAt`**: `X_v(x_q)`
here is `novelAt v (K.ofBits q)` there, so `enc0` and `cwRec` are leanVM's `enc`/`encK` at `κ = 13`,
`R = 2` (up to the reindexing `bitsToNat` of cube points). WP-7's `LvmNovelBasis` ports the same
definitions; the identification of the two copies is a later obligation (definitional when they
match leanVM's text).
-/

namespace Lvm.X

open Polynomial Finset Lvm.Nb CompPoly.Extension BF64

/-! ## The domain -/

/-- **The domain point** of index `j`: the `K` word whose bit `c` is the coefficient of `x^c`
(leanVM's `K.ofBits`). -/
def ptK (j : ℕ) : BF64 := BF64.ofBitVec (BitVec.ofNat 64 j)

theorem ptK_xor (a b : ℕ) : ptK (a ^^^ b) = ptK a + ptK b := by
  simp only [ptK, BitVec.ofNat_xor]; rfl

theorem ptK_zero : ptK 0 = 0 := rfl

theorem ptK_injOn64 : Set.InjOn ptK (Set.Iio (2 ^ 64)) := by
  intro a ha b hb h
  have h' := congrArg (fun x : BF64 => (BF64.toBitVec x).toNat) h
  simp only [ptK, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat] at h'
  rwa [Nat.mod_eq_of_lt (Set.mem_Iio.1 ha), Nat.mod_eq_of_lt (Set.mem_Iio.1 hb)] at h'

/-- `ptK` is injective below `2^N` for `N ≤ 64`. -/
theorem ptK_injOn {N : ℕ} (hN : N ≤ 64) : Set.InjOn ptK (Set.Iio (2 ^ N)) := fun a ha b hb h =>
  ptK_injOn64 (Set.mem_Iio.2 ((Set.mem_Iio.1 ha).trans_le (Nat.pow_le_pow_right (by norm_num) hN)))
    (Set.mem_Iio.2 ((Set.mem_Iio.1 hb).trans_le (Nat.pow_le_pow_right (by norm_num) hN))) h

/-- The table size of the decoder: points below `2^15`. -/
abbrev nLog : ℕ := 15

theorem ptK_injOn15 : Set.InjOn ptK (Set.Iio (2 ^ nLog)) := ptK_injOn (by decide)

/-! ## The objects of the decoder -/

/-- `K` inside `E`. -/
abbrev ofK (a : BF64) : Ext3 := algebraMap BF64 Ext3 a

/-- `X_v(x_q)`: the novel basis polynomial `v` at the point of position `q`. -/
noncomputable def nbAt (v q : ℕ) : BF64 := (novelX ptK v).eval (ptK q)

/-- **The `K`-codeword of a message** (`2^19` words): row `l` at position `q` is
`Enc(msg(l·2^13 + ·))[q] = Σ_{v<2^13} msg(l·2^13 + v)·X_v(x_q)`. -/
noncomputable def cwRec (msg : ℕ → BF64) (l q : ℕ) : BF64 :=
  ∑ v ∈ range (2 ^ 13), msg (l * 2 ^ 13 + v) * nbAt v q

/-- **`Enc₀`** of the final message `f₁` (`2^13` `E` coefficients) at position `q`. -/
noncomputable def enc0 (f₁ : ℕ → Ext3) (q : ℕ) : Ext3 :=
  ∑ v ∈ range (2 ^ 13), f₁ v * ofK (nbAt v q)

/-- Row `l` (lane block `l`) of the read word at position `q`: leaf word `63 − l`. -/
def rowW (wd : ℕ → ℕ → BF64) (l q : ℕ) : BF64 := wd q (63 - l)

/-- `eq(α, l) = Π_{i<6} (l_i ? α_i : 1 − α_i)`, bit 0 of the lane index first. -/
def eqA (α : ℕ → Ext3) (l : ℕ) : Ext3 := eqBits α 6 l

/-- **The fold** of the read word at position `q`: `Σ_{l<64} eq(α, l)·w[l, q]`. -/
def foldAt (α : ℕ → Ext3) (wd : ℕ → ℕ → BF64) (q : ℕ) : Ext3 :=
  ∑ l ∈ range 64, eqA α l * ofK (rowW wd l q)

/-- **The agreement list**: the positions `q < 2^15`, increasing, where the fold agrees with
`Enc₀(f₁)`. -/
noncomputable def agreeL (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) : List ℕ :=
  (List.range (2 ^ 15)).filter fun q => decide (foldAt α wd q = enc0 f₁ q)

/-- The interpolation positions: the first `2^13` of the agreement list. -/
noncomputable def selJ (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) : List ℕ :=
  (agreeL wd α f₁).take (2 ^ 13)

/-- **Word `i` of the decoded message**: row `i / 2^13` interpolated on `selJ` at the points
`x_s`, `s < 2^13`, then coefficient `i % 2^13` of the inverse additive NTT. -/
noncomputable def decWord (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (i : ℕ) : BF64 :=
  coeffsAt ptK nLog 13 0 (interpF ptK (selJ wd α f₁).toFinset (rowW wd (i / 2 ^ 13))) (i % 2 ^ 13)

/-- **The decoder of `C_rec`**: `none` when fewer than `2^13` positions agree, else the `2^19`
message words. -/
noncomputable def decodeRec (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) : Option (List BF64) :=
  if 2 ^ 13 ≤ (agreeL wd α f₁).length then
    some ((List.range (2 ^ 19)).map (decWord wd α f₁))
  else none

/-! ## Correctness -/

open Classical in
/-- The positions where the read word agrees with a codeword on all rows. -/
noncomputable def closeSet (wd : ℕ → ℕ → BF64) (msg : ℕ → BF64) : Finset ℕ :=
  (range (2 ^ 15)).filter fun q => ∀ l < 64, rowW wd l q = cwRec msg l q

/-- `cwRec` is `Enc` of the row (FR's `encN`). -/
theorem cwRec_eq_encN (msg : ℕ → BF64) (l q : ℕ) :
    cwRec msg l q = encN ptK (fun x : Fin (2 ^ 13) => msg (l * 2 ^ 13 + x)) q := by
  rw [cwRec, encN, ← Fin.sum_univ_eq_sum_range (fun v => msg (l * 2 ^ 13 + v) * nbAt v q)]
  rfl

/-- **`Enc₀` is linear**: the fold of the codeword is `Enc₀` of the folded message. -/
theorem fold_cwRec (α : ℕ → Ext3) (msg : ℕ → BF64) (q : ℕ) :
    ∑ l ∈ range 64, eqA α l * ofK (cwRec msg l q) =
      enc0 (fun v => ∑ l ∈ range 64, eqA α l * ofK (msg (l * 2 ^ 13 + v))) q := by
  simp only [cwRec, enc0, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem nodup_agreeL (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) : (agreeL wd α f₁).Nodup :=
  List.nodup_range.filter _

theorem mem_agreeL {wd : ℕ → ℕ → BF64} {α f₁ : ℕ → Ext3} {q : ℕ} :
    q ∈ agreeL wd α f₁ ↔ q < 2 ^ 15 ∧ foldAt α wd q = enc0 f₁ q := by
  simp [agreeL]

/-- **Correctness of the decoder** (BLUEPRINT §6.2): close, folded, and not lucky ⇒ the message. -/
theorem decodeRec_correct (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (msg : ℕ → BF64)
    (hclose : 2 ^ 13 ≤ (closeSet wd msg).card)
    (hf : ∀ v < 2 ^ 13, f₁ v = ∑ l ∈ range 64, eqA α l * ofK (msg (l * 2 ^ 13 + v)))
    (hluck : ∀ q < 2 ^ 15, foldAt α wd q = enc0 f₁ q → ∀ l < 64, rowW wd l q = cwRec msg l q) :
    decodeRec wd α f₁ = some ((List.range (2 ^ 19)).map msg) := by
  -- the agreement set contains the close set
  have henc : ∀ q, enc0 f₁ q =
      enc0 (fun v => ∑ l ∈ range 64, eqA α l * ofK (msg (l * 2 ^ 13 + v))) q := fun q =>
    Finset.sum_congr rfl fun v hv => by rw [hf v (mem_range.1 hv)]
  have hsub : closeSet wd msg ⊆ (agreeL wd α f₁).toFinset := by
    intro q hq
    simp only [closeSet, mem_filter, mem_range] at hq
    rw [List.mem_toFinset, mem_agreeL]
    refine ⟨hq.1, ?_⟩
    rw [henc, ← fold_cwRec, foldAt]
    exact Finset.sum_congr rfl fun l hl => by rw [hq.2 l (mem_range.1 hl)]
  have hlen : 2 ^ 13 ≤ (agreeL wd α f₁).length := by
    have := (card_le_card hsub).trans (List.toFinset_card_le _)
    omega
  rw [decodeRec, if_pos hlen]
  refine congrArg some (List.map_congr_left fun i hi => ?_)
  have hi' := List.mem_range.1 hi
  -- the interpolation positions
  set J := (selJ wd α f₁).toFinset with hJ
  have hJsub : ∀ q ∈ J, q ∈ agreeL wd α f₁ := fun q hq =>
    List.mem_of_mem_take (List.mem_toFinset.1 hq)
  have hJcard : J.card = 2 ^ 13 := by
    rw [hJ, selJ, List.toFinset_card_of_nodup
      ((nodup_agreeL wd α f₁).sublist (List.take_sublist _ _)), List.length_take,
      Nat.min_eq_left hlen]
  have hJlt : ∀ q ∈ J, q < 2 ^ nLog := fun q hq => (mem_agreeL.1 (hJsub q hq)).1
  set l := i / 2 ^ 13 with hl
  have hl64 : l < 64 := by rw [hl]; omega
  have hrow : ∀ q ∈ J, rowW wd l q = encN ptK (fun x : Fin (2 ^ 13) => msg (l * 2 ^ 13 + x)) q :=
    fun q hq => by
      obtain ⟨hq15, hfq⟩ := mem_agreeL.1 (hJsub q hq)
      rw [← cwRec_eq_encN]; exact hluck q hq15 hfq l hl64
  have hdec := decode_row ptK_xor ptK_injOn15 (ℓ := 13) (by decide)
    (fun a ha b hb h => ptK_injOn15 (hJlt a ha) (hJlt b hb) h) hJcard _ (rowW wd l) hrow
  have hv : i % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by positivity)
  have := congrFun hdec ⟨i % 2 ^ 13, hv⟩
  simp only [coeffsOfValues] at this
  rw [decWord, ← hl, this]
  show msg (l * 2 ^ 13 + i % 2 ^ 13) = msg i
  rw [hl, Nat.div_add_mod' i (2 ^ 13)]

/-- **Correctness in the unique-decoding regime**: the closeness hypothesis at WP-6's
threshold `udThr 13 2 = 20480` (`δ₀ = 3/8` of the `2^15` positions may disagree). -/
theorem decodeRec_correct_ud (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (msg : ℕ → BF64)
    (hclose : LeanVM.Protocol.Whir.udThr 13 2 ≤ (closeSet wd msg).card)
    (hf : ∀ v < 2 ^ 13, f₁ v = ∑ l ∈ range 64, eqA α l * ofK (msg (l * 2 ^ 13 + v)))
    (hluck : ∀ q < 2 ^ 15, foldAt α wd q = enc0 f₁ q → ∀ l < 64, rowW wd l q = cwRec msg l q) :
    decodeRec wd α f₁ = some ((List.range (2 ^ 19)).map msg) :=
  decodeRec_correct wd α f₁ msg
    (le_trans (by norm_num [LeanVM.Protocol.Whir.udThr]) hclose) hf hluck

end Lvm.X
