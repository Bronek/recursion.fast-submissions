-- WP-13b: the whole decoder program `decIR` and its semantics (new composition; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b).
import LvmXDecIR2
import LvmXEqT

/-!
# The decoder of `C_rec` on the machine

`decIR dB wB aB fB`: the basis table; `eq(α, ·)` (`eqtIR`); `Enc₀(f₁)` (`encIR`); the agreement
scan (`agreeIR`); the flag (`okIR`); on success the interpolation, the inverse NTT per row and the
reorder (`decTail`).

**`decIR_sem`**: on a memory holding the word `wd` at `wB + 64q + t`, `α_i` at `aB + 3i` and
`f₁(v)` at `fB + 3v` (`rdE`), with the layout `DecLay`:
* the cell `okB dB` holds `[2^13 ≤ |agreeL wd α f₁|]`, i.e. `decodeRec wd α f₁ ≠ none`;
* if `decodeRec wd α f₁ = some out`, the `2^19` cells at `mB dB` hold `out`;
* the heap outside the workspace `[dB, dB + 2^21)` is kept.

With `decodeRec_correct`/`decodeRec_of_ud`, the cells at `mB dB` are `C_rec`'s message.
**`cost_decIR`**: `≈ 2^37.95` steps, all but `2^31.6` in the interpolation.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The decoder program.** -/
def decIR (dB wB aB fB : ℕ) : XIR :=
  .seq (wtabIR (tbB dB)) (.seq (eqtIR 6 aB (qB dB)) (.seq (encIR dB fB)
    (.seq (agreeIR wB (qB dB) (encB dB) (agB dB)) (.seq (okIR dB) (.ite rOk (decTail dB wB) (.blk []))))))

/-! ## Pure helpers -/

theorem coeffsAt_congr {L M : Type*} [Field L] [Field M] [Algebra L M] (pt : ℕ → L) (N : ℕ) :
    ∀ ℓ s (y y' : ℕ → M), (∀ j < 2 ^ ℓ, y j = y' j) →
      ∀ x < 2 ^ ℓ, coeffsAt pt N ℓ s y x = coeffsAt pt N ℓ s y' x
  | 0, _, _, _, h, x, hx => by simp only [coeffsAt]; exact h x hx
  | ℓ + 1, s, y, y', h, x, hx => by
    have hp : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
    have hu := coeffsAt_congr pt N ℓ s y y' (fun j hj => h j (by omega))
    have hw := coeffsAt_congr pt N ℓ (s + 2 ^ ℓ) (fun j => y (2 ^ ℓ + j)) (fun j => y' (2 ^ ℓ + j))
      (fun j hj => h _ (by omega))
    simp only [coeffsAt]
    split_ifs with hx'
    · rw [hu x hx', hw x hx']
    · rw [hu _ (by omega), hw _ (by omega)]

theorem getD_take_lt {L : List ℕ} {n t : ℕ} (ht : t < n) : (L.take n).getD t 0 = L.getD t 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht]

theorem eqA_congr {α α' : ℕ → Ext3} (h : ∀ i < 6, α i = α' i) (l : ℕ) : eqA α l = eqA α' l := by
  simp only [eqA, eqBits, bitSel]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i (mem_range.1 hi)]

theorem decWord_split (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) {l v : ℕ} (hv : v < 2 ^ 13) :
    decWord wd α f₁ (l * 2 ^ 13 + v) =
      coeffsAt ptK nLog 13 0 (interpF ptK (selJ wd α f₁).toFinset (rowW wd l)) v := by
  rw [decWord]
  have h1 : (l * 2 ^ 13 + v) / 2 ^ 13 = l := by omega
  have h2 : (l * 2 ^ 13 + v) % 2 ^ 13 = v := by omega
  rw [h1, h2]

/-! ## The decoding proper -/

/-- **The decoding proper**: on a list of `≥ 2^13` agreeing positions at `agB`, the message of
`decodeRec` at `mB`. -/
theorem decTail_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) (wd : ℕ → ℕ → BF64)
    (α f₁ : ℕ → Ext3) (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hlen : 2 ^ 13 ≤ (agreeL wd α f₁).length)
    (hJ : ∀ t < 2 ^ 13, rd s.M (agB dB + t) = toWord ((agreeL wd α f₁).getD t 0)) :
    (∀ i < 2 ^ 19, rdK (semXIR I (decTail dB wB) s).M (mB dB + i) = decWord wd α f₁ i) ∧
    (∀ x, regs ≤ x → (x < dB + 2 ^ 13 ∨ dB + 2 ^ 21 ≤ x) →
      rd (semXIR I (decTail dB wB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decTail dB wB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rW
  set Jl := selJ wd α f₁ with hJl
  have hJlen : Jl.length = 2 ^ 13 := by
    rw [hJl, selJ, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_agreeL wd α f₁).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ 15 := fun j hj => (mem_agreeL.1 (List.mem_of_mem_take hj)).1
  have hBL : BaryLay (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB) s.M.size := by
    refine ⟨by norm_num, le_rfl, ?_, ?_, ?_, ?_, rW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs, agB, wbB, ebB, oB]) <;> omega
  rw [decTail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_lvm I s hM (Jl := Jl) hJlen hJnd hJlt hBL (fun t ht => by
    rw [hJ t ht, hJl, selJ, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB)) s
  generalize semXIR I (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB)) s = s1
    at b1 b2 hM1 z1
  have hL1 : DecLay dB wB aB fB s1.M.size := by rw [z1]; exact hL
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact b2 x (by simp only [regs]; omega) (by simp only [wbB]; omega) (by simp only [ebB]; omega)
      (by simp only [oB]; omega)
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bflyAll_sem I s1 hM1 hL1 hT1 (fun t i => rdK s1.M (oB dB + t * 2 ^ 13 + i))
    (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bflyAll dB) s1
  generalize semXIR I (bflyAll dB) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := rowsIR_sem I s2 hM2 (oB := oB dB) (mB := mB dB)
    (by simp only [regs, oB]; omega) (by simp only [oB]; omega) (by simp only [regs, mB]; omega)
    (by simp only [mB]; omega) (by rw [z2, z1]; simp only [mB]; omega)
    (by simp only [oB, mB]; omega)
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, hM3⟩
  · -- the message word
    have hl : i / 2 ^ 13 < 64 := by omega
    have hv : i % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by norm_num)
    have hi' : mB dB + i = mB dB + i / 2 ^ 13 * 2 ^ 13 + i % 2 ^ 13 := by
      have := Nat.div_add_mod' i (2 ^ 13); omega
    set l := i / 2 ^ 13
    set v := i % 2 ^ 13
    have ht : 63 - l < 64 := by omega
    simp only [rdK]
    rw [hi', d1 l hl v hv]
    rw [show wK (rd s2.M (oB dB + (63 - l) * 2 ^ 13 + v)) = rdK s2.M (oB dB + (63 - l) * 2 ^ 13 + v)
      from rfl, c1 (63 - l) ht v hv, show i = l * 2 ^ 13 + v by omega, decWord_split wd α f₁ hv]
    refine coeffsAt_congr ptK nLog 13 0 _ _ (fun j hj => ?_) v hv
    rw [show oB dB + (63 - l) * 2 ^ 13 + j = oB dB + 2 ^ 13 * (63 - l) + j by ring, b1 j hj _ ht]
    refine interpF_congr ptK _ (fun q hq => ?_) j
    have hq' := hJlt q (List.mem_toFinset.1 hq)
    rw [hW q hq' _ ht, rowW]
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by simp only [mB]; omega),
      c2 x (by simp only [regs]; omega) (by simp only [oB]; omega),
      b2 x (by simp only [regs]; omega) (by simp only [wbB]; omega) (by simp only [ebB]; omega)
        (by simp only [oB]; omega)]

end Lvm.X
