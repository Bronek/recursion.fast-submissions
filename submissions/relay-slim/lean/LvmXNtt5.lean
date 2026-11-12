-- adapted from rf-k/submissions/flock-recursive/lean/FRXFwd.lean@8bff272b (section G6_FRXBfly:
-- bflyIR_decode, as `bflyIR_decode`).
-- New for lvm (WP-13b): the table and the NTTs composed (`wtab_bflyIR_coeffs`,
-- `wtab_fwdIR_enc`) and the link to the pure decoder `LvmXDec.decWord` (`bflyIR_decWord`).
import LvmXNtt3
import LvmXNtt4

/-!
# The NTT programs composed with the basis table and the decoder

* `wtabIR_nw`: the table program does not touch the row pointer `rA0` or the forward NTT's
  registers.
* **`wtab_bflyIR_coeffs`**, **`wtab_fwdIR_enc`**: `wtabIR tb` then `bflyIR ℓ tb` (resp.
  `fwdIR ℓ tb`) from any state with the row pointer set: the table hypothesis of
  `bflyIR_sem`/`fwdIR_sem` is discharged by `wtabIR_sem`.
* **`bflyIR_decode`**: a row holding `interpF ptK J u` with `u = Enc(c)` on `J` (`|J| = 2^ℓ`)
  decodes to `c` (`Lvm.Nb.decode_row`).
* **`bflyIR_decWord`**: the row of `C_rec`'s decoder (`LvmXDec.decWord`, `ℓ = 13`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

/-- The table program writes neither the row pointer nor the forward NTT's registers. -/
theorem wtabIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rKf ∨ r = rTbf) (tb : ℕ) :
    ¬ Writes (wtabIR tb) r := by
  have hr12 : 12 ≤ r ∧ r ≠ fH ∧ r ≠ fN ∧ r ≠ fAl := by
    rcases hr with rfl | rfl | rfl <;> decide
  have n1 : ¬ Writes (mulK fH fU fW) r := (mulK_writes_iff (by have := hr12.1; omega) hr12.2.1).1
  have n2 : ¬ Writes (mulK fN fH fAl) r :=
    (mulK_writes_iff (by have := hr12.1; omega) hr12.2.2.1).1
  have n3 : ¬ Writes (invK fAl fH) r := (invK_writes_iff hr12.1 hr12.2.2.2).1
  simp only [wtabIR, row0IR, row0Body, rowIR, rowBody, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, n1, n2, n3]
  rcases hr with rfl | rfl | rfl <;>
  simp [rA0, rKf, rTbf, rTr, uI, rTa, rN2, rC2, fG, rLv, rN3, rC3, uT1, fU, fW, rAH, cTmp]

/-- **The table, then the inverse NTT**: the row ends holding the novel-basis coefficients of its
values. -/
theorem wtab_bflyIR_coeffs (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64) (hsz : A + 2 ^ ℓ ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hszt : tb + 225 ≤ s.M.size)
    (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    ∀ i < 2 ^ ℓ, rdK (semXIR I (.seq (wtabIR tb) (bflyIR ℓ tb)) s).M (A + i) =
      coeffsAt ptK nLog ℓ 0 Y i := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM htb htb2 hszt
  rw [semXIR_seq]
  refine bflyIR_coeffs I _ t3 hℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 ?_
  · rw [frame I _ s (wf_wtabIR tb) hM _ (by decide) (wtabIR_nw (.inl rfl) tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

/-- **The table, then the forward NTT**: on a zero-padded message the row ends holding `Enc`. -/
theorem wtab_fwdIR_enc (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ m : ℕ}
    (hℓ : ℓ ≤ nLog) (hmℓ : m ≤ ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64)
    (hszt : tb + 225 ≤ s.M.size) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb)
    (hA0 : rd s.M rA0 = toWord A) (c : Fin (2 ^ m) → BF64)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = if h : i < 2 ^ m then c ⟨i, h⟩ else 0) :
    ∀ j < 2 ^ ℓ, rdK (semXIR I (.seq (wtabIR tb) (fwdIR ℓ tb)) s).M (A + j) = encN ptK c j := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM htb htb2 hszt
  rw [semXIR_seq]
  refine fwdIR_enc I _ t3 hℓ hmℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 c ?_
  · rw [frame I _ s (wf_wtabIR tb) hM _ (by decide) (wtabIR_nw (.inl rfl) tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

/-- **The machine decodes a row** (`Lvm.Nb.decode_row`): if the row at `A` holds the interpolated
values `interpF ptK J u` on `ptK [0, 2^ℓ)` and `u` agrees with `Enc(c)` on `J` (`|J| = 2^ℓ`,
`J ⊆ [0, 2^15)`), the inverse NTT leaves the message `c` in the row. -/
theorem bflyIR_decode (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64) (hsz : A + 2 ^ ℓ ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb)
    (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    {J : Finset ℕ} (hJN : ∀ i ∈ J, i < 2 ^ nLog) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → BF64)
    (u : ℕ → BF64) (hu : ∀ i ∈ J, u i = encN ptK c i)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = interpF ptK J u i) (i : Fin (2 ^ ℓ)) :
    rdK (semXIR I (bflyIR ℓ tb) s).M (A + i) = c i := by
  rw [(bflyIR_sem I s hM hℓ hA hA2 hsz htb htb2 hdisj hA0 hW hY).1 i i.2, bflyRun_coeffs]
  exact congrFun (decode_row ptK_xor ptK_injOn15 hℓ
    (fun a ha b hb h => ptK_injOn15 (hJN a ha) (hJN b hb) h) hJc c u hu) i

open CompPoly.Extension BF64 in
/-- **`C_rec`'s decoder word on the machine** (`LvmXDec.decWord`): a row holding the interpolated
values `interpF ptK (selJ wd α f₁) (rowW wd l)` on `ptK [0, 2^13)` is turned by `bflyIR 13 tb`
into the words `decWord wd α f₁ (l·2^13 + v)`, `v < 2^13`. -/
theorem bflyIR_decWord (I : Array Word) (s : St) (hM : Inv s.M) {A tb : ℕ}
    (hA : regs ≤ A) (hA2 : A + 2 ^ 13 < 2 ^ 64) (hsz : A + 2 ^ 13 ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ 13 ≤ tb)
    (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (l : ℕ)
    (hY : ∀ i < 2 ^ 13, rdK s.M (A + i) = interpF ptK (selJ wd α f₁).toFinset (rowW wd l) i) :
    ∀ v < 2 ^ 13, rdK (semXIR I (bflyIR 13 tb) s).M (A + v) =
      decWord wd α f₁ (l * 2 ^ 13 + v) := by
  intro v hv
  rw [bflyIR_coeffs I s hM (by decide) hA hA2 hsz htb htb2 hdisj hA0 hW hY v hv, decWord,
    show (l * 2 ^ 13 + v) / 2 ^ 13 = l by omega, show (l * 2 ^ 13 + v) % 2 ^ 13 = v by omega]

end Lvm.X
