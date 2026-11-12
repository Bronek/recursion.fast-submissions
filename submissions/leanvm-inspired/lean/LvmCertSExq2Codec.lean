-- lvm2 X-REC2 (helper XA). The byte-level and O12 bridges of O5c that need no certificate module,
-- moved out of WP-14d's `LvmCertSExqCodec` (unchanged: `kOfBytes_eq`, `eOfBytes_eq`, `chalOf_eq_alphaE`,
-- `alphaE_zero`, `xDescend_eq`, `readRow_eq_wordOf`), and their level-1 analogues for `C_rec`'s second
-- WHIR level (lvm2 S4): `f2E_eq`, `readRow1_eq_wordOf`, `readWd1_eq_wdOf`, `capRec1_eq`.
import LvmCompileCodec
import LvmXSpec
import LvmXDecUd

/-!
# The certificate-free bridges of O5c

* `kOfBytes_eq`: `kOfBytes b = decLE (b.take 8)`; `eOfBytes_eq`, **`chalOf_eq_alphaE`**,
  **`f2E_eq`** (π's `f₂` coefficient `v` is `eOfBytes` of its 24 bytes at `f2Off + 24 v`);
* **`readRow_eq_wordOf`** (O12): XD's `readRow L cap p` is WP-5's `S.wordOf L ⟨15, 64, 7, cap⟩ p`
  for every scheme with `decK = kOfBytes`; **`readRow1_eq_wordOf`**: DEC's level-1 `readRow1 L cap p`
  is `S.wordOf L ⟨12, 48, 7, cap⟩ p`, and `readWd1_eq_wdOf`: the decoder's word is `wdOf` of it;
* **`capRec1_eq`**: the 128 digests of π's 4096 bytes at `capRec1Off` are `capRec1 π`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-! ## Bytes -/

theorem get!_eq_getD (π : ByteArray) (k : ℕ) : π.get! k = π.data.toList.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  first
    | rfl
    | (simp only [ByteArray.get!]; rfl)
    | (cases π; simp only [ByteArray.get!, getElem!_def]; split <;> simp_all <;> rfl)

theorem sum_fin_ofLE : ∀ (n : ℕ) (b : List UInt8),
    ∑ i : Fin n, (b.getD i 0).toNat * 256 ^ (i : ℕ) = ofLE (b.take n)
  | 0, b => by simp [ofLE]
  | n + 1, [] => by simp [ofLE]
  | n + 1, d :: ds => by
    rw [Fin.sum_univ_succ, List.take_succ_cons, ofLE_cons, ← sum_fin_ofLE n ds, Finset.mul_sum]
    simp only [Fin.val_zero, List.getD_cons_zero, pow_zero, mul_one, Fin.val_succ,
      List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem ofLE_take8_lt (b : List UInt8) : ofLE (b.take 8) < 2 ^ 64 :=
  (ofLE_lt _).trans_le (by
    rw [show (2 : ℕ) ^ 64 = 256 ^ 8 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by simp))

/-- **WP-5's word decoder is XD's** on the first eight bytes. -/
theorem kOfBytes_eq (b : List UInt8) : kOfBytes b = Lvm.X.decLE (b.take 8) := by
  unfold kOfBytes Lvm.X.decLE
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofFin, Fin.coe_cast, finFunctionFinEquiv_apply, toWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (ofLE_take8_lt b), ← sum_fin_ofLE 8 b]
  rfl

theorem mkE_ofFn (f : Fin BF64.ext3Params.d → BF64) :
    (CompPoly.Extension.Ext.equivFn BF64.ext3Params).symm f =
      Lvm.X.mkE (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) := by
  apply CompPoly.Extension.Ext.coeffs_injective
  apply Vector.ext
  intro i hi
  have hi3 : i < 3 := hi
  interval_cases i <;> rfl

/-- **WP-5's scalar decoder** in XD's limbs. -/
theorem eOfBytes_eq (b : List UInt8) : eOfBytes b = Lvm.X.mkE (Lvm.X.decLE (b.take 8))
    (Lvm.X.decLE ((b.drop 8).take 8)) (Lvm.X.decLE ((b.drop 16).take 8)) := by
  unfold eOfBytes
  rw [mkE_ofFn]
  simp only [kOfBytes_eq, mul_zero, mul_one, List.drop_zero]

/-- `wK` of a packed word of a byte string is XD's decoder of its eight bytes. -/
theorem wK_packBytes (l : List UInt8) {j : ℕ} (hj : 8 * j < l.length) :
    Lvm.X.wK ((packBytes l).getD j 0) = Lvm.X.decLE ((l.drop (8 * j)).take 8) := by
  rw [Lvm.X.packBytes_getDX, if_pos hj]
  rfl

/-- **The codec of a fold challenge** (bridge (a)): WP-5's `chalOf` is WP-13a's `alphaE`. -/
theorem chalOf_eq_alphaE (a : Digest) : chalOf a = Lvm.X.alphaE a := by
  have hl : a.toList.length = 32 := by simp
  rw [chalOf, eOfBytes_eq, Lvm.X.alphaE, Lvm.X.dw, Lvm.X.dw, Lvm.X.dw,
    wK_packBytes _ (by omega), wK_packBytes _ (by omega), wK_packBytes _ (by omega)]
  simp

/-- The all-zero digest's challenge is `0`. -/
theorem alphaE_zero : Lvm.X.alphaE Lvm.X.zeroDL = 0 := by
  have h0 : Lvm.X.decLE (List.replicate 8 0) = 0 := by
    unfold Lvm.X.decLE
    simp [ofLE, toWord]
    rfl
  rw [← chalOf_eq_alphaE, chalOf, eOfBytes_eq]
  simp only [Lvm.X.zeroDL, Vector.toList_replicate, List.take_replicate, List.drop_replicate]
  norm_num only [h0]
  apply CompPoly.Extension.Ext.coeffs_injective
  apply Vector.ext
  intro i hi
  have hi3 : i < 3 := hi
  interval_cases i <;> rfl

/-- **π's `f₂` coefficient** (bridge (a)): the scalar of the 24 bytes at `f2Off + 24 v`. -/
theorem f2E_eq (π : Proof) (v : ℕ) (hv : Lvm.X.f2Off Lvm.X.pX + 24 * v + 24 ≤ π.size) :
    Lvm.X.f2E π v = eOfBytes ((π.data.toList.drop (Lvm.X.f2Off Lvm.X.pX + 24 * v)).take 24) := by
  have h8 : Lvm.X.f2Off Lvm.X.pX % 8 = 0 := Lvm.X.layoutX.2.2.2.2.2.2.1
  have hs : π.data.toList.length = π.size := Array.length_toList
  rw [eOfBytes_eq, Lvm.X.f2E, Lvm.X.pw, Lvm.X.pw, Lvm.X.pw, wK_packBytes _ (by omega),
    wK_packBytes _ (by omega), wK_packBytes _ (by omega)]
  simp only [List.take_take, List.drop_take, List.drop_drop]
  have e0 : 8 * (Lvm.X.f2Off Lvm.X.pX / 8 + 3 * v) = Lvm.X.f2Off Lvm.X.pX + 24 * v := by omega
  have e1 : 8 * (Lvm.X.f2Off Lvm.X.pX / 8 + 3 * v + 1) = Lvm.X.f2Off Lvm.X.pX + 24 * v + 8 := by omega
  have e2 : 8 * (Lvm.X.f2Off Lvm.X.pX / 8 + 3 * v + 2) = Lvm.X.f2Off Lvm.X.pX + 24 * v + 16 := by
    omega
  rw [e0, e1, e2]
  simp [Nat.add_comm]

/-! ## O12: the column reading is WP-5's first-preimage word -/

theorem xDescend_eq (L : Log) : ∀ (n : ℕ) (v : Digest) (q : ℕ),
    Lvm.X.xDescend L n v q = Scheme.descend L n v q
  | 0, _, _ => rfl
  | n + 1, v, q => by
    simp only [Lvm.X.xDescend, Scheme.descend, xDescend_eq L n]
    rfl

/-- **O12**: XD's `readRow L cap p` is WP-5's word under the cap `cap` (`⟨15, 64, 7, cap⟩`), for a
scheme whose word decoder is `kOfBytes`. -/
theorem readRow_eq_wordOf (S : Scheme) (hK : S.decK = kOfBytes) (L : Log) (cap : List Digest)
    (p : ℕ) : Lvm.X.readRow L cap p = S.wordOf L ⟨15, 64, 7, cap⟩ p := by
  have hl : Lvm.X.xLeafBytes L cap p = Scheme.leafBytes L ⟨15, 64, 7, cap⟩ p := by
    simp only [Lvm.X.xLeafBytes, Scheme.leafBytes, xDescend_eq]
    rfl
  rw [Lvm.X.readRow, Scheme.wordOf, hl, hK]
  simp only [Lvm.X.xRowOf, rowOf, kOfBytes_eq, List.take_take, Nat.min_self]

/-- **O12 at level 1**: DEC's `readRow1 L cap p` is WP-5's word under the level-1 cap
(`⟨12, 48, 7, cap⟩`), for a scheme whose word decoder is `kOfBytes`. -/
theorem readRow1_eq_wordOf (S : Scheme) (hK : S.decK = kOfBytes) (L : Log) (cap : List Digest)
    (p : ℕ) : Lvm.X.readRow1 L cap p = S.wordOf L ⟨12, 48, 7, cap⟩ p := by
  have hl : Lvm.X.xLeafBytes1 L cap p = Scheme.leafBytes L ⟨12, 48, 7, cap⟩ p := by
    simp only [Lvm.X.xLeafBytes1, Scheme.leafBytes, xDescend_eq]
    rfl
  rw [Lvm.X.readRow1, Scheme.wordOf, hl, hK]
  simp only [Lvm.X.xRowOf, rowOf, kOfBytes_eq, List.take_take, Nat.min_self]

/-- **The level-1 decoder's word** is `wdOf` of WP-5's word under the level-1 cap. -/
theorem readWd1_eq_wdOf (S : Scheme) (hK : S.decK = kOfBytes) (L : Log) (cap : List Digest) :
    Lvm.X.readWd1 L cap = Lvm.X.wdOf (S.wordOf L ⟨12, 48, 7, cap⟩) := by
  funext p t
  unfold Lvm.X.readWd1 Lvm.X.wdOf
  rw [readRow1_eq_wordOf S hK]

/-- **The level-1 cap** (O13 at level 1): the 128 digests of π's 4096 bytes at `capRec1Off`. -/
theorem capRec1_eq (π : Proof) (hs : Lvm.X.capRec1Off Lvm.X.pX + 4096 ≤ π.size) :
    digestsOf ((π.data.toList.drop (Lvm.X.capRec1Off Lvm.X.pX)).take 4096) (2 ^ 7) =
      Lvm.X.capRec1 π := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  have hc : Lvm.X.capRec1Off Lvm.X.pX = 205280 := Lvm.X.layout_P20.2.2.2.1
  rw [hc] at hs ⊢
  unfold digestsOf Lvm.X.capRec1
  rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
  refine List.map_congr_left fun e he => ?_
  have he' : e < 128 := List.mem_range.1 he
  rw [Lvm.X.hdD_eq_digestAt, hc]
  apply Vector.ext
  intro i hi
  simp only [dg, digestAt, Vector.getElem_ofFn]
  rw [get!_eq_getD, List.getD_eq_getElem _ _ (by simp only [List.length_drop, List.length_take]; omega),
    List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_drop, List.getElem_take]
  have e8 : 8 * (205280 / 8 + 4 * e) + i = 205280 + (32 * e + i) := by omega
  simp only [e8]

end Lvm.ASM
