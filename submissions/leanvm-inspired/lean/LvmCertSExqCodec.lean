-- WP-14d (EXQ). New for lvm (O5c bridges (c), (d)): WP-5's byte decoders (`kOfBytes`, `eOfBytes`,
-- `chalOf`) against WP-13a's word readers (`decLE`, `pw`, `alphaE`, `f1E`), V_S's header parser
-- (`u64At`, `digestAt`, `Header.ofProof`) against WP-13a's (`pw`, `hdD`), and WP-13b's column reading
-- (`readRow`) against WP-5's first-preimage word (`Scheme.wordOf`, O12).
import LvmCertS
import LvmCertSExq2Codec

/-!
# The byte-level bridges of O5c

* (the byte decoders, `f2E_eq` and O12 are in `LvmCertSExq2Codec`, which needs no certificate module);
* **`pw_toNat`**: `(pw π j).toNat = u64At π (8 j)` (`u64At` by `Nat.two_pow_add_eq_or_of_lt`);
* **`hdrOf_eq`**: the statement's header (`hdrOf`, the header from byte 8) is `Header.ofProof π`,
  and its fields are WP-13a's (`hd_b`, `hd_vk`, `hd_cL`, `hd_s`, `hd_n`, `hd_h`, `hd_sig`);
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-! ## `u64At` and the packed words -/

theorem or_shift (x : UInt64) (c : UInt8) (k : ℕ) (hk : k < 8) (hx : x.toNat < 2 ^ (8 * k)) :
    (x ||| c.toUInt64 <<< (8 * k).toUInt64).toNat = x.toNat + 2 ^ (8 * k) * c.toNat := by
  have hc : c.toNat < 256 := c.toNat_lt
  have h1 : (8 * k).toUInt64.toNat % 64 = 8 * k := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have h2 : c.toNat * 2 ^ (8 * k) < 2 ^ 64 := by
    calc c.toNat * 2 ^ (8 * k) < 256 * 2 ^ (8 * k) := by
          exact Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ ≤ 2 ^ 64 := by
          rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, h1, UInt8.toNat_toUInt64, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt h2, Nat.lor_comm, mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx]
  ring

/-- **`u64At` is the little-endian number** of the eight bytes. -/
theorem u64At_eq (b : ByteArray) (o : ℕ) :
    u64At b o = ofLE ((List.range 8).map fun i => b.get! (o + i)) := by
  let g : ℕ → UInt64 := fun i => (b.get! (o + i)).toUInt64 <<< (8 * i).toUInt64
  let acc : ℕ → UInt64 := fun k => Nat.rec (g 0) (fun k a => a ||| g (k + 1)) k
  have key : ∀ k, k < 8 → (acc k).toNat =
      ∑ i ∈ Finset.range (k + 1), 2 ^ (8 * i) * (b.get! (o + i)).toNat ∧
      (acc k).toNat < 2 ^ (8 * (k + 1)) := by
    intro k hk
    induction k with
    | zero =>
      have hc := (b.get! (o + 0)).toNat_lt
      have e : (acc 0).toNat = (b.get! (o + 0)).toNat := by simp [acc, g]
      refine ⟨by rw [e]; simp, by rw [e]; norm_num; omega⟩
    | succ k ih =>
      obtain ⟨e, l⟩ := ih (by omega)
      have s := or_shift (acc k) (b.get! (o + (k + 1))) (k + 1) hk l
      have e' : (acc (k + 1)).toNat = (acc k).toNat + 2 ^ (8 * (k + 1)) * (b.get! (o + (k + 1))).toNat :=
        s
      refine ⟨by rw [e', e]; exact (Finset.sum_range_succ _ (k + 1)).symm, ?_⟩
      rw [e']
      have hc : (b.get! (o + (k + 1))).toNat ≤ 255 := by have := (b.get! (o + (k + 1))).toNat_lt; omega
      have hp : 2 ^ (8 * (k + 1 + 1)) = 2 ^ (8 * (k + 1)) * 256 := by
        rw [show 8 * (k + 1 + 1) = 8 * (k + 1) + 8 by ring, pow_add]; norm_num
      rw [hp]
      nlinarith
  have h7 := (key 7 (by norm_num)).1
  show (acc 7).toNat = _
  rw [h7]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, List.cons_append, ofLE_cons]
  simp only [ofLE, List.foldr]
  ring

/-- **WP-13a's packed word is V_S's `u64At`** at an aligned offset inside π. -/
theorem pw_toNat (π : Proof) (j : ℕ) (hj : 8 * j + 8 ≤ π.size) :
    (Lvm.X.pw π j).toNat = u64At π (8 * j) := by
  have hs : π.data.toList.length = π.size := Array.length_toList
  rw [Lvm.X.pw, Lvm.X.packBytes_getDX, if_pos (by omega), toWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (ofLE_take8_lt _), u64At_eq]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_take, List.length_drop, List.length_map, List.length_range] at h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [get!_eq_getD, List.getD_eq_getElem _ _ (by omega)]

/-! ## The header -/

/-- Two byte arrays equal on `[8, 5624)`. -/
def HdrEq (b b' : ByteArray) : Prop := ∀ k, 8 ≤ k → k < headerBytes → b.get! k = b'.get! k

theorem u64At_congr {b b' : ByteArray} (h : HdrEq b b') {o : ℕ} (ho : 8 ≤ o) (ho' : o + 8 ≤ headerBytes) :
    u64At b o = u64At b' o := by
  rw [u64At_eq, u64At_eq]
  congr 1
  refine List.map_congr_left fun i hi => h _ (by omega) (by simp at hi; omega)

theorem digestAt_congr {b b' : ByteArray} (h : HdrEq b b') {o : ℕ} (ho : 8 ≤ o)
    (ho' : o + 32 ≤ headerBytes) : digestAt b o = digestAt b' o := by
  apply Vector.ext
  intro i hi
  simp only [digestAt, Vector.getElem_ofFn]
  exact h _ (by omega) (by omega)

theorem sigAt_congr {b b' : ByteArray} (h : HdrEq b b') : sigAt b offSig = sigAt b' offSig := by
  have hH : headerBytes = 5624 := rfl
  have e1 : u64At b offSig = u64At b' offSig := u64At_congr h (by decide) (by decide)
  have e2 : ((List.range wotsLen).map fun k => digestAt b (offSig + 8 + 32 * k)) =
      (List.range wotsLen).map fun k => digestAt b' (offSig + 8 + 32 * k) :=
    List.map_congr_left fun k hk => digestAt_congr h (by simp [offSig]; omega) (by
      simp only [List.mem_range, wotsLen] at hk; simp only [offSig]; omega)
  have e3 : ((List.range sigHeight).map fun k => digestAt b (offSig + 8 + 32 * wotsLen + 32 * k)) =
      (List.range sigHeight).map fun k => digestAt b' (offSig + 8 + 32 * wotsLen + 32 * k) :=
    List.map_congr_left fun k hk => digestAt_congr h (by simp [offSig, wotsLen]; omega) (by
      simp only [List.mem_range, sigHeight] at hk; simp only [offSig, wotsLen]; omega)
  unfold sigAt
  rw [e1, e2, e3]

theorem ofProof_congr {b b' : ByteArray} (h : HdrEq b b') : Header.ofProof b = Header.ofProof b' := by
  unfold Header.ofProof
  rw [u64At_congr h (o := offB) (by decide) (by decide), digestAt_congr h (o := offVk) (by decide) (by decide),
    digestAt_congr h (o := offCL) (by decide) (by decide), digestAt_congr h (o := offS) (by decide) (by decide),
    u64At_congr h (o := offN) (by decide) (by decide), digestAt_congr h (o := offH) (by decide) (by decide),
    sigAt_congr h]

/-- **The statement's header is π's** (`hdrS`'s statement: π's bytes `8 … 4927`). -/
theorem hdrOf_eq (π : Proof) (hs : headerBytes ≤ π.size) :
    hdrOf ((π.data.toList.drop 8).take hdrLen) = Header.ofProof π := by
  unfold hdrOf
  apply ofProof_congr
  intro k hk hk'
  have hl : π.data.toList.length = π.size := Array.length_toList
  have hL : hdrLen = 5616 := rfl
  have hH : headerBytes = 5624 := rfl
  rw [get!_eq_getD, get!_eq_getD]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_replicate]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_take, List.getElem_drop]
  congr 1
  omega

theorem wsAt_shift (W : ℕ → RecursionFast.Word) (a u n : ℕ) :
    Lvm.X.wsAt (fun j => W (a + j)) u n = Lvm.X.wsAt W (a + u) n := by
  simp only [Lvm.X.wsAt, Nat.add_assoc]

/-- **The header's signature** is WP-13a's `σ_leaf` (words `19 …` of π). -/
theorem sig_eq (π : Proof) (hs : headerBytes ≤ π.size) :
    sigAt π offSig = Lvm.X.sigOfF fun j => Lvm.X.pw π (19 + j) := by
  have hH : headerBytes = 5624 := rfl
  have e1 : u64At π offSig = (Lvm.X.pw π (19 + 0)).toNat := (pw_toNat π 19 (by omega)).symm
  have e2 : ((List.range wotsLen).map fun k => digestAt π (offSig + 8 + 32 * k)) =
      (List.range wotsLen).map fun k => Lvm.X.digW (Lvm.X.wsAt (fun j => Lvm.X.pw π (19 + j)) (1 + 4 * k) 4) :=
    List.map_congr_left fun k _ => by
      rw [wsAt_shift, ← Lvm.X.hdD, Lvm.X.hdD_eq_digestAt]
      congr 1
      simp only [offSig]
      ring
  have e3 : ((List.range sigHeight).map fun k => digestAt π (offSig + 8 + 32 * wotsLen + 32 * k)) =
      (List.range sigHeight).map fun k =>
        Lvm.X.digW (Lvm.X.wsAt (fun j => Lvm.X.pw π (19 + j)) (1 + 4 * wotsLen + 4 * k) 4) :=
    List.map_congr_left fun k _ => by
      rw [wsAt_shift, ← Lvm.X.hdD, Lvm.X.hdD_eq_digestAt]
      congr 1
      simp only [offSig, wotsLen]
      ring
  unfold sigAt Lvm.X.sigOfF
  rw [e1, e2, e3]

end Lvm.ASM
