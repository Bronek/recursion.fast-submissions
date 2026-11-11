-- New for lvm (WP-14a, H1): V_S's header check (`parseOk`, LvmDriver) gives the compiled `S` verifier's
-- header parse (`hdrS`) and statement check (`okS`, LvmCertS), and V_S's public values (`pubOf`) are the
-- statement's (`pubX`, LvmVEqMid). `zeroBytes_spec'`, `take8_of_parse'` adapted from
-- rf-lvm-QL/submissions/leanvm-inspired/lean/LvmReplayRound.lean@lvm/QL (`zeroBytes_spec`, `take8_of_parse`).
import LvmCertS
import LvmVEqMid
import LvmVEqCodec

/-!
# The header: `parseOk` ⇒ `hdrS`, `okS`, `pubX`

`xOf π` is the statement of an `S` proof (bytes `8 … 4927`, the header after `'S' 0^7`).

* `ofProof_congr`, `pubOf_congr`: `Header.ofProof` reads only bytes `[8, headerBytes)`, `pubOf` only
  `[headerAt 8, headerAt 8 + headerBytes − 8)`;
* `hdrOf_xOf`: the header fields of the statement are the proof's;
* **`hdrS_of_parseOk`**, **`okS_of_parseOk`** (the fast hashes are the specification's, Library/Fast),
  **`pubOf_eq_pubX`**.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm

/-- The statement bytes of an `S` proof (the header from byte 8). -/
def xOf (π : ByteArray) : List UInt8 := ((π.data.toList).drop 8).take Lvm.ASM.hdrLen

/-! ## Bytes -/

theorem get!_eq_getD (b : ByteArray) (i : ℕ) : b.get! i = b.data.toList.getD i 0 := by
  rw [ByteArray.get!, getElem!_def, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  cases b.data[i]? <;> rfl

theorem get!_mk (l : List UInt8) (i : ℕ) : (⟨l.toArray⟩ : ByteArray).get! i = l.getD i 0 :=
  get!_eq_getD _ _

theorem hdrLen_eq : Lvm.ASM.hdrLen = 5616 := rfl

theorem headerBytes_eq : headerBytes = 5624 := rfl

theorem getD_xOf (π : ByteArray) {t : ℕ} (ht : t < Lvm.ASM.hdrLen) :
    (xOf π).getD t 0 = π.get! (8 + t) := by
  simp only [get!_eq_getD, xOf, List.getD_eq_getElem?_getD, List.getElem?_take, ht, ↓reduceIte,
    List.getElem?_drop]

/-- The statement's byte array (`hdrOf`'s) holds the proof's header bytes. -/
theorem get!_hdrBytes (π : ByteArray) {o : ℕ} (h1 : 8 ≤ o) (h2 : o < headerBytes) :
    (⟨(List.replicate 8 0 ++ xOf π).toArray⟩ : ByteArray).get! o = π.get! o := by
  rw [get!_mk, List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
    List.length_replicate, getD_xOf π (by rw [hdrLen_eq]; rw [headerBytes_eq] at h2; omega)]
  congr 1
  omega

/-- `sigOfX` of the statement holds the proof's header bytes. -/
theorem get!_sigOfX (π : ByteArray) {t : ℕ} (ht : t < Lvm.ASM.hdrLen) :
    (sigOfX (xOf π)).get! (headerAt 8 + t) = π.get! (8 + t) := by
  rw [sigOfX, get!_mk, List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega),
    List.length_replicate, Nat.add_sub_cancel_left, getD_xOf π ht]

/-! ## Congruence of the readers -/

theorem laneAt_congr {b b' : ByteArray} {o : ℕ} (h : ∀ i, o ≤ i → i < o + 8 → b.get! i = b'.get! i) :
    laneAt b o = laneAt b' o := by
  apply UInt64.toNat_inj.mp
  rw [toNat_laneAt, toNat_laneAt]
  exact Finset.sum_congr rfl fun i _ ↦ by
    have := i.isLt
    rw [h (o + i) (by omega) (by omega)]

theorem kAt_congr {b b' : ByteArray} {o : ℕ} (h : ∀ i, o ≤ i → i < o + 8 → b.get! i = b'.get! i) :
    kAt b o = kAt b' o := by
  unfold kAt
  rw [laneAt_congr h]

theorem u64At_congr {b b' : ByteArray} {o : ℕ} (h : ∀ i, o ≤ i → i < o + 8 → b.get! i = b'.get! i) :
    u64At b o = u64At b' o :=
  congrArg UInt64.toNat (laneAt_congr h)

theorem digestAt_congr {b b' : ByteArray} {o : ℕ} (h : ∀ i, o ≤ i → i < o + 32 → b.get! i = b'.get! i) :
    digestAt b o = digestAt b' o := by
  unfold digestAt
  exact congrArg Vector.ofFn (funext fun i ↦ h _ (by omega) (by have := i.isLt; omega))

theorem sigAt_congr {b b' : ByteArray} {o : ℕ}
    (h : ∀ i, o ≤ i → i < o + sigBytes → b.get! i = b'.get! i) : sigAt b o = sigAt b' o := by
  have hs : sigBytes = 8 + 133 * 32 + 16 * 32 := rfl
  have hw : wotsLen = 133 := rfl
  have hh : sigHeight = 16 := rfl
  have h1 : ∀ k ∈ List.range wotsLen, digestAt b (o + 8 + 32 * k) = digestAt b' (o + 8 + 32 * k) :=
    fun k hk ↦ digestAt_congr fun i h1 h2 ↦ h i (by omega) (by have := List.mem_range.mp hk; omega)
  have h2 : ∀ k ∈ List.range sigHeight, digestAt b (o + 8 + 32 * wotsLen + 32 * k) =
      digestAt b' (o + 8 + 32 * wotsLen + 32 * k) :=
    fun k hk ↦ digestAt_congr fun i h1 h2 ↦ h i (by omega) (by have := List.mem_range.mp hk; omega)
  unfold sigAt
  rw [u64At_congr fun i h1 h2 ↦ h i h1 (by omega), List.map_congr_left h1, List.map_congr_left h2]

/-- **`Header.ofProof` reads only the header bytes `[8, headerBytes)`.** -/
theorem ofProof_congr {π π' : ByteArray} (h : ∀ o, 8 ≤ o → o < headerBytes → π.get! o = π'.get! o) :
    Header.ofProof π = Header.ofProof π' := by
  have hH : headerBytes = 5624 := rfl
  have hs : sigBytes = 8 + 133 * 32 + 16 * 32 := rfl
  have hR : ∀ a n, 8 ≤ a → a + n ≤ 5624 → ∀ i, a ≤ i → i < a + n → π.get! i = π'.get! i :=
    fun a n ha hn i h1 h2 ↦ h i (by omega) (by omega)
  unfold Header.ofProof
  rw [u64At_congr (hR offB 8 (by decide) (by decide)), digestAt_congr (hR offVk 32 (by decide) (by decide)),
    digestAt_congr (hR offCL 32 (by decide) (by decide)), digestAt_congr (hR offS 32 (by decide) (by decide)),
    u64At_congr (hR offN 8 (by decide) (by decide)), digestAt_congr (hR offH 32 (by decide) (by decide)),
    sigAt_congr (hR offSig sigBytes (by decide) (by decide))]

/-- **`pubOf` reads only the header bytes of the stream.** -/
theorem pubOf_congr {vk c : Digest} {sig sig' : ByteArray}
    (h : ∀ o, headerAt 8 ≤ o → o < headerAt 8 + (headerBytes - 8) → sig.get! o = sig'.get! o) :
    pubOf vk c sig = pubOf vk c sig' := by
  have hH : headerBytes = 5624 := rfl
  have hR : ∀ a n, 8 ≤ a → a + n ≤ 5624 → ∀ i, headerAt a ≤ i → i < headerAt a + n →
      sig.get! i = sig'.get! i :=
    fun a n ha hn i h1 h2 ↦ h i (by simp only [headerAt] at h1 ⊢; omega)
      (by simp only [headerAt] at h2 ⊢; omega)
  have hL : ∀ a m, 8 ≤ a → a + 8 * m ≤ 5624 → ∀ k ∈ List.range m, ∀ i, headerAt a + 8 * k ≤ i →
      i < headerAt a + 8 * k + 8 → sig.get! i = sig'.get! i := by
    intro a m ha hm k hk i h1 h2
    have := List.mem_range.mp hk
    exact h i (by simp only [headerAt] at h1 ⊢; omega) (by simp only [headerAt] at h2 ⊢; omega)
  have hs : sigBytes / 8 = 597 := rfl
  unfold pubOf
  rw [laneAt_congr (hR 8 8 (by decide) (by decide)), laneAt_congr (hR 112 8 (by decide) (by decide)),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 48 4 (by decide) (by decide) k hk),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 80 4 (by decide) (by decide) k hk),
    List.map_congr_left fun k hk ↦ kAt_congr (hL 120 4 (by decide) (by decide) k hk), hs,
    List.map_congr_left fun k hk ↦ kAt_congr (hL 152 597 (by decide) (by decide) k hk)]
  -- A23: `acc_in`, `accVars + 1` scalars of three lanes from `offAcc`
  have hE : ∀ i, i ≤ accVars → feAt sig (headerAt (offAcc + eBytes * i)) =
      feAt sig' (headerAt (offAcc + eBytes * i)) := by
    intro i hi
    have hi' : i ≤ 28 := hi
    unfold feAt
    rw [kAt_congr fun j h1 h2 ↦ hR (offAcc + eBytes * i) 24 (by simp only [offAcc, sigBytes]; omega)
        (by simp only [offAcc, eBytes, sigBytes]; omega) j h1 (by omega),
      kAt_congr fun j h1 h2 ↦ hR (offAcc + eBytes * i) 24 (by simp only [offAcc, sigBytes]; omega)
        (by simp only [offAcc, eBytes, sigBytes]; omega) j (by omega) (by omega),
      kAt_congr fun j h1 h2 ↦ hR (offAcc + eBytes * i) 24 (by simp only [offAcc, sigBytes]; omega)
        (by simp only [offAcc, eBytes, sigBytes]; omega) j (by omega) (by omega)]
  rw [List.map_congr_left fun k hk ↦ hE k (List.mem_range.mp hk).le, hE accVars le_rfl]

/-- **The statement's header fields are the proof's.** -/
theorem hdrOf_xOf (π : ByteArray) : Lvm.ASM.hdrOf (xOf π) = Header.ofProof π :=
  ofProof_congr fun _ h1 h2 ↦ get!_hdrBytes π h1 h2

theorem hdX_xOf (π : ByteArray) : hdX (xOf π) = Header.ofProof π := hdrOf_xOf π

/-! ## `parseOk` -/

theorem zeroBytes_spec' (b : ByteArray) :
    ∀ (n o : Nat), zeroBytes b o n = true → ∀ x < n, b.get! (o + x) = 0
  | 0, _, _, x, hx => absurd hx (by omega)
  | n + 1, o, h, x, hx => by
    simp only [zeroBytes, Bool.and_eq_true, beq_iff_eq] at h
    rcases x with _ | x
    · simpa using h.1
    · rw [show o + (x + 1) = o + 1 + x by omega]; exact zeroBytes_spec' b n (o + 1) h.2 x (by omega)

/-- The first eight bytes of a proof that passes the header check are `'S'` and seven zeros. -/
theorem take8_of_parse' {π : ByteArray} (h8 : 8 ≤ π.size) (h0 : π.get! 0 = 0x53)
    (hz : zeroBytes π 1 7 = true) : π.data.toList.take 8 = Lvm.ASM.sPrefix := by
  have hz' := zeroBytes_spec' π 7 1 hz
  have hl : 8 ≤ π.data.toList.length := by rw [Array.length_toList]; exact h8
  apply List.ext_getElem (by simp [Lvm.ASM.sPrefix]; omega)
  intro n h1 h2
  have hn8 : n < 8 := by simpa [Lvm.ASM.sPrefix] using h2
  have hnl : n < π.data.toList.length := by omega
  simp only [List.getElem_take]
  have hn : π.data.toList[n] = π.get! n := by
    rw [get!_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnl, Option.getD_some]
  rw [hn]
  rcases n with _ | n
  · simpa [Lvm.ASM.sPrefix] using h0
  · have := hz' n (by omega)
    rw [Nat.add_comm 1 n] at this
    rw [this]
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> first | rfl | omega

/-- What `parseOk` checks. -/
theorem parseOk_parts {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOk p vk c π = true) :
    π.size = piSize p ∧ π.get! 0 = 0x53 ∧ zeroBytes π 1 7 = true ∧
      ((Header.ofProof π).b = 0 ∨ (Header.ofProof π).b = 1) ∧ (Header.ofProof π).vk = vk ∧
      1 ≤ (Header.ofProof π).n ∧ (Header.ofProof π).n ≤ chainCap ∧ c = (Header.ofProof π).stmt ∧
      ((Header.ofProof π).b ≠ 0 → SigOkF vk (traceDigestF []) (Header.ofProof π).sig = true) := by
  simp only [parseOk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hs, h0, hz, hb, hvk, hn1, hn2, -, hif⟩ := h
  refine ⟨hs, h0, hz, hb, hvk, hn1, hn2, ?_, ?_⟩
  · by_cases hb0 : (Header.ofProof π).b = 0
    · simp only [hb0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hif
      exact hif.2
    · simp only [hb0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hif
      exact hif.1
  · intro hb0
    simp only [hb0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hif
    exact hif.2

theorem headerBytes_le_piSize (p : Params) : headerBytes ≤ piSize p := by
  simp only [piSize]
  omega

/-- **`parseOk` ⇒ the compiled verifier's header parse.** -/
theorem hdrS_of_parseOk {vk c : Digest} {π : ByteArray} (h : parseOk P20 vk c π = true) :
    Lvm.ASM.hdrS π = some (xOf π, (π.data.toList).drop headerBytes) := by
  obtain ⟨hs, h0, hz, -⟩ := parseOk_parts h
  have h8 : 8 ≤ π.size := by
    rw [hs]; exact le_trans (by decide) (headerBytes_le_piSize P20)
  have hs' : π.size = Lvm.T.piSz := hs
  simp only [Lvm.ASM.hdrS, hs', take8_of_parse' h8 h0 hz, and_self, ↓reduceIte]
  rfl

/-- **`parseOk` ⇒ the compiled verifier's statement check** (the fast hashes are the
specification's). -/
theorem okS_of_parseOk {vk c : Digest} {π : ByteArray} (h : parseOk P20 vk c π = true) :
    Lvm.ASM.okS vk c (xOf π) = true := by
  obtain ⟨-, -, -, hb, hvk, hn1, hn2, hc, hsig⟩ := parseOk_parts h
  unfold Lvm.ASM.okS
  rw [hdrOf_xOf]
  unfold Header.stmt Header.leaf at hc
  rw [leafStmtF_eq, nodeStmtF_eq] at hc
  rw [SigOkF_eq, traceDigestF_eq] at hsig
  generalize Header.ofProof π = hd at *
  rcases hb with hb | hb
  · simp only [hb, ↓reduceIte] at hc
    simp [hb, hvk, hn1, hn2, hc]
  · simp only [hb, one_ne_zero, ↓reduceIte] at hc hsig
    simp [hb, hvk, hn1, hn2, hc, hsig]

/-- **V_S's public values are the statement's** (on a stream holding the proof's header bytes where
the seed query puts them). -/
theorem pubOf_eq_pubX {vk c : Digest} {π : ByteArray} (h : parseOk P20 vk c π = true) {sig : ByteArray}
    (hsig : ∀ t < headerBytes - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubOf vk c sig = pubX (xOf π) := by
  obtain ⟨-, -, -, -, hvk, -, -, hc, -⟩ := parseOk_parts h
  unfold pubX
  rw [hdX_xOf, hvk, ← hc]
  refine pubOf_congr fun o h1 h2 ↦ ?_
  obtain ⟨t, rfl⟩ : ∃ t, o = headerAt 8 + t := ⟨o - headerAt 8, by omega⟩
  have ht : t < headerBytes - 8 := by omega
  rw [hsig t ht, get!_sigOfX π ht]

end Lvm.VEq
