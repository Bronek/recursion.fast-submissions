-- New for lvm (WP-11b-QL): Q_link's BITS hypothesis — the position bits as BITS outputs — and the
-- `QIn.bits` it gives.
import LvmQLinkSound
import LvmQSigDefs

/-!
# The position bits as `BITS` outputs

`PosBits p lay v`: every position bit cell `bitBase p lay k + H·j + z` (opening `k`, position `j`,
bit `z`) is the `BITS` output `bit (n % 64)` of the stream lane `ansLane (pe + j/8) + n / 64`,
`n = (j mod 8)·H + z` (WP-12's `Out1`, the form `Q_sig`'s `SigBits` uses). **`qin_bits`**: with the
stream lanes in place, `PosBits` gives `QIn.bits` (the position bits are their answer's bits).
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Bits

/-- **Q_link's `BITS` outputs**: the position bits. -/
structure PosBits (p : Params) (lay : Layout) (v : Nat → FK) : Prop where
  bit : ∀ k < (opens p).length, ∀ j < ((opens p).getD k default).L.t,
    ∀ z < ((opens p).getD k default).L.height,
    Out1 v (lay.sb + ansLane p (((opens p).getD k default).pe + j / 8) +
        (j % 8 * ((opens p).getD k default).L.height + z) / 64)
      (.bit ((j % 8 * ((opens p).getD k default).L.height + z) % 64))
      (bitBase p lay k + ((opens p).getD k default).L.height * j + z)

theorem bit_word (x : UInt64) {z : Nat} (hz : z < 64) :
    w64 ((BOut.bit z).word x) = if x.toNat.testBit z then 1 else 0 := by
  have hs : (z.toUInt64).toNat % 64 = z := by rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  have e : ((BOut.bit z).word x).toNat = if x.toNat.testBit z then 1 else 0 := by
    simp only [BOut.word]
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hs, UInt64.toNat_one, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
    have := Nat.mod_lt (x.toNat / 2 ^ z) (show 0 < 2 by decide)
    by_cases h1 : x.toNat / 2 ^ z % 2 = 1
    · rw [if_pos (by simpa using h1)]; exact h1
    · rw [if_neg (by simpa using h1)]; omega
  split
  · show w64 _ = ⟨1⟩; congr 1; apply UInt64.toNat_inj.mp; rw [e, if_pos ‹_›]; rfl
  · show w64 _ = ⟨0⟩; congr 1; apply UInt64.toNat_inj.mp; rw [e, if_neg ‹_›]; rfl

section
variable {p : Params} {lay : Layout} {ws : List Word}

/-- An opening's positions answers: their bits lie in three lanes, inside the plan. -/
theorem open_pos_facts (hS : StreamOk p) (hQ : QOk p lay) {o : OpenInfo} (ho : o ∈ opens p) {j : Nat}
    (hj : j < o.L.t) :
    j % 8 * o.L.height + o.L.height ≤ 192 ∧ 1 ≤ o.pe + j / 8 ∧ o.pe + j / 8 < (plan p).length := by
  have hal := opens_al p ho
  obtain ⟨hp1, -, -, -, -⟩ := hQ.opens o ho
  have hx : j * (1 + o.L.path) + 1 < (openPlan o.L o.pe o.ce o.co).length := by
    rw [openPlan_length]; nlinarith
  have hi := hal.2 _ hx
  rw [openPlan_getD _ _ _ _ hj (by omega), if_neg (by omega)] at hi
  have hilt : o.i0 + (j * (1 + o.L.path) + 1) < (plan p).length := by have := hal.1; omega
  have he := streamOk_entry hS.1 hilt
  rw [hi] at he
  simp only [entryOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h192⟩, hlt⟩, h1⟩, -⟩ := he
  exact ⟨h192, h1, by omega⟩

/-- **`QIn.bits` from the `BITS` outputs.** -/
theorem qin_bits (hS : StreamOk p) (hQ : QOk p lay) {v : Nat → FK}
    (hs : ∀ L < 2 ^ lay.m, v (lay.sb + L) = laneK ws L) (hb : PosBits p lay v) :
    ∀ k < (opens p).length, ∀ j < ((opens p).getD k default).L.t, ∀ z < ((opens p).getD k default).L.height,
      v (bitBase p lay k + ((opens p).getD k default).L.height * j + z) =
        if ansBit p ws (((opens p).getD k default).pe + j / 8) (j % 8 * ((opens p).getD k default).L.height + z)
        then 1 else 0 := by
  intro k hk j hj z hz
  have hbit := hb.bit k hk j hj z hz
  have ho : (opens p).getD k default ∈ opens p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  generalize (opens p).getD k default = o at ho hj hz hbit ⊢
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hj
  have hin := lanes_in hS h1 hlt
  have hT := hQ.hT
  have hlane : ansLane p (o.pe + j / 8) + (j % 8 * o.L.height + z) / 64 < 2 ^ lay.m := by
    simp only [ansLane, if_neg (show o.pe + j / 8 ≠ 0 by omega)]; omega
  unfold Out1 at hbit
  rw [hbit, Nat.add_assoc, hs _ hlane, bit_word _ (Nat.mod_lt _ (by decide))]
  rfl

end

end Lvm.QLink
