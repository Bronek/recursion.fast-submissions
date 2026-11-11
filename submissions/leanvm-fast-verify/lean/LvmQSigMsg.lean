import LvmQSigPre

/-!
# `Q_sig`: the message lanes as words

New for lvm (WP-12). For each message template of `LvmQSig`, in every memory where its rows hold
(and the zero cell is `0`), the lanes' words (`(M.k _).val`) are the `XOR`s of the operand words
and constants that `LvmWotsMsg`'s layout lemmas take as hypotheses.
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-- The word of a cell. -/
abbrev V (M : Mem) (a : Nat) : UInt64 := (M.k a).val

/-- The word of an operand at an iteration. -/
abbrev OV (M : Mem) (o : LoopOut) (jf : Nat) (x : Opd) : UInt64 := (ov M o jf x).val

section lanes

variable {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr} {jf t : Nat}

theorem lane1 (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {k' : FK} {a b : Opd} (hr : tpl.getD t default = lr 1 k' a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) {x y z : UInt64}
    (hx : OV M (loop dims tpl p).1 jf a = x) (hy : OV M (loop dims tpl p).1 jf b = y)
    (hz : k'.val = z) : V M ((loop dims tpl p).1.cell t jf).n = x ^^^ y ^^^ z := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr ha hb, one_mul, ← hx, ← hy, ← hz]; rfl

theorem lane1z (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {a b : Opd} (hr : tpl.getD t default = lr 1 0 a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) {x y : UInt64}
    (hx : OV M (loop dims tpl p).1 jf a = x) (hy : OV M (loop dims tpl p).1 jf b = y) :
    V M ((loop dims tpl p).1.cell t jf).n = x ^^^ y := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr ha hb, one_mul, add_zero, ← hx, ← hy]; rfl

theorem lane0 (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {k' : FK} {a b : Opd} (hr : tpl.getD t default = lr 0 k' a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) {x z : UInt64}
    (hx : OV M (loop dims tpl p).1 jf a = x) (hz : k'.val = z) :
    V M ((loop dims tpl p).1.cell t jf).n = x ^^^ z := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr ha hb, zero_mul, add_zero, ← hx, ← hz]; rfl

theorem lane00 (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {a b : Opd} (hr : tpl.getD t default = lr 0 0 a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) {x : UInt64}
    (hx : OV M (loop dims tpl p).1 jf a = x) : V M ((loop dims tpl p).1.cell t jf).n = x := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr ha hb, zero_mul, add_zero, add_zero, ← hx]

theorem laneZ {Zn : Nat} (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) (hr : tpl.getD t default = lr 0 0 (oA Zn) (oA Zn)) (hZ : M.k Zn = 0) :
    V M ((loop dims tpl p).1.cell t jf).n = 0 := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr rfl rfl, ov_oA, hZ, zero_mul, add_zero, add_zero]; rfl

theorem lanePad {Zn : Nat} (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) (hr : tpl.getD t default = padLane Zn) (hZ : M.k Zn = 0) :
    V M ((loop dims tpl p).1.cell t jf).n = 0x8000000000000000 := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr rfl rfl, ov_oA, hZ, zero_mul, add_zero, zero_add]

end lanes

theorem ovS_V {M : Mem} {o : LoopOut} {d jf n s n2 : Nat} (hd : o.dims = [d]) (hjf : jf < 2 ^ d)
    (h : n + s * jf = n2) : OV M o jf (oS n s) = V M n2 := by
  subst h; simp only [OV, V, ov_oS M o hd hjf]

/-- **A chain step's lanes** (template `stepsTpl`, step `s < 3`, lanes `17 s + l`). -/
theorem steps_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {I : SigIn} {Zn : Nat} {T : Opd}
    {c1 : Nat → UInt64} {xb st : Nat}
    (h : SegsHold c M p (loop dims (stepsTpl I Zn T c1 xb st) p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) (hT : OpdK (loop dims (stepsTpl I Zn T c1 xb st) p).1 T)
    (hZ : M.k Zn = 0) {s : Nat} (hs : s < 3) :
    let o := (loop dims (stepsTpl I Zn T c1 xb st) p).1
    let L := fun l => V M (o.cell (17 * s + l) jf).n
    let X := fun k => OV M o jf (oS (xb + 8 * s + k) st)
    L 0 = V M I.bi ^^^ 0x57 ∧ L 1 = (OV M o jf T ^^^ X 0) ^^^ c1 s ∧
      (∀ k, 1 ≤ k → k < 4 → L (k + 1) = X (2 * k - 1) ^^^ X (2 * k)) ∧
      L 5 = X 7 ^^^ 0x1000000 ∧ (∀ l, 6 ≤ l → l < 16 → L l = 0) ∧ L 16 = 0x8000000000000000 := by
  dsimp only
  have hlen : (stepsTpl I Zn T c1 xb st).length = 51 := by simp [stepsTpl, stepLanes, zeroLanes]
  refine ⟨?_, ?_, fun k hk1 hk2 => ?_, ?_, fun l hl1 hl2 => ?_, ?_⟩
  · interval_cases s <;> apply lane0 h hjf <;>
      first | (rw [hlen]; omega) | rfl
  · interval_cases s <;> apply lane1 h hjf <;>
      first | (rw [hlen]; omega) | rfl | assumption
  · interval_cases s <;> interval_cases k <;> apply lane1z h hjf <;>
      first | (rw [hlen]; omega) | rfl
  · interval_cases s <;> apply lane0 h hjf <;>
      first | (rw [hlen]; omega) | rfl
  · interval_cases s <;> interval_cases l <;> apply laneZ h hjf (hZ := hZ) <;>
      first | (rw [hlen]; omega) | rfl
  · interval_cases s <;> apply lanePad h hjf (hZ := hZ) <;> first | (rw [hlen]; omega) | rfl

/-- **Two digests after a tag** (template `twoLanes`). -/
theorem two_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {Zn : Nat} {tag : UInt64}
    {aB bB st : Nat} (h : SegsHold c M p (loop dims (twoLanes Zn tag aB bB st) p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) (hZ : M.k Zn = 0) :
    let o := (loop dims (twoLanes Zn tag aB bB st) p).1
    let L := fun l => V M (o.cell l jf).n
    let A := fun k => OV M o jf (oS (aB + k) st)
    let B := fun k => OV M o jf (oS (bB + k) st)
    L 0 = A 0 ^^^ tag ∧ (∀ k, 1 ≤ k → k < 4 → L k = A (2 * k - 1) ^^^ A (2 * k)) ∧
      L 4 = A 7 ^^^ B 0 ∧ (∀ k, 1 ≤ k → k < 4 → L (4 + k) = B (2 * k - 1) ^^^ B (2 * k)) ∧
      L 8 = B 7 ^^^ 0x100 ∧ (∀ l, 9 ≤ l → l < 16 → L l = 0) ∧ L 16 = 0x8000000000000000 := by
  dsimp only
  have hlen : (twoLanes Zn tag aB bB st).length = 17 := by simp [twoLanes, zeroLanes]
  refine ⟨?_, fun k hk1 hk2 => ?_, ?_, fun k hk1 hk2 => ?_, ?_, fun l hl1 hl2 => ?_, ?_⟩
  · apply lane0 h hjf <;> first | (rw [hlen]; omega) | rfl
  · interval_cases k <;> apply lane1z h hjf <;> first | (rw [hlen]; omega) | rfl
  · apply lane1z h hjf <;> first | (rw [hlen]; omega) | rfl
  · interval_cases k <;> apply lane1z h hjf <;> first | (rw [hlen]; omega) | rfl
  · apply lane0 h hjf <;> first | (rw [hlen]; omega) | rfl
  · interval_cases l <;> apply laneZ h hjf (hZ := hZ) <;> first | (rw [hlen]; omega) | rfl
  · apply lanePad h hjf (hZ := hZ) <;> first | (rw [hlen]; omega) | rfl

/-- **`leafStmt`'s lanes** (template `leafStmtLanes`). -/
theorem leafStmt_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {I : SigIn} {Zn : Nat}
    (h : SegsHold c M p (loop dims (leafStmtLanes I Zn) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hZ : M.k Zn = 0) :
    let o := (loop dims (leafStmtLanes I Zn) p).1
    let L := fun l => V M (o.cell l jf).n
    L 0 = V M I.bh ^^^ 0x4C ∧ (∀ k, 1 ≤ k → k < 4 → L k = V M (I.bh + 2 * k - 1) ^^^ V M (I.bh + 2 * k)) ∧
      L 4 = V M (I.bh + 7) ^^^ V M I.bn ∧ L 5 = V M (I.bn + 1) ^^^ 0x100 ∧
      (∀ l, 6 ≤ l → l < 16 → L l = 0) ∧ L 16 = 0x8000000000000000 := by
  dsimp only
  have hlen : (leafStmtLanes I Zn).length = 17 := by simp [leafStmtLanes, zeroLanes]
  refine ⟨?_, fun k hk1 hk2 => ?_, ?_, ?_, fun l hl1 hl2 => ?_, ?_⟩
  · apply lane0 h hjf <;> first | (rw [hlen]; omega) | rfl
  · interval_cases k <;> apply lane1z h hjf <;> first | (rw [hlen]; omega) | rfl
  · apply lane1z h hjf <;> first | (rw [hlen]; omega) | rfl
  · apply lane0 h hjf <;> first | (rw [hlen]; omega) | rfl
  · interval_cases l <;> apply laneZ h hjf (hZ := hZ) <;> first | (rw [hlen]; omega) | rfl
  · apply lanePad h hjf (hZ := hZ) <;> first | (rw [hlen]; omega) | rfl

/-- **The key leaf's lanes 0, 1** (template `leafA`). -/
theorem leafA_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {I : SigIn}
    (h : SegsHold c M p (loop dims (leafA I) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    V M ((loop dims (leafA I) p).1.cell 0 jf).n = V M I.bi ^^^ 0x4B ∧
      V M ((loop dims (leafA I) p).1.cell 1 jf).n = V M I.be := by
  have hlen : (leafA I).length = 2 := rfl
  constructor
  · apply lane0 h hjf <;> first | (rw [hlen]; omega) | rfl
  · apply lane00 h hjf <;> first | (rw [hlen]; omega) | rfl

/-- **The key leaf's lanes `2 + m`** (template `leafB`, loop over `m < 512`). -/
theorem leafB_spec {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn}
    (h : SegsHold c M p (loop [9] (leafB I) p).2) {m : Nat} (hm : m < 2 ^ 9) :
    V M ((loop [9] (leafB I) p).1.cell 0 m).n = V M (I.be + 2 * m + 1) ^^^ V M (I.be + 2 * (m + 1)) := by
  have hm' : m < 2 ^ [9].sum := by simpa using hm
  apply lane1z h hm' (by simp [leafB]) rfl
  · rfl
  · rfl
  · exact ovS_V rfl hm (by omega)
  · exact ovS_V rfl hm (by omega)

/-- **The key leaf's lanes 514 … 543** (template `leafC`, row `k` = lane `514 + k`). -/
theorem leafC_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {I : SigIn} {Zn : Nat}
    (h : SegsHold c M p (loop dims (leafC I Zn) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hZ : M.k Zn = 0) :
    let L := fun k => V M ((loop dims (leafC I Zn) p).1.cell k jf).n
    (∀ k < 19, L k = V M (I.be + 2 * (512 + k) + 1) ^^^ V M (I.be + 2 * (513 + k))) ∧
      L 19 = V M (I.be + 2 * 531 + 1) ^^^ 0x100 ∧ (∀ k, 20 ≤ k → k < 29 → L k = 0) ∧
      L 29 = 0x8000000000000000 := by
  dsimp only
  have hlen : (leafC I Zn).length = 30 := by simp [leafC, zeroLanes]
  refine ⟨fun k hk => ?_, ?_, fun k hk1 hk2 => ?_, ?_⟩
  · interval_cases k <;> apply lane1z h hjf <;> first | (rw [hlen]; omega) | rfl
  · apply lane0 h hjf <;> first | (rw [hlen]; omega) | rfl
  · interval_cases k <;> apply laneZ h hjf (hZ := hZ) <;> first | (rw [hlen]; omega) | rfl
  · apply lanePad h hjf (hZ := hZ) <;> first | (rw [hlen]; omega) | rfl

end Lvm.QSig
