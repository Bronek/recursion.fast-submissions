import LvmQSig

/-!
# `Q_sig`: what the loop templates compute

New for lvm (WP-12). Per template of `LvmQSig`, in every memory where its rows hold:
* `chain_spec`: a WOTS chain's step inputs and end are the mux of `[d < s]` (FR `wots_chain_sound`'s
  `hsel`/`hend` hypotheses);
* `csf_spec`: the checksum factor is `x^{3 − d}`; `pt_spec`: a product-tree level; `t_spec`: a
  doubling level of `T`;
* `path_spec`: the path mux orders `(cur, sib)` by the index bit.
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-- The value of row `t`'s cell at iteration `jf` of a loop. -/
abbrev cv (M : Mem) (o : LoopOut) (t jf : Nat) : FK := M.k (o.cell t jf).n

/-- A Boolean `K` value as a number. -/
def bnat (b : FK) : Nat := if b = 1 then 1 else 0

theorem FK.one_add_one : (1 : FK) + 1 = 0 := FK.add_self 1

theorem mux_eq {s a b : FK} (hs : s = 0 ∨ s = 1) :
    s * (a + b) + b = if s = 1 then a else b := by
  rcases hs with rfl | rfl
  · simp [show ¬ ((0 : FK) = 1) from by decide]
  · simp only [one_mul, if_true]; rw [add_assoc, FK.add_self, add_zero]

section chain

variable {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {d0 d1 Z O : Opd}
  {ots o1 o2 o3 : Nat → Opd}

/-- **One WOTS chain**: with Boolean digit bits `b₀, b₁` (`d = b₀ + 2 b₁`), lane `l`'s step-2 input
is `out₁` if `d < 1`, its step-3 input `out₂` if `d < 2`, its end `out₃` if `d < 3`, else the signed
value `ots`. -/
theorem chain_spec
    (h : SegsHold c M p (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).2)
    {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hK : ∀ x ∈ [d0, d1, Z, O], OpdK (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 x)
    (hKl : ∀ l < 4, ∀ x ∈ [ots l, o1 l, o2 l, o3 l],
      OpdK (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 x)
    (hZ : ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf Z = 0)
    (hO : ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf O = 1)
    {b0 b1 : FK} (hv0 : ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf d0 = b0)
    (hv1 : ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf d1 = b1)
    (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1) {l : Nat} (hl : l < 4) :
    cv M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 (8 + l) jf =
        (if bnat b0 + 2 * bnat b1 < 1 then ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (o1 l)
          else ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (ots l)) ∧
      cv M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 (16 + l) jf =
        (if bnat b0 + 2 * bnat b1 < 2 then ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (o2 l)
          else ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (ots l)) ∧
      cv M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 (24 + l) jf =
        (if bnat b0 + 2 * bnat b1 < 3 then ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (o3 l)
          else ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (ots l)) := by
  set o := (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 with ho
  have hlen : (chainTpl d0 d1 Z O ots o1 o2 o3).length = 28 := by simp [chainTpl]
  have hcur : ∀ t < 28, OpdK o (.cur t) := fun t ht => by
    show ((chainTpl d0 d1 Z O ots o1 o2 o3).getD t default).ty = .K
    interval_cases t <;> rfl
  have ovc : ∀ t < 28, ov M o jf (.cur t) = cv M o t jf := fun t ht =>
    ov_cur M o hjf t (hcur t ht)
  have hd0 := hK d0 (by simp); have hd1 := hK d1 (by simp)
  have hZK := hK Z (by simp); have hOK := hK O (by simp)
  obtain ⟨hots, ho1, ho2, ho3⟩ : OpdK o (ots l) ∧ OpdK o (o1 l) ∧ OpdK o (o2 l) ∧ OpdK o (o3 l) :=
    ⟨hKl l hl _ (by simp), hKl l hl _ (by simp), hKl l hl _ (by simp), hKl l hl _ (by simp)⟩
  have r0 := loopK_lin h hjf (t := 0) (by omega) rfl hd0 hd0
  have r1 := loopK_lin h hjf (t := 1) (by omega) rfl hd1 hd1
  have r2 := loopK_mad h hjf (t := 2) (by omega) rfl (hcur 0 (by omega)) (hcur 1 (by omega)) hZK
  have r3 := loopK_mad h hjf (t := 3) (by omega) rfl hd0 hd1 hOK
  have g4 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (4 + l) default = lr 1 0 (o1 l) (ots l) := by
    interval_cases l <;> rfl
  have g8 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (8 + l) default = mr (.cur 2) (.cur (4 + l)) (ots l) := by
    interval_cases l <;> rfl
  have g12 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (12 + l) default = lr 1 0 (o2 l) (ots l) := by
    interval_cases l <;> rfl
  have g16 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (16 + l) default =
      mr (.cur 1) (.cur (12 + l)) (ots l) := by
    interval_cases l <;> rfl
  have g20 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (20 + l) default = lr 1 0 (o3 l) (ots l) := by
    interval_cases l <;> rfl
  have g24 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (24 + l) default =
      mr (.cur 3) (.cur (20 + l)) (ots l) := by
    interval_cases l <;> rfl
  have r4 := loopK_lin h hjf (by omega) g4 ho1 hots
  have r8 := loopK_mad h hjf (by omega) g8 (hcur 2 (by omega)) (hcur _ (by omega)) hots
  have r12 := loopK_lin h hjf (by omega) g12 ho2 hots
  have r16 := loopK_mad h hjf (by omega) g16 (hcur 1 (by omega)) (hcur _ (by omega)) hots
  have r20 := loopK_lin h hjf (by omega) g20 ho3 hots
  have r24 := loopK_mad h hjf (by omega) g24 (hcur 3 (by omega)) (hcur _ (by omega)) hots
  simp only [← ho] at r0 r1 r2 r3 r4 r8 r12 r16 r20 r24
  simp only [one_mul, zero_mul, add_zero] at r0 r1 r4 r12 r20
  have e2 := ovc 2 (by omega); have e1 := ovc 1 (by omega); have e3 := ovc 3 (by omega)
  have e0 := ovc 0 (by omega); have e4 := ovc (4 + l) (by omega)
  have e12 := ovc (12 + l) (by omega); have e20 := ovc (20 + l) (by omega)
  simp only [cv] at e0 e1 e2 e3 e4 e12 e20 ⊢
  rw [e0, e1, hZ, add_zero] at r2
  rw [hO] at r3
  rw [e2, e4, r2, r0, r1, r4] at r8
  rw [e1, e12, r1, r12] at r16
  rw [e3, e20, r3, r20] at r24
  rw [r8, r16, r24]
  rw [hv0, hv1] at *
  have h10 : ¬ ((1 : FK) = 0) := by decide
  have h01 : ¬ ((0 : FK) = 1) := by decide
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;>
    simp [bnat, h01, FK.one_add_one, add_assoc, FK.add_self]

end chain

end Lvm.QSig
