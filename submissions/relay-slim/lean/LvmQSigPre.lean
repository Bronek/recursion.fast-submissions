import LvmQSigChain

/-!
# `Q_sig`: constants and the table `T[i] = i << 8`

New for lvm (WP-12). `gPre_spec`: in every memory where `gPre`'s rows hold, `Z = 0`, `O = 1` and
the cells `Tbase + i` hold `i << 8` (`i < 128`), the byte `i` a chain step's lane 1 carries.
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-- The doubling levels' values: level `d + 1` at index `q` is level `d` at `q / 2` plus bit
`q mod 2` at `x^{14 − d}`. -/
def tv : Nat → Nat → FK
  | 0, _ => 0
  | d + 1, q => tv d (q / 2) + (if q % 2 = 1 then w64 ((1 : UInt64) <<< (14 - d : Nat).toUInt64) else 0)

theorem tv_seven : ∀ q < 128, tv 7 q = w64 (q.toUInt64 <<< (8 : Nat).toUInt64) := by decide

theorem cell_lin1 (o : LoopOut) (t jf : Nat) (ht : t < o.tpl.length)
    (hw : ∀ r ∈ o.tpl, r.op ≠ .assert0 ∧ r.ty = .K) :
    (o.cell t jf).n = o.p.k + t + o.tpl.length * jf := by
  have hall : ∀ r ∈ o.tpl, LRow.w .K r = 1 := fun r hr => by
    obtain ⟨h1, h2⟩ := hw r hr
    obtain ⟨op, ty, args⟩ := r
    simp only at h1 h2; subst h2
    cases op <;> simp_all [LRow.w, Row.w, Row.writes]
  have hK : (o.tpl.getD t default).ty = .K := by
    rw [List.getD_eq_getElem _ _ ht]; exact (hw _ (List.getElem_mem ht)).2
  have hrank : lrank .K o.tpl t = t := by
    unfold lrank
    rw [List.map_congr_left (l := o.tpl.take t) (g := fun _ => 1)
      (fun r hr => hall r (List.mem_of_mem_take hr))]
    simp; omega
  have htw : ltw .K o.tpl = o.tpl.length := by
    unfold ltw
    rw [List.map_congr_left (g := fun _ => 1) hall]
    simp
  simp only [LoopOut.cell, hK, Ptr.at, hrank, htw]

/-- **One doubling level.** -/
theorem tlev_spec {c : Ctx} {M : Mem} {d : Nat} {src : Opd} {Zn : Nat} {p : Ptr}
    (h : SegsHold c M p (loop [d] (tTpl d src Zn) p).2) (hs : OpdK (loop [d] (tTpl d src Zn) p).1 src)
    (hZ : M.k Zn = 0) {q : Nat} (hq : q < 2 ^ (d + 1)) :
    M.k (p.k + q) = ov M (loop [d] (tTpl d src Zn) p).1 (q / 2) src +
      (if q % 2 = 1 then w64 ((1 : UInt64) <<< (14 - d : Nat).toUInt64) else 0) := by
  have hy : q / 2 < 2 ^ ([d].sum) := by simp; rw [pow_succ] at hq; omega
  have hZK : OpdK (loop [d] (tTpl d src Zn) p).1 (oA Zn) := rfl
  have hc : ∀ t < 2, ((loop [d] (tTpl d src Zn) p).1.cell t (q / 2)).n = p.k + t + 2 * (q / 2) :=
    fun t ht => cell_lin1 _ t _ (by simpa [loop_apply, tTpl] using ht)
      (fun r hr => by simp [loop_apply, tTpl] at hr; rcases hr with rfl | rfl <;> simp)
  rcases Nat.mod_two_eq_zero_or_one q with h0 | h1
  · have r := loopK_lin h hy (t := 0) (by simp [tTpl]) rfl hs hZK
    rw [hc 0 (by omega), ov_oA, hZ] at r
    rw [show p.k + q = p.k + 0 + 2 * (q / 2) by omega, r, h0]; simp
  · have r := loopK_lin h hy (t := 1) (by simp [tTpl]) rfl hs hZK
    rw [hc 1 (by omega), ov_oA, hZ] at r
    rw [show p.k + q = p.k + 1 + 2 * (q / 2) by omega, r, h1]; simp

end Lvm.QSig

namespace Lvm.QSig
open Lvm Lvm.Loop Lvm.Loop.Build

theorem const_K_spec {c : Ctx} {M : Mem} {p : Ptr} {k' : FK} {a : Nat}
    (h : SegsHold c M p (const .K k' (kc a) p).2) : M.k (const .K k' (kc a) p).1.n = k' := by
  have := linK_spec h
  simp only [const, lin, rowRes, Ptr.at] at this ⊢
  rw [this, one_mul, FK.add_self, zero_add]

/-- **Sequencing, hold only**: a postcondition of `m >>= f` from `m`'s rows and `f`'s at any pointer. -/
theorem seqH {α β : Type} {c : Ctx} {M : Mem} {m : BM α} {f : α → BM β} {p : Ptr} {Q : β → Prop}
    (h : SegsHold c M p ((m >>= f) p).2)
    (k : SegsHold c M p (m p).2 → ∀ p', SegsHold c M p' (f (m p).1 p').2 → Q (f (m p).1 p').1) :
    Q ((m >>= f) p).1 := by
  rw [hold_bind] at h
  rw [bind_apply]
  exact k h.1 _ h.2

/-- **Sequencing**: rows and assertions. -/
theorem seqHA {α β : Type} {c : Ctx} {M : Mem} {m : BM α} {f : α → BM β} {p : Ptr} {Q : β → Prop}
    (h : SegsHold c M p ((m >>= f) p).2) (hA : SegsAssert M p ((m >>= f) p).2)
    (k : SegsHold c M p (m p).2 → SegsAssert M p (m p).2 → ∀ p', SegsHold c M p' (f (m p).1 p').2 →
      SegsAssert M p' (f (m p).1 p').2 → Q (f (m p).1 p').1) :
    Q ((m >>= f) p).1 := by
  rw [hold_bind] at h
  rw [assert_bind] at hA
  rw [bind_apply]
  exact k h.1 hA.1 _ h.2 hA.2

/-- A doubling level read from the previous level's cells. -/
theorem tlev_next {c : Ctx} {M : Mem} {d : Nat} {b Zn : Nat} {p : Ptr}
    (h : SegsHold c M p (loop [d + 1] (tTpl (d + 1) (oS b 1) Zn) p).2) (hZ : M.k Zn = 0)
    (hprev : ∀ q < 2 ^ (d + 1), M.k (b + q) = tv (d + 1) q) :
    ∀ q < 2 ^ (d + 2), M.k (p.k + q) = tv (d + 2) q := by
  intro q hq
  rw [tlev_spec h rfl hZ hq, ov_oS _ _ rfl (by rw [pow_succ] at hq; omega), Nat.one_mul,
    hprev _ (by rw [pow_succ] at hq; omega)]
  rfl

/-- What `gPre` gives. -/
def PreOk (M : Mem) (r : Cell × Cell × List LoopOut) : Prop :=
  r.1.ty = .K ∧ r.2.1.ty = .K ∧ M.k r.1.n = 0 ∧ M.k r.2.1.n = 1 ∧
    ∀ i < 128, M.k (Tbase r + i) = w64 (i.toUInt64 <<< (8 : Nat).toUInt64)

theorem gPre_spec {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : SegsHold c M p (gPre I p).2) :
    PreOk M (gPre I p).1 := by
  unfold gPre at h ⊢
  refine seqH (Q := PreOk M) h fun hZ p1 h => ?_
  have eZ := const_K_spec hZ
  have tZ : (const .K 0 (kc I.flag) p).1.ty = .K := rfl
  generalize const .K 0 (kc I.flag) p = rZ at eZ tZ h ⊢
  refine seqH (Q := PreOk M) h fun hO p2 h => ?_
  have eO := const_K_spec hO
  have tO : (const .K 1 (kc I.flag) p1).1.ty = .K := rfl
  generalize const .K 1 (kc I.flag) p1 = rO at eO tO h ⊢
  refine seqH (Q := PreOk M) h fun h0 p3 h => ?_
  have e0 : ∀ q < 2 ^ 1, M.k (p2.k + q) = tv 1 q := fun q hq => by
    rw [tlev_spec h0 rfl eZ hq, ov_oA, eZ]; rfl
  replace e0 : ∀ q < 2 ^ 1, M.k ((loop [0] (tTpl 0 (oA rZ.1.n) rZ.1.n) p2).1.p.k + q) = tv 1 q := e0
  generalize loop [0] (tTpl 0 (oA rZ.1.n) rZ.1.n) p2 = r0 at e0 h ⊢
  refine seqH (Q := PreOk M) h fun h1 p4 h => ?_
  have e1 := tlev_next (d := 0) h1 eZ e0
  replace e1 : ∀ q < 2 ^ 2, M.k ((loop [1] (tTpl 1 (oS r0.1.p.k 1) rZ.1.n) p3).1.p.k + q) = tv 2 q := e1
  generalize loop [1] (tTpl 1 (oS r0.1.p.k 1) rZ.1.n) p3 = r1 at e1 h ⊢
  refine seqH (Q := PreOk M) h fun h2 p5 h => ?_
  have e2 := tlev_next (d := 1) h2 eZ e1
  replace e2 : ∀ q < 2 ^ 3, M.k ((loop [2] (tTpl 2 (oS r1.1.p.k 1) rZ.1.n) p4).1.p.k + q) = tv 3 q := e2
  generalize loop [2] (tTpl 2 (oS r1.1.p.k 1) rZ.1.n) p4 = r2 at e2 h ⊢
  refine seqH (Q := PreOk M) h fun h3 p6 h => ?_
  have e3 := tlev_next (d := 2) h3 eZ e2
  replace e3 : ∀ q < 2 ^ 4, M.k ((loop [3] (tTpl 3 (oS r2.1.p.k 1) rZ.1.n) p5).1.p.k + q) = tv 4 q := e3
  generalize loop [3] (tTpl 3 (oS r2.1.p.k 1) rZ.1.n) p5 = r3 at e3 h ⊢
  refine seqH (Q := PreOk M) h fun h4 p7 h => ?_
  have e4 := tlev_next (d := 3) h4 eZ e3
  replace e4 : ∀ q < 2 ^ 5, M.k ((loop [4] (tTpl 4 (oS r3.1.p.k 1) rZ.1.n) p6).1.p.k + q) = tv 5 q := e4
  generalize loop [4] (tTpl 4 (oS r3.1.p.k 1) rZ.1.n) p6 = r4 at e4 h ⊢
  refine seqH (Q := PreOk M) h fun h5 p8 h => ?_
  have e5 := tlev_next (d := 4) h5 eZ e4
  replace e5 : ∀ q < 2 ^ 6, M.k ((loop [5] (tTpl 5 (oS r4.1.p.k 1) rZ.1.n) p7).1.p.k + q) = tv 6 q := e5
  generalize loop [5] (tTpl 5 (oS r4.1.p.k 1) rZ.1.n) p7 = r5 at e5 h ⊢
  refine seqH (Q := PreOk M) h fun h6 p9 _ => ?_
  have e6 := tlev_next (d := 5) h6 eZ e5
  replace e6 : ∀ q < 2 ^ 7, M.k ((loop [6] (tTpl 6 (oS r5.1.p.k 1) rZ.1.n) p8).1.p.k + q) = tv 7 q := e6
  generalize loop [6] (tTpl 6 (oS r5.1.p.k 1) rZ.1.n) p8 = r6 at e6 ⊢
  refine ⟨tZ, tO, eZ, eO, fun i hi => ?_⟩
  show M.k (r6.1.p.k + i) = _
  rw [e6 i hi, tv_seven i hi]

end Lvm.QSig
