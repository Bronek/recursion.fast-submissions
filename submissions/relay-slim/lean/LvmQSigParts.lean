import LvmQSigHdr
import LvmQSigCheck
import LvmQSigMsg

/-!
# `Q_sig`: its parts

New for lvm (WP-12). `qsig_parts`, `gMsg_parts`: where `Q_sig`'s rows and assertions hold, every
part's rows and assertions hold at some pointer, and its output is the field of `Q_sig`'s output
that names it (the frame property of QL's builder: specs are pointer-generic).
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

theorem ok_bind' {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Ok c M (m >>= f) p) :
    Ok c M m p ∧ Ok c M (f (m p).1) (p.adv (m p).2) ∧
      ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := by
  obtain ⟨h1, h2⟩ := h
  rw [hold_bind] at h1; rw [assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩, rfl⟩

/-- A default loop output (for `getD`). -/
def dLoop : LoopOut := ⟨⟨0, 0⟩, [], []⟩

theorem ok_seqAll_get {c : Ctx} {M : Mem} :
    ∀ (ms : List (BM LoopOut)) (p : Ptr), Ok c M (seqAll ms) p →
      ∀ u < ms.length, ∃ q, Ok c M (ms.getD u (pure dLoop)) q ∧
        (seqAll ms p).1.getD u dLoop = ((ms.getD u (pure dLoop)) q).1
  | [], _, _, u, hu => absurd hu (by simp)
  | m :: ms, p, h, u, hu => by
    obtain ⟨h1, h2⟩ := h
    rw [seqAll_cons_apply, segsHold_append, segsHold_append] at h1
    rw [seqAll_cons_apply, segsAssert_append, segsAssert_append] at h2
    cases u with
    | zero => exact ⟨p, ⟨h1.1, h2.1⟩, by simp [seqAll_cons_apply]⟩
    | succ u =>
      obtain ⟨q, hq, e⟩ := ok_seqAll_get ms _ ⟨h1.2.1, h2.2.1⟩ u (by simpa using hu)
      refine ⟨q, by simpa using hq, ?_⟩
      simp only [seqAll_cons_apply, List.getD_cons_succ]
      exact e

theorem ok_forN_get {c : Ctx} {M : Mem} {n : Nat} {f : Nat → BM LoopOut} {p : Ptr}
    (h : Ok c M (forN n f) p) : ∀ u < n, ∃ q, Ok c M (f u) q ∧ (forN n f p).1.getD u dLoop = (f u q).1 := by
  intro u hu
  obtain ⟨q, hq, e⟩ := ok_seqAll_get _ p h u (by simpa using hu)
  have hg : ((List.range n).map f).getD u (pure dLoop) = f u := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu)]; simp
  rw [hg] at hq e
  exact ⟨q, hq, e⟩

set_option maxRecDepth 100000 in
/-- **The parts of `Q_sig`.** -/
theorem qsig_parts {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p) :
    let o := (qsig I p).1
    (∃ q, Ok c M (gPre I) q ∧ (gPre I q).1 = o.pre) ∧
    (∃ q, Ok c M (loop [7] (chainM I o.pre.1.n o.pre.2.1.n)) q ∧
      (loop [7] (chainM I o.pre.1.n o.pre.2.1.n) q).1 = o.cm) ∧
    (∀ u < 5, ∃ q, Ok c M (loop [] (chainC I o.pre.1.n o.pre.2.1.n u)) q ∧
      (loop [] (chainC I o.pre.1.n o.pre.2.1.n u) q).1 = o.cc.getD u dLoop) ∧
    (∃ q, Ok c M (gCheck I o.pre.1 o.pre.2.1) q) ∧
    (∃ q, Ok c M (loop [4] (pathTpl I)) q ∧ (loop [4] (pathTpl I) q).1 = o.pa) ∧
    (∃ q, Ok c M (header I o.pre.1 o.pre.2.1) q) ∧
    (∃ q, Ok c M (assert0 (kc (I.bi + 17)) (kc I.flag)) q) ∧
    (∃ q, Ok c M (gSl I) q) ∧
    (∃ q, Ok c M (gMsg I o.pre.1.n (Tbase o.pre)) q ∧ (gMsg I o.pre.1.n (Tbase o.pre) q).1 = o.msg) := by
  unfold qsig at h ⊢
  intro o
  obtain ⟨o1, h, e1⟩ := ok_bind' h
  obtain ⟨o2, h, e2⟩ := ok_bind' h
  obtain ⟨o3, h, e3⟩ := ok_bind' h
  obtain ⟨o4, h, e4⟩ := ok_bind' h
  obtain ⟨o5, h, e5⟩ := ok_bind' h
  obtain ⟨o6, h, e6⟩ := ok_bind' h
  obtain ⟨o7, h, e7⟩ := ok_bind' h
  obtain ⟨o8, h, e8⟩ := ok_bind' h
  obtain ⟨o9, h, e9⟩ := ok_bind' h
  obtain ⟨o10, h, e10⟩ := ok_bind' h
  refine ⟨⟨_, o1, rfl⟩, ⟨_, o2, rfl⟩, fun u hu => ?_, ⟨_, o4⟩, ⟨_, o5, rfl⟩, ⟨_, o6⟩, ⟨_, o7⟩,
    ⟨_, o8⟩, ⟨_, o10, ?_⟩⟩
  · obtain ⟨q, hq, e⟩ := ok_forN_get o3 u hu
    exact ⟨q, hq, e.symm⟩
  -- `o.msg` through the bind equations (a bare `rfl` makes the kernel unfold the whole builder: 16 s).
  have E := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans e10))))))))
  rw [show o.pre = (gPre I p).1 from congrArg SigOut.pre E]
  exact (congrArg SigOut.msg E).symm

/-- **The parts of the message gadget.** -/
theorem gMsg_parts {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {Zn Tb : Nat}
    (h : Ok c M (gMsg I Zn Tb) p) :
    let o := (gMsg I Zn Tb p).1
    (∃ q, Ok c M (loop [7] (stepsTpl I Zn (oS Tb 1) (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24)) q ∧
      (loop [7] (stepsTpl I Zn (oS Tb 1) (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) q).1 = o.xm) ∧
    (∀ u < 5, ∃ q, Ok c M (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0)) q ∧
      (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) q).1 = o.xc.getD u dLoop) ∧
    (∃ q, Ok c M (loop [] (leafA I)) q ∧ (loop [] (leafA I) q).1 = o.la) ∧
    (∃ q, Ok c M (loop [9] (leafB I)) q ∧ (loop [9] (leafB I) q).1 = o.lb) ∧
    (∃ q, Ok c M (loop [] (leafC I Zn)) q ∧ (loop [] (leafC I Zn) q).1 = o.lc) ∧
    (∃ q, Ok c M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16)) q ∧
      (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) q).1 = o.xp) ∧
    (∃ q, Ok c M (loop [] (leafStmtLanes I Zn)) q ∧ (loop [] (leafStmtLanes I Zn) q).1 = o.xls) ∧
    (∃ q, Ok c M (loop [] (twoLanes Zn 0x4E I.bcl I.bls 0)) q ∧
      (loop [] (twoLanes Zn 0x4E I.bcl I.bls 0) q).1 = o.xns) := by
  unfold gMsg at h ⊢
  intro o
  obtain ⟨o1, h, e1⟩ := ok_bind' h
  obtain ⟨o2, h, e2⟩ := ok_bind' h
  obtain ⟨o3, h, e3⟩ := ok_bind' h
  obtain ⟨o4, h, e4⟩ := ok_bind' h
  obtain ⟨o5, h, e5⟩ := ok_bind' h
  obtain ⟨o6, h, e6⟩ := ok_bind' h
  obtain ⟨o7, h, e7⟩ := ok_bind' h
  obtain ⟨o8, h, e8⟩ := ok_bind' h
  refine ⟨⟨_, o1, rfl⟩, fun u hu => ?_, ⟨_, o3, rfl⟩, ⟨_, o4, rfl⟩, ⟨_, o5, rfl⟩, ⟨_, o6, rfl⟩,
    ⟨_, o7, rfl⟩, ⟨_, o8, rfl⟩⟩
  obtain ⟨q, hq, e⟩ := ok_forN_get o2 u hu
  exact ⟨q, hq, e.symm⟩

end Lvm.QSig
