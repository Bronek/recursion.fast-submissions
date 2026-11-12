import LvmQSigSig
import LvmQSigChild
import LvmQSigXs

/-!
# `Q_sig` is sound (BLUEPRINT §4.6, §11 A2, A3)

New for lvm (WP-12). **`qsig_sound`** (the theorem WP-14 consumes): `LvmQSigDefs` states the
hypotheses (`SigKS`, `SigBits`) and the conclusions (`SigOk`, `ChildOk`). **`qsig_sound_in`**: the
same with the `KS` hypothesis on the message input array `I.xs` (`SigKSin`, decision A19), which
`Q_sig` asserts equal to its message lanes (`LvmQSigXs`).
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build

/-- **`Q_sig` is sound.** -/
theorem qsig_sound {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKS I (qsig I p).1 M.k) (hbits : SigBits I (qsig I p).1 M.k)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true ∧ ChildOk I M.k :=
  ⟨qsig_sigOk h hg hks hbits hinj, qsig_child hln h hg hks hbits⟩

/-- **`Q_sig` is sound, `KS` on the input array** (A19). -/
theorem qsig_sound_in {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKSin I M.k) (hbits : SigBits I (qsig I p).1 M.k)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true ∧ ChildOk I M.k :=
  qsig_sound hln h hg (sigKS_of_in h hg hks) hbits hinj

end Lvm.QSig
