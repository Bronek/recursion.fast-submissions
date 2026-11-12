import LvmQSigSigAux

/-!
# `Q_sig`: the child's signature (`SigOk`)

New for lvm (WP-12). See `LvmQSigDefs` for the hypotheses. FR's `wots_sound` with the chains
(`chain_end` of `step_m`/`step_c` and `sel_m`/`sel_c`), the key leaf (`leaf_digest`), the path
(`node_digest`, `path_spec`) and the root check of `header_spec`; helpers in `LvmQSigSigAux`.
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.KSponge Lvm.Wots
open Lvm.QSig.SigH

/-- **The child's signature** (the one WOTS walk, A2). -/
theorem qsig_sigOk {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKS I (qsig I p).1 M.k) (hbits : SigBits I (qsig I p).1 M.k)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true := by
  obtain ⟨⟨q1, hpre, epre⟩, ⟨q2, hcm, ecm⟩, hcc, ⟨q4, hck⟩, ⟨q5, hpa, epa⟩, ⟨q6, hhd⟩, ⟨q7, has⟩, -,
    ⟨q9, hmsg, emsg⟩⟩ := qsig_parts h
  obtain ⟨⟨r1, hxm, exm⟩, hxc, ⟨r3, hla, ela⟩, ⟨r4, hlb, elb⟩, ⟨r5, hlc, elc⟩, ⟨r6, hxp, exp⟩, -, -⟩ :=
    gMsg_parts hmsg
  rw [emsg] at exm hxc ela elb elc exp
  have pre := gPre_spec hpre.1
  rw [epre] at pre
  obtain ⟨hZt, hOt, hZ, hO, hT⟩ := pre
  clear h hpre epre hmsg emsg
  generalize (qsig I p).1 = o at *
  have hj := idx_lt has hg hbits
  have hbd : ∀ q < 256, M.k (I.bd + q) = 0 ∨ M.k (I.bd + q) = 1 := fun q hq => by
    rw [hbits.md q hq]; exact bit_bool _ (Nat.mod_lt _ (by norm_num))
  have hbc : ∀ k < 10, M.k (I.bc + k) = 0 ∨ M.k (I.bc + k) = 1 := by
    obtain ⟨w, hw⟩ := hbits.cs
    exact fun k hk => by rw [hw k hk]; exact bit_bool w (by omega)
  have hx := gCheck_spec hZt hOt hck.1 hck.2 hg hZ hO hbd hbc
  rw [range_mdig hbits] at hx
  have hC := checksum_of_pow _ _ hinj hx
  have hdr := header_spec hZt hOt hhd.1 hhd.2 hg hZ hO
  refine wots_sound (σ := sigAt' M.k I.sg) hj (by simp [sigAt']) (by simp [sigAt'])
    (ends := (List.range wotsLen).map fun i => digOfW (lanesW M.k (endc o i))) (by simp)
    (fun i hi => ?_) (cur := fun t => digAt M.k (I.yc + 4 * t)) ?_ (fun t ht => ?_) ?_
  · -- one chain
    simp only [sigAt', List.getElem_map, List.getElem_range]
    by_cases hi' : i < 128
    · rw [wdig_lt _ hi', ← mdig_eq hbits hi']
      obtain ⟨hm, he⟩ := sel_m hcm.1 ecm hZ hO hbd hi'
      have hle : mdig M I i ≤ 3 := by
        unfold mdig; have := bnat_le (M.k (I.bd + 2 * i)); have := bnat_le (M.k (I.bd + 2 * i + 1))
        omega
      exact chain_end hle (fun s hs => step_m hks hbits hZ hT hj hxm.1 exm hi' hs) hm he
    · obtain ⟨u, rfl⟩ : ∃ u, i = 128 + u := ⟨i - 128, by omega⟩
      have hu : u < 5 := by simp [wotsLen] at hi; omega
      rw [← cdig_eq _ hC hu]
      obtain ⟨q, hq, eq⟩ := hcc u hu
      obtain ⟨r, hr, er⟩ := hxc u hu
      obtain ⟨hm, he⟩ := sel_c hq.1 eq hZ hO hbc hu
      have hle : cdig M I u ≤ 3 := by
        unfold cdig; have := bnat_le (M.k (I.bc + 2 * u)); have := bnat_le (M.k (I.bc + 2 * u + 1))
        omega
      exact chain_end hle (fun s hs => step_c hks hbits hZ hj hu hr.1 er hs) hm he
  · -- the leaf
    show digAt M.k (I.yc + 4 * 0) = _
    rw [Nat.mul_zero, Nat.add_zero]
    exact leaf_digest hks hbits hZ hj hla.1 ela hlb.1 elb hlc.1 elc
  · -- the walk
    have ht' : t < 16 := by simpa [sigAt', sigHeight] using ht
    show digAt M.k (I.yc + 4 * (t + 1)) = _
    rw [node_digest hks hbits hZ hxp.1 exp ht']
    have hb := hbits.idx_bit t ht'
    unfold Out1 at hb
    have hbool : M.k (I.bi + 1 + t) = 0 ∨ M.k (I.bi + 1 + t) = 1 := by
      rw [hb]; exact bit_bool _ (by omega)
    have hA : (digOfW fun l => (M.k (o.pa.cell (4 + l) t).n).val) =
        if M.k (I.bi + 1 + t) = 1 then digAt M.k (I.sg + 533 + 4 * t) else digAt M.k (I.yc + 4 * t) :=
      digOfW_ite fun l hl => by
        rw [← epa, (path_spec hpa.1 ht' hl hbool).1]
        split_ifs <;> exact kval_congr M (by omega)
    have hB : (digOfW fun l => (M.k (o.pa.cell (8 + l) t).n).val) =
        if M.k (I.bi + 1 + t) = 1 then digAt M.k (I.yc + 4 * t) else digAt M.k (I.sg + 533 + 4 * t) :=
      digOfW_ite fun l hl => by
        rw [← epa, (path_spec hpa.1 ht' hl hbool).2]
        split_ifs <;> exact kval_congr M (by omega)
    have key : M.k (I.bi + 1 + t) = 1 ↔ ¬ ((M.k I.sg).val.toNat / 2 ^ t % 2 = 0) := by
      rw [hb, w64_bit _ (by omega), ubit_testBit, Nat.testBit_eq_decide_div_mod_eq]
      have h01 : ¬ ((0 : FK) = 1) := by decide
      by_cases hq : (M.k I.sg).val.toNat / 2 ^ t % 2 = 1
      · simp [hq]
      · simp [hq, h01]
    simp only [sigAt', List.getElem_map, List.getElem_range]
    rw [hA, hB]
    by_cases hc : M.k (I.bi + 1 + t) = 1
    · have := key.mp hc
      simp only [hc, ↓reduceIte, this]
    · have : (M.k I.sg).val.toNat / 2 ^ t % 2 = 0 := by
        by_contra hn; exact hc (key.mpr hn)
      simp only [hc, ↓reduceIte, this]
  · -- the root
    show digAt M.k (I.yc + 4 * 16) = digAt M.k I.vk
    unfold digAt
    exact digOfW_congr fun l hl => by
      rw [show I.yc + 4 * 16 + l = I.yc + 64 + l by ring, hdr.2.1 l hl]

end Lvm.QSig
