import LvmQSigDefs

/-!
# `Q_sig`: the child's header checks (`ChildOk`)

New for lvm (WP-12). See `LvmQSigDefs` for the hypotheses.
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.KSponge Lvm.Wots

/-! ## Helpers -/

theorem out1_val {v : Nat → FK} {w : Nat} {b : BOut} {c : Nat} (h : Out1 v w b c) :
    (v c).val = b.word (v w).val := by rw [h]

theorem digAt_congr {v : Nat → FK} {a b : Nat} (h : ∀ l < 4, v (a + l) = v (b + l)) :
    digAt v a = digAt v b := by
  unfold digAt digOfW
  congr 1; funext k
  dsimp only
  rw [h (k.val / 8) (by omega)]

theorem digAt_zero {v : Nat → FK} {a : Nat} (h : ∀ l < 4, v (a + l) = 0) : digAt v a = zeroDig := by
  apply Vector.ext; intro k hk
  rw [digAt, digOfW_get _ hk, h _ (by omega)]
  simp only [zeroDig, Vector.getElem_replicate]
  exact byteW_zero _

theorem ov_oS_nil (M : Mem) (o : LoopOut) (hd : o.dims = []) (n s : Nat) :
    ov M o 0 (oS n s) = M.k n := by
  simp [ov, Opd.resolve, Addr.at, dot, hd, unflat]

theorem w64_inj {a b : UInt64} (h : w64 a = w64 b) : a = b := congrArg FK.val h

/-- `n'`'s range from its `BITS` fields (WP-11b-QL: for any bound `2^ln`, `1 ≤ ln ≤ 62`). -/
theorem n_range (w : UInt64) (ln : Nat) (hln : 1 ≤ ln ∧ ln ≤ 62) (htop : w >>> (ln + 1 : Nat).toUInt64 = 0)
    (hmul : w64 ((w >>> (ln : Nat).toUInt64) &&& 1) * w64 (w <<< (64 - ln : Nat).toUInt64) = 0)
    (hz : ∃ z ≤ ln, (w >>> z.toUInt64) &&& 1 = 1) : 1 ≤ w.toNat ∧ w.toNat ≤ 2 ^ ln := by
  have hs : ∀ n, n < 64 → (n.toUInt64).toNat % 64 = n := fun n hn => by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  have t1 := congrArg UInt64.toNat htop
  rw [UInt64.toNat_shiftRight, hs _ (by omega), Nat.shiftRight_eq_div_pow] at t1
  have hlt : w.toNat < 2 ^ (ln + 1) := by
    rw [UInt64.toNat_zero, Nat.div_eq_zero_iff] at t1
    rcases t1 with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · exact h
  obtain ⟨z, hzl, hz⟩ := hz
  have t2 := congrArg UInt64.toNat hz
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hs _ (by omega), Nat.shiftRight_eq_div_pow] at t2
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos w.toNat with h0 | h0
    · rw [h0, Nat.zero_div] at t2; simp at t2
    · exact h0
  have hp : 2 ^ (ln + 1) = 2 * 2 ^ ln := by rw [Nat.pow_succ, Nat.mul_comm]
  rcases mul_eq_zero.mp hmul with h | h
  · have t3 := congrArg UInt64.toNat (w64_inj (b := 0) h)
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hs _ (by omega), Nat.shiftRight_eq_div_pow] at t3
    have t3' : (w.toNat / 2 ^ ln) % 2 = 0 := by simpa [Nat.and_one_is_mod] using t3
    have h2 : w.toNat / 2 ^ ln < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
    have : w.toNat / 2 ^ ln = 0 := by
      generalize w.toNat / 2 ^ ln = d at t3' h2 ⊢; omega
    rw [Nat.div_eq_zero_iff] at this
    rcases this with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · omega
  · have t3 := congrArg UInt64.toNat (w64_inj (b := 0) h)
    rw [UInt64.toNat_shiftLeft, hs _ (by omega), Nat.shiftLeft_eq, UInt64.toNat_zero] at t3
    have hd : 2 ^ ln * 2 ^ (64 - ln) ∣ w.toNat * 2 ^ (64 - ln) := by
      rw [← Nat.pow_add, show ln + (64 - ln) = 64 by omega]
      exact Nat.dvd_of_mod_eq_zero (by simpa using t3)
    obtain ⟨c, hc⟩ := Nat.dvd_of_mul_dvd_mul_right (Nat.two_pow_pos _) hd
    have : c < 2 := by
      by_contra hc2
      have : 2 ^ ln * 2 ≤ 2 ^ ln * c := Nat.mul_le_mul_left _ (by omega)
      omega
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simp at hc <;> omega

/-- **The child's header checks** (A3). -/
theorem qsig_child {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKS I (qsig I p).1 M.k) (hbits : SigBits I (qsig I p).1 M.k) :
    ChildOk I M.k := by
  obtain ⟨⟨qP, hP, eP⟩, -, -, -, -, ⟨qH, hH⟩, -, ⟨qS, hS⟩, ⟨qM, hM, eM⟩⟩ := qsig_parts h
  have pre := gPre_spec hP.1
  rw [eP] at pre
  obtain ⟨tZ, tO, eZ, eO, -⟩ := pre
  obtain ⟨hvk, -, hbb, hb0, htop, hmul, hprod, hsel⟩ := header_spec tZ tO hH.1 hH.2 hg eZ eO
  have hsl := gSl_spec hS.1 hS.2 hg
  obtain ⟨-, -, -, -, -, -, ⟨qls, hls, els⟩, ⟨qns, hns, ens⟩⟩ := gMsg_parts hM
  rw [eM] at els ens
  set o := (qsig I p).1 with ho
  -- the leaf statement
  have hLS : digAt M.k I.yls = leafStmt (digAt M.k (I.hd + 14)) (M.k (I.hd + 13)).val.toNat := by
    obtain ⟨s, hperm, hdig⟩ := hks.ls
    obtain ⟨L0, Lk, L4, L5, Lz, L16⟩ := leafStmt_spec hls.1 (jf := 0) (by simp) eZ
    beta_reduce at L0 Lk L4 L5 Lz L16
    have e : ∀ l, lanesW M.k (xcell o 447) l = V M ((loop [] (leafStmtLanes I o.pre.1.n) qls).1.cell l 0).n :=
      fun l => by rw [els]; simp [lanesW, xcell]
    have B := leafStmt_lanes (fun l => (M.k (I.hd + 14 + l)).val) (M.k (I.hd + 13)).val
      (lanesW M.k (xcell o 447)) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hdig]
      exact leafStmt_block _ _ _ s B.1 B.2.1 B.2.2.1 B.2.2.2 hperm
    · rw [e, L0]
      have := out1_val (hbits.h 0 (by decide)).1
      simp only [Nat.mul_zero, Nat.add_zero] at this
      exact congrArg (· ^^^ _) this
    · intro k hk1 hk2
      rw [e, Lk k hk1 hk2, show I.bh + 2 * k - 1 = I.bh + 2 * (k - 1) + 1 by omega]
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.h (k - 1) (by omega)).2)
        (out1_val (hbits.h k hk2).1)
    · rw [e, L4]
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.h 3 (by decide)).2) (out1_val hbits.n_lo)
    · rw [e, L5]
      exact congrArg (· ^^^ _) (out1_val hbits.n_hi)
    · intro l hl1 hl2; rw [e, Lz l hl1 hl2]
    · rw [e, L16]
  -- the node statement
  have hNS : digAt M.k I.yns = nodeStmt (digAt M.k (I.hd + 5)) (digAt M.k I.yls) := by
    obtain ⟨s, hperm, hdig⟩ := hks.ns
    obtain ⟨L0, La, L4, Lb, L8, Lz, L16⟩ := two_spec hns.1 (jf := 0) (by simp) eZ
    beta_reduce at L0 La L4 Lb L8 Lz L16
    have e : ∀ l, lanesW M.k (xcell o 448) l = V M ((loop [] (twoLanes o.pre.1.n 0x4E I.bcl I.bls 0) qns).1.cell l 0).n :=
      fun l => by rw [ens]; simp [lanesW, xcell]
    have hA : ∀ n, OV M (loop [] (twoLanes o.pre.1.n 0x4E I.bcl I.bls 0) qns).1 0 (oS n 0) = V M n :=
      fun n => congrArg FK.val (ov_oS_nil M _ rfl n 0)
    simp only [hA] at L0 La L4 Lb L8
    have B := two_lanes tagNode (fun l => (M.k (I.hd + 5 + l)).val) (fun l => (M.k (I.yls + l)).val)
      (lanesW M.k (xcell o 448)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hdig]
      exact nodeStmt_block _ _ _ s B.1 B.2.1 B.2.2.1 B.2.2.2 hperm
    · rw [e, L0]
      have := out1_val (hbits.cl 0 (by decide)).1
      simp only [Nat.mul_zero, Nat.add_zero] at this
      exact congrArg₂ (· ^^^ ·) this rfl
    · intro k hk1 hk2
      rw [e, La k hk1 hk2, show I.bcl + (2 * k - 1) = I.bcl + 2 * (k - 1) + 1 by omega]
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.cl (k - 1) (by omega)).2)
        (out1_val (hbits.cl k hk2).1)
    · rw [e, L4]
      have := out1_val (hbits.ls 0 (by decide)).1
      simp only [Nat.mul_zero, Nat.add_zero] at this
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.cl 3 (by decide)).2) this
    · intro k hk1 hk2
      rw [e, Lb k hk1 hk2, show I.bls + (2 * k - 1) = I.bls + 2 * (k - 1) + 1 by omega]
      exact congrArg₂ (· ^^^ ·) (out1_val (hbits.ls (k - 1) (by omega)).2)
        (out1_val (hbits.ls k hk2).1)
    · rw [e, L8]
      exact congrArg (· ^^^ _) (out1_val (hbits.ls 3 (by decide)).2)
    · intro l hl1 hl2; rw [e, Lz l hl1 hl2]
    · rw [e, L16]
  -- `n'`
  have hn : 1 ≤ (M.k (I.hd + 13)).val.toNat ∧ (M.k (I.hd + 13)).val.toNat ≤ 2 ^ I.ln := by
    refine n_range _ I.ln hln ?_ ?_ ?_
    · have := out1_val hbits.n_top
      rw [htop] at this
      exact this.symm
    · rw [hbits.n_bit I.ln le_rfl, hbits.n_low] at hmul
      exact hmul
    · obtain ⟨z, hz, h0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hprod)
      have hzl : z ≤ I.ln := by simp at hz; omega
      refine ⟨z, hzl, ?_⟩
      have := FK.eq_neg_of_add h0
      rw [hbits.n_bit z hzl] at this
      exact w64_inj this
  have z0 : (0 : FK).val.toNat = 0 := rfl
  have z1 : (1 : FK).val.toNat = 1 := rfl
  dsimp only [ChildOk]
  rcases bool_of_idem hbb with hb | hb
  · have hcl : digAt M.k I.cL = digAt M.k I.yls := digAt_congr fun l hl => by
      have := hsel l hl; rw [hb, zero_mul, zero_add] at this; exact this.symm
    rw [hb, z0, ite_eq_left rfl, hcl, hLS]
    refine ⟨Or.inl rfl, digAt_congr hvk, hn.1, hn.2, fun _ => ⟨digAt_zero (hb0 hb), fun k hk => ?_⟩,
      fun h => absurd h (by decide), rfl⟩
    have := hsl k hk; rwa [hb, zero_mul, zero_add] at this
  · have hcl : digAt M.k I.cL = digAt M.k I.yns := digAt_congr fun l hl => by
      have := hsel l hl
      rw [hb, one_mul, add_assoc, FK.add_self, add_zero] at this; exact this.symm
    rw [hb, z1, ite_eq_right (by decide), hcl, hNS, hLS]
    refine ⟨Or.inr rfl, digAt_congr hvk, hn.1, hn.2, fun h => absurd h (by decide),
      fun _ k hk => ?_, rfl⟩
    have := hsl k hk; rw [hb, one_mul] at this
    exact (FK.eq_neg_of_add this).symm

end Lvm.QSig
