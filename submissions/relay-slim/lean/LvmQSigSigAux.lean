import LvmQSigDefs

/-!
# `Q_sig`'s signature: helpers (words, digests, one hash per kind, one chain)

New for lvm (WP-12). Helpers of `qsig_sigOk` (`LvmQSigSig`).
-/

set_option autoImplicit false

namespace Lvm.QSig.SigH

open Lvm.QSig RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.KSponge Lvm.Wots

/-! ## Words and bits -/

theorem sOut1_val {v : Nat → FK} {w : Nat} {b : BOut} {c : Nat} (h : Out1 v w b c) :
    (v c).val = b.word (v w).val := by rw [h]

theorem bit_word (w : UInt64) {z : Nat} (hz : z < 64) :
    (BOut.bit z).word w = if ubit w z then 1 else 0 := by
  apply u64_ext
  intro i hi
  simp only [BOut.word, ubit_and, ubit_shr _ hz, ubit_one]
  by_cases h : ubit w z <;> by_cases h0 : i = 0 <;> simp_all [ubit_one, ubit_zero]

theorem w64_bit (w : UInt64) {z : Nat} (hz : z < 64) :
    w64 ((BOut.bit z).word w) = if ubit w z then 1 else 0 := by
  rw [bit_word w hz]; split <;> rfl

theorem bit_bool (w : UInt64) {z : Nat} (hz : z < 64) :
    w64 ((BOut.bit z).word w) = 0 ∨ w64 ((BOut.bit z).word w) = 1 := by
  rw [w64_bit w hz]; split <;> simp

theorem bnat_bit (w : UInt64) {z : Nat} (hz : z < 64) :
    bnat (w64 ((BOut.bit z).word w)) = (ubit w z).toNat := by
  rw [w64_bit w hz]
  have h01 : ¬ ((0 : FK) = 1) := by decide
  split <;> simp_all [bnat]

theorem ubit_testBit (w : UInt64) (z : Nat) : ubit w z = w.toNat.testBit z := rfl

/-! ## Digests -/

theorem digOfW_congr {w w' : Nat → UInt64} (h : ∀ l < 4, w l = w' l) : digOfW w = digOfW w' := by
  apply Vector.ext
  intro k hk
  simp only [digOfW, Vector.getElem_ofFn]
  rw [h _ (by omega)]

theorem digOfW_ite {v : Nat → FK} {w : Nat → UInt64} {c : Prop} [Decidable c] {A B : Nat}
    (h : ∀ l < 4, w l = if c then (v (A + l)).val else (v (B + l)).val) :
    digOfW w = if c then digAt v A else digAt v B := by
  unfold digAt
  split_ifs with hc
  · exact digOfW_congr fun l hl => by simp only [h l hl, hc, ↓reduceIte]
  · exact digOfW_congr fun l hl => by simp only [h l hl, hc, ↓reduceIte]

/-! ## One hash per kind -/

/-- A chain step from its lanes (`steps_spec`'s form). -/
theorem step_of_lanes {lane X xw : Nat → UInt64} {jw T c : UInt64} {i s : Nat}
    (hj : jw.toNat < 2 ^ 16) (hi : i < 256) (hs : s < 256)
    (hTc : T ^^^ c = (i.toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
    (hX : ∀ l < 4, X (2 * l) = xw l <<< (24 : Nat).toUInt64 ∧ X (2 * l + 1) = xw l >>> (40 : Nat).toUInt64)
    (L0 : lane 0 = (jw <<< (8 : Nat).toUInt64) ^^^ 0x57) (L1 : lane 1 = (T ^^^ X 0) ^^^ c)
    (Lk : ∀ k, 1 ≤ k → k < 4 → lane (k + 1) = X (2 * k - 1) ^^^ X (2 * k))
    (L5 : lane 5 = X 7 ^^^ 0x1000000) (Lz : ∀ l, 6 ≤ l → l < 16 → lane l = 0)
    (L16 : lane 16 = 0x8000000000000000) {st : State}
    (hperm : BlockPerm (xorMsg zeroSt (laneByte lane)) st) :
    stDigest st = wotsStep jw.toNat i s (digOfW xw) := by
  have h1 : lane 1 = ((i.toUInt64 <<< (8 : ℕ).toUInt64) ^^^ (s.toUInt64 <<< (16 : ℕ).toUInt64)) ^^^
      (xw 0 <<< (24 : ℕ).toUInt64) := by
    rw [L1, UInt64.xor_assoc, UInt64.xor_comm (X 0), ← UInt64.xor_assoc, hTc, ← (hX 0 (by omega)).1]
  have hx : ∀ k, 1 ≤ k → k < 4 →
      lane (k + 1) = (xw (k - 1) >>> (40 : ℕ).toUInt64) ^^^ (xw k <<< (24 : ℕ).toUInt64) := by
    intro k h1 h2
    rw [Lk k h1 h2, show 2 * k - 1 = 2 * (k - 1) + 1 by omega, (hX (k - 1) (by omega)).2,
      (hX k h2).1]
  have h5 : lane 5 = (xw 3 >>> (40 : ℕ).toUInt64) ^^^ 0x1000000 := by
    rw [L5, ← (hX 3 (by omega)).2]
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := wotsStep_lanes jw hj i s hi hs xw lane L0 h1 hx h5 Lz L16
  exact wotsStep_block _ _ _ _ _ _ b0 b1 b2 b3 b4 b5 hperm

/-- A path node from its lanes (`two_spec`'s form, tag `0x4D`). -/
theorem node_of_lanes {lane A B a b : Nat → UInt64}
    (hA : ∀ l < 4, A (2 * l) = a l <<< (8 : Nat).toUInt64 ∧ A (2 * l + 1) = a l >>> (56 : Nat).toUInt64)
    (hB : ∀ l < 4, B (2 * l) = b l <<< (8 : Nat).toUInt64 ∧ B (2 * l + 1) = b l >>> (56 : Nat).toUInt64)
    (L0 : lane 0 = A 0 ^^^ 0x4D) (Lk : ∀ k, 1 ≤ k → k < 4 → lane k = A (2 * k - 1) ^^^ A (2 * k))
    (L4 : lane 4 = A 7 ^^^ B 0)
    (Lb : ∀ k, 1 ≤ k → k < 4 → lane (4 + k) = B (2 * k - 1) ^^^ B (2 * k))
    (L8 : lane 8 = B 7 ^^^ 0x100) (Lz : ∀ l, 9 ≤ l → l < 16 → lane l = 0)
    (L16 : lane 16 = 0x8000000000000000) {st : State}
    (hperm : BlockPerm (xorMsg zeroSt (laneByte lane)) st) :
    stDigest st = sigNode (digOfW a) (digOfW b) := by
  have h0 : lane 0 = (a 0 <<< (8 : ℕ).toUInt64) ^^^ tagSigNode.toUInt64 := by
    rw [L0, ← (hA 0 (by omega)).1]; rfl
  have ha : ∀ k, 1 ≤ k → k < 4 →
      lane k = (a (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (a k <<< (8 : ℕ).toUInt64) := by
    intro k h1 h2
    rw [Lk k h1 h2, show 2 * k - 1 = 2 * (k - 1) + 1 by omega, (hA (k - 1) (by omega)).2,
      (hA k h2).1]
  have h4 : lane 4 = (a 3 >>> (56 : ℕ).toUInt64) ^^^ (b 0 <<< (8 : ℕ).toUInt64) := by
    rw [L4, ← (hA 3 (by omega)).2, ← (hB 0 (by omega)).1]
  have hb : ∀ k, 1 ≤ k → k < 4 →
      lane (4 + k) = (b (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (b k <<< (8 : ℕ).toUInt64) := by
    intro k h1 h2
    rw [Lb k h1 h2, show 2 * k - 1 = 2 * (k - 1) + 1 by omega, (hB (k - 1) (by omega)).2,
      (hB k h2).1]
  have h8 : lane 8 = (b 3 >>> (56 : ℕ).toUInt64) ^^^ 0x100 := by
    rw [L8, ← (hB 3 (by omega)).2]
  obtain ⟨b0, b1, b2, b3⟩ := two_lanes tagSigNode a b lane h0 ha h4 hb h8 Lz L16
  exact sigNode_block _ _ _ _ b0 b1 b2 b3 hperm

/-- The WOTS key leaf from its 544 lanes (`lane`), read by blocks of 17. -/
theorem leaf_of_lanes {lane E : Nat → UInt64} {jw : UInt64} (hj : jw.toNat < 2 ^ 16)
    (h0 : lane 0 = (jw <<< (8 : ℕ).toUInt64) ^^^ 0x4B) (h1 : lane 1 = E 0 <<< (8 : ℕ).toUInt64)
    (hE : ∀ m, 2 ≤ m → m ≤ 532 →
      lane m = (E (m - 2) >>> (56 : ℕ).toUInt64) ^^^ (E (m - 1) <<< (8 : ℕ).toUInt64))
    (h533 : lane 533 = (E 531 >>> (56 : ℕ).toUInt64) ^^^ 0x100)
    (hz : ∀ l, 534 ≤ l → l < 543 → lane l = 0) (h543 : lane 543 = 0x8000000000000000)
    {ends : List Digest} (hlen : ends.length = wotsLen)
    (hends : ∀ i (hi : i < wotsLen), ∀ k (hk : k < 32),
      (ends[i]'(hlen ▸ hi))[k] = byteW (E (4 * i + k / 8)) (k % 8))
    {sIn sOut : Nat → State} (hstart : sIn 0 = zeroSt)
    (hperm : ∀ u < 32, BlockPerm (xorMsg (sIn u) (laneByte fun l => lane (17 * u + l))) (sOut u))
    (hlink : ∀ u, u + 1 < 32 → sIn (u + 1) = sOut u) :
    stDigest (sOut 31) = wotsLeaf jw.toNat ends := by
  have hrate : rate = 136 := rfl
  obtain ⟨b0, b1, b2, b3⟩ := wotsLeaf_lanes jw hj E lane h0 h1 hE h533 hz h543
  have hm : ∀ p, laneByte (fun l => lane (17 * (p / rate) + l)) (p % rate) = laneByte lane p := by
    intro p
    simp only [laneByte, hrate]
    rw [show 17 * (p / 136) + p % 136 / 8 = p / 8 by omega, show p % 136 % 8 = p % 8 by omega]
  have hb : ∀ p, laneByte lane (rate * (p / rate) + p % rate) = laneByte lane p := fun p => by
    rw [Nat.div_add_mod]
  beta_reduce at b0 b1 b2 b3
  refine wotsLeaf_stream jw.toNat ends _ sIn sOut hstart hperm hlink (fun p hp1 hp2 => ?_) ?_
  · rw [hm, ← hb]; exact b3 p hp1 hp2
  · apply wotsLeaf_bytes jw.toNat ends hlen
    · have := hm 0
      simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero] at this b0
      rw [this]; exact b0
    · intro k hk; rw [hm, ← hb]; exact b1 k hk
    · intro i hi k hk; rw [hm, ← hb, hends i hi k hk]; exact b2 i hi k hk

/-! ## One chain -/

/-- **One chain's end** from its three steps and the selections (`chain_spec`'s form). -/
theorem chain_end {v : Nat → FK} {o : SigOut} {I : SigIn} {i d : Nat} {j : Nat} (hd : d ≤ 3)
    (hstep : ∀ s < 3, digAt v (I.ys + 4 * (3 * i + s)) = wotsStep j i s (digOfW (lanesW v (xin I o i s))))
    (hm : ∀ s, 1 ≤ s → s < 3 → ∀ l < 4, (v (xin I o i s l)).val =
      if d < s then (v (I.ys + 4 * (3 * i + (s - 1)) + l)).val else (v (I.sg + 1 + 4 * i + l)).val)
    (he : ∀ l < 4, (v (endc o i l)).val =
      if d < 3 then (v (I.ys + 4 * (3 * i + 2) + l)).val else (v (I.sg + 1 + 4 * i + l)).val) :
    digOfW (lanesW v (endc o i)) = wotsChain j i d (3 - d) (digAt v (I.sg + 1 + 4 * i)) := by
  refine wots_chain_sound hd (a := fun s => digOfW (lanesW v (xin I o i (s - 1))))
    (out := fun s => digAt v (I.ys + 4 * (3 * i + (s - 1)))) (fun s h1 h3 => hstep _ (by omega))
    (fun s h1 h3 => ?_) (digOfW_ite he)
  rcases (show s = 1 ∨ s = 2 ∨ s = 3 by omega) with rfl | rfl | rfl
  · simp only [show ¬ d + 1 < 1 by omega, ↓reduceIte]
    unfold digAt
    exact digOfW_congr fun l _ => by simp [lanesW, xin]
  · show digOfW (lanesW v (xin I o i 1)) = _
    rw [digOfW_ite (w := lanesW v (xin I o i 1)) (hm 1 le_rfl (by omega)),
      show (2 : Nat) - 1 - 1 = 1 - 1 from rfl]
    split_ifs <;> first | (exfalso; omega) | rfl
  · show digOfW (lanesW v (xin I o i 2)) = _
    rw [digOfW_ite (w := lanesW v (xin I o i 2)) (hm 2 (by omega) (by omega)),
      show (3 : Nat) - 1 - 1 = 2 - 1 from rfl]
    split_ifs <;> first | (exfalso; omega) | rfl


/-! ## The gadget's cells -/

theorem xcell_m {o : SigOut} {i s : Nat} (hi : i < 128) (hs : s < 3) (l : Nat) :
    xcell o (3 * i + s) l = (o.msg.xm.cell (17 * s + l) i).n := by
  simp only [xcell, show 3 * i + s < 384 by omega, ↓reduceIte, show (3 * i + s) % 3 = s by omega,
    show (3 * i + s) / 3 = i by omega]

theorem xcell_c {o : SigOut} {u s : Nat} (hu : u < 5) (hs : s < 3) (l : Nat) :
    xcell o (3 * (128 + u) + s) l = ((o.msg.xc.getD u dLoop).cell (17 * s + l) 0).n := by
  simp only [xcell, show ¬ 3 * (128 + u) + s < 384 by omega, show 3 * (128 + u) + s < 399 by omega,
    ↓reduceIte, show (3 * (128 + u) + s - 384) % 3 = s by omega,
    show (3 * (128 + u) + s - 384) / 3 = u by omega]

theorem xcell_leaf (v : Nat → FK) (o : SigOut) {u : Nat} (hu : u < 32) :
    lanesW v (xcell o (399 + u)) = fun l => (v (leafLane o (17 * u + l))).val := by
  funext l
  simp only [lanesW, xcell, show ¬ 399 + u < 384 by omega, show ¬ 399 + u < 399 by omega,
    show 399 + u < 431 by omega, ↓reduceIte, show 399 + u - 399 = u by omega]

theorem xcell_path (v : Nat → FK) (o : SigOut) {t : Nat} (ht : t < 16) :
    lanesW v (xcell o (431 + t)) = fun l => (v (o.msg.xp.cell l t).n).val := by
  funext l
  simp only [lanesW, xcell, show ¬ 431 + t < 384 by omega, show ¬ 431 + t < 399 by omega,
    show ¬ 431 + t < 431 by omega, show 431 + t < 447 by omega, ↓reduceIte,
    show 431 + t - 431 = t by omega]

theorem ov_nil (M : Mem) (o : LoopOut) (hd : o.dims = []) (n s : Nat) :
    ov M o 0 (oS n s) = M.k n := by
  simp [ov, Opd.resolve, Addr.at, dot, hd, unflat]

theorem bnat_dec (b : FK) : bnat b = (decide (b = 1)).toNat := by
  unfold bnat; split <;> simp_all

/-! ## The path mux -/

theorem path_spec {c : Ctx} {M : Mem} {q : Ptr} {I : SigIn}
    (h : SegsHold c M q (loop [4] (pathTpl I) q).2) {t l : Nat} (ht : t < 16) (hl : l < 4)
    (hb : M.k (I.bi + 1 + t) = 0 ∨ M.k (I.bi + 1 + t) = 1) :
    M.k ((loop [4] (pathTpl I) q).1.cell (4 + l) t).n =
        (if M.k (I.bi + 1 + t) = 1 then M.k (I.sg + 533 + l + 4 * t) else M.k (I.yc + l + 4 * t)) ∧
      M.k ((loop [4] (pathTpl I) q).1.cell (8 + l) t).n =
        (if M.k (I.bi + 1 + t) = 1 then M.k (I.yc + l + 4 * t) else M.k (I.sg + 533 + l + 4 * t)) := by
  have hjf : t < 2 ^ ([4] : List Nat).sum := by simpa using ht
  have ht' : t < 2 ^ 4 := by simpa using ht
  have hd : (loop [4] (pathTpl I) q).1.dims = [4] := rfl
  have hlen : (pathTpl I).length = 12 := by simp [pathTpl]
  have g0 : (pathTpl I).getD l default = lr 1 0 (oS (I.yc + l) 4) (oS (I.sg + 533 + l) 4) := by
    interval_cases l <;> rfl
  have g4 : (pathTpl I).getD (4 + l) default = mr (oS (I.bi + 1) 1) (.cur l) (oS (I.yc + l) 4) := by
    interval_cases l <;> rfl
  have g8 : (pathTpl I).getD (8 + l) default =
      mr (oS (I.bi + 1) 1) (.cur l) (oS (I.sg + 533 + l) 4) := by
    interval_cases l <;> rfl
  have hK : ((loop [4] (pathTpl I) q).1.tpl.getD l default).ty = .K := by
    show ((pathTpl I).getD l default).ty = .K; rw [g0]
  have r0 := loopK_lin h hjf (by omega) g0 rfl rfl
  have r4 := loopK_mad h hjf (by omega) g4 rfl hK rfl
  have r8 := loopK_mad h hjf (by omega) g8 rfl hK rfl
  rw [ov_cur M _ hjf l hK, r0] at r4 r8
  simp only [ov_oS M _ hd ht', one_mul, add_zero] at r4 r8
  rw [r4, r8, add_comm (M.k (I.yc + l + 4 * t)) (M.k (I.sg + 533 + l + 4 * t)),
    mux_eq hb]
  rw [add_comm (M.k (I.sg + 533 + l + 4 * t)) (M.k (I.yc + l + 4 * t)), mux_eq hb]
  exact ⟨rfl, rfl⟩

/-! ## Chain steps -/

/-- **A message chain's step** `s` (row `3i + s`). -/
theorem step_m {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {r : Ptr} {Zn Tb : Nat}
    (hks : SigKS I o M.k) (hbits : SigBits I o M.k) (hZ : M.k Zn = 0)
    (hT : ∀ i < 128, M.k (Tb + i) = w64 (i.toUInt64 <<< (8 : Nat).toUInt64))
    (hj : (M.k I.sg).val.toNat < 2 ^ 16)
    (h : SegsHold c M r (loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).2)
    (e : (loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).1 = o.msg.xm)
    {i s : Nat} (hi : i < 128) (hs : s < 3) :
    digAt M.k (I.ys + 4 * (3 * i + s)) =
      wotsStep (M.k I.sg).val.toNat i s (digOfW (lanesW M.k (xin I o i s))) := by
  obtain ⟨st, hp, hd⟩ := hks.step (3 * i + s) (by omega)
  rw [hd]
  have hjf : i < 2 ^ ([7] : List Nat).sum := by simpa using hi
  have hi7 : i < 2 ^ 7 := by simpa using hi
  have hd7 : (loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).1.dims = [7] := rfl
  obtain ⟨L0, L1, Lk, L5, Lz, L16⟩ := steps_spec h hjf rfl hZ hs
  beta_reduce at L0 L1 Lk L5 Lz L16
  have hlane : ∀ l, lanesW M.k (xcell o (3 * i + s)) l = V M ((loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).1.cell (17 * s + l) i).n := by
    intro l; rw [e]; simp only [lanesW, xcell_m hi hs]
  have hbi : V M I.bi = (M.k I.sg).val <<< (8 : Nat).toUInt64 := by
    show (M.k I.bi).val = _; rw [hbits.idx_lo]; rfl
  refine step_of_lanes (lane := lanesW M.k (xcell o (3 * i + s)))
    (X := fun k => OV M (loop [7] (stepsTpl I Zn (oS Tb 1)
      (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) r).1 i (oS (I.bx + 8 * s + k) 24)) hj (by omega) (by omega)
    ?_ (fun l hl => ⟨?_, ?_⟩) (by rw [hlane, L0, hbi]) (by rw [hlane]; exact L1)
    (fun k h1 h2 => by rw [hlane]; exact Lk k h1 h2) (by rw [hlane]; exact L5)
    (fun l h1 h2 => by rw [hlane]; exact Lz l h1 h2) (by rw [hlane]; exact L16) hp
  · rw [ovS_V hd7 hi7 (show Tb + 1 * i = Tb + i by ring)]
    show (M.k (Tb + i)).val ^^^ _ = _
    rw [hT i hi]
  · rw [ovS_V hd7 hi7 (show I.bx + 8 * s + 2 * l + 24 * i = I.bx + 2 * (4 * (3 * i + s) + l) by ring)]
    dsimp only [V]; rw [sOut1_val (hbits.x i (by omega) s hs l hl).1]; rfl
  · rw [ovS_V hd7 hi7
      (show I.bx + 8 * s + (2 * l + 1) + 24 * i = I.bx + 2 * (4 * (3 * i + s) + l) + 1 by ring)]
    dsimp only [V]; rw [sOut1_val (hbits.x i (by omega) s hs l hl).2]; rfl

/-- **A checksum chain's step** `s` (chain `128 + u`, row `3(128 + u) + s`). -/
theorem step_c {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {r : Ptr} {Zn u : Nat}
    (hks : SigKS I o M.k) (hbits : SigBits I o M.k) (hZ : M.k Zn = 0)
    (hj : (M.k I.sg).val.toNat < 2 ^ 16) (hu : u < 5)
    (h : SegsHold c M r (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).2)
    (e : (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).1 = o.msg.xc.getD u dLoop)
    {s : Nat} (hs : s < 3) :
    digAt M.k (I.ys + 4 * (3 * (128 + u) + s)) =
      wotsStep (M.k I.sg).val.toNat (128 + u) s (digOfW (lanesW M.k (xin I o (128 + u) s))) := by
  obtain ⟨st, hp, hd⟩ := hks.step (3 * (128 + u) + s) (by omega)
  rw [hd]
  have hjf : 0 < 2 ^ ([] : List Nat).sum := by simp
  have hd0 : (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).1.dims = [] := rfl
  obtain ⟨L0, L1, Lk, L5, Lz, L16⟩ := steps_spec h hjf rfl hZ hs
  beta_reduce at L0 L1 Lk L5 Lz L16
  have hlane : ∀ l, lanesW M.k (xcell o (3 * (128 + u) + s)) l = V M ((loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).1.cell (17 * s + l) 0).n := by
    intro l; rw [e]; simp only [lanesW, xcell_c hu hs]
  have hbi : V M I.bi = (M.k I.sg).val <<< (8 : Nat).toUInt64 := by
    show (M.k I.bi).val = _; rw [hbits.idx_lo]; rfl
  refine step_of_lanes (lane := lanesW M.k (xcell o (3 * (128 + u) + s)))
    (X := fun k => OV M (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) r).1 0 (oS (I.bx + 24 * (128 + u) + 8 * s + k) 0)) hj (by omega) (by omega)
    ?_ (fun l hl => ⟨?_, ?_⟩) (by rw [hlane, L0, hbi]) (by rw [hlane]; exact L1)
    (fun k h1 h2 => by rw [hlane]; exact Lk k h1 h2) (by rw [hlane]; exact L5)
    (fun l h1 h2 => by rw [hlane]; exact Lz l h1 h2) (by rw [hlane]; exact L16) hp
  · show (ov M _ 0 (oA Zn)).val ^^^ _ = _
    rw [ov_oA, hZ]; exact UInt64.zero_xor
  · show (ov M _ 0 (oS _ 0)).val = _
    rw [ov_nil M _ hd0, show I.bx + 24 * (128 + u) + 8 * s + 2 * l =
      I.bx + 2 * (4 * (3 * (128 + u) + s) + l) by ring]
    rw [sOut1_val (hbits.x (128 + u) (by omega) s hs l hl).1]; rfl
  · show (ov M _ 0 (oS _ 0)).val = _
    rw [ov_nil M _ hd0, show I.bx + 24 * (128 + u) + 8 * s + (2 * l + 1) =
      I.bx + 2 * (4 * (3 * (128 + u) + s) + l) + 1 by ring]
    rw [sOut1_val (hbits.x (128 + u) (by omega) s hs l hl).2]; rfl

/-! ## Chain selections -/

theorem loop_dims_eq (dims : List Nat) (tpl : List LRow) (q : Ptr) : (loop dims tpl q).1.dims = dims :=
  rfl

theorem kval_congr (M : Mem) {a b : Nat} (h : a = b) : (M.k a).val = (M.k b).val := by rw [h]

/-- **A message chain's selections** (iteration `i` of the `cm` loop). -/
theorem sel_m {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {q : Ptr} {Zn On : Nat}
    (h : SegsHold c M q (loop [7] (chainM I Zn On) q).2)
    (e : (loop [7] (chainM I Zn On) q).1 = o.cm) (hZ : M.k Zn = 0) (hO : M.k On = 1)
    (hbd : ∀ q < 256, M.k (I.bd + q) = 0 ∨ M.k (I.bd + q) = 1) {i : Nat} (hi : i < 128) :
    (∀ s, 1 ≤ s → s < 3 → ∀ l < 4, (M.k (xin I o i s l)).val =
      if mdig M I i < s then (M.k (I.ys + 4 * (3 * i + (s - 1)) + l)).val
        else (M.k (I.sg + 1 + 4 * i + l)).val) ∧
    (∀ l < 4, (M.k (endc o i l)).val =
      if mdig M I i < 3 then (M.k (I.ys + 4 * (3 * i + 2) + l)).val
        else (M.k (I.sg + 1 + 4 * i + l)).val) := by
  unfold chainM at h e
  have hjf : i < 2 ^ ([7] : List Nat).sum := by simpa using hi
  have hi7 : i < 2 ^ 7 := by simpa using hi
  have hd7 := loop_dims_eq [7] (chainTpl (oS I.bd 2) (oS (I.bd + 1) 2) (oA Zn) (oA On)
    (fun l => oS (I.sg + 1 + l) 4) (fun l => oS (I.ys + l) 12) (fun l => oS (I.ys + 4 + l) 12)
    (fun l => oS (I.ys + 8 + l) 12)) q
  have C := fun l (hl : l < 4) => chain_spec (d0 := oS I.bd 2) (d1 := oS (I.bd + 1) 2)
    (Z := oA Zn) (O := oA On) (ots := fun l => oS (I.sg + 1 + l) 4)
    (o1 := fun l => oS (I.ys + l) 12) (o2 := fun l => oS (I.ys + 4 + l) 12)
    (o3 := fun l => oS (I.ys + 8 + l) 12) h hjf
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (fun l _ x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                        rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (by rw [ov_oA, hZ]) (by rw [ov_oA, hO]) (b0 := M.k (I.bd + 2 * i))
    (b1 := M.k (I.bd + 2 * i + 1)) (by rw [ov_oS _ _ hd7 hi7])
    (by rw [ov_oS _ _ hd7 hi7, show I.bd + 1 + 2 * i = I.bd + 2 * i + 1 by ring])
    (hbd _ (by omega)) (by rw [Nat.add_assoc]; exact hbd _ (by omega)) hl
  unfold mdig
  refine ⟨fun s h1 h2 l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨C1, C2, -⟩ := C l hl
    simp only [cv] at C1 C2
    rcases (show s = 1 ∨ s = 2 by omega) with rfl | rfl
    · simp only [← e, xin, chainCell, one_ne_zero, ↓reduceIte, hi, show 8 * 1 + l = 8 + l by ring, C1,
        ov_oS _ _ hd7 hi7]
      split_ifs <;> exact kval_congr M (by omega)
    · simp only [← e, xin, chainCell, show (2 : Nat) ≠ 0 by omega, ↓reduceIte, hi,
        show 8 * 2 + l = 16 + l by ring, C2, ov_oS _ _ hd7 hi7]
      split_ifs <;> exact kval_congr M (by omega)
  · obtain ⟨-, -, C3⟩ := C l hl
    simp only [cv] at C3
    simp only [← e, endc, chainCell, hi, ↓reduceIte, C3, ov_oS _ _ hd7 hi7]
    split_ifs <;> exact kval_congr M (by omega)

/-- The digit of checksum chain `128 + u` from its bit cells. -/
def cdig (M : Mem) (I : SigIn) (u : Nat) : Nat :=
  bnat (M.k (I.bc + 2 * u)) + 2 * bnat (M.k (I.bc + 2 * u + 1))

/-- **A checksum chain's selections** (chain `128 + u`). -/
theorem sel_c {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {q : Ptr} {Zn On u : Nat}
    (h : SegsHold c M q (loop [] (chainC I Zn On u) q).2)
    (e : (loop [] (chainC I Zn On u) q).1 = o.cc.getD u dLoop) (hZ : M.k Zn = 0) (hO : M.k On = 1)
    (hbc : ∀ k < 10, M.k (I.bc + k) = 0 ∨ M.k (I.bc + k) = 1) (hu : u < 5) :
    (∀ s, 1 ≤ s → s < 3 → ∀ l < 4, (M.k (xin I o (128 + u) s l)).val =
      if cdig M I u < s then (M.k (I.ys + 4 * (3 * (128 + u) + (s - 1)) + l)).val
        else (M.k (I.sg + 1 + 4 * (128 + u) + l)).val) ∧
    (∀ l < 4, (M.k (endc o (128 + u) l)).val =
      if cdig M I u < 3 then (M.k (I.ys + 4 * (3 * (128 + u) + 2) + l)).val
        else (M.k (I.sg + 1 + 4 * (128 + u) + l)).val) := by
  unfold chainC at h e
  have hjf : 0 < 2 ^ ([] : List Nat).sum := by simp
  have C := fun l (hl : l < 4) => chain_spec (d0 := oA (I.bc + 2 * u)) (d1 := oA (I.bc + 2 * u + 1))
    (Z := oA Zn) (O := oA On) (ots := fun l => oA (I.sg + 1 + 4 * (128 + u) + l))
    (o1 := fun l => oA (I.ys + 4 * (3 * (128 + u)) + l))
    (o2 := fun l => oA (I.ys + 4 * (3 * (128 + u) + 1) + l))
    (o3 := fun l => oA (I.ys + 4 * (3 * (128 + u) + 2) + l)) h hjf
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (fun l _ x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                        rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (by rw [ov_oA, hZ]) (by rw [ov_oA, hO]) (b0 := M.k (I.bc + 2 * u))
    (b1 := M.k (I.bc + 2 * u + 1)) (by rw [ov_oA]) (by rw [ov_oA])
    (hbc _ (by omega)) (by rw [Nat.add_assoc]; exact hbc _ (by omega)) hl
  unfold cdig
  have hn : ¬ 128 + u < 128 := by omega
  have hs : 128 + u - 128 = u := by omega
  refine ⟨fun s h1 h2 l hl => ?_, fun l hl => ?_⟩
  · obtain ⟨C1, C2, -⟩ := C l hl
    simp only [cv] at C1 C2
    rcases (show s = 1 ∨ s = 2 by omega) with rfl | rfl
    · simp only [← e, xin, chainCell, one_ne_zero, ↓reduceIte, hn, hs, show 8 * 1 + l = 8 + l by ring, C1,
        ov_oA]
      split_ifs <;> exact kval_congr M (by omega)
    · simp only [← e, xin, chainCell, show (2 : Nat) ≠ 0 by omega, ↓reduceIte, hn, hs,
        show 8 * 2 + l = 16 + l by ring, C2, ov_oA]
      split_ifs <;> exact kval_congr M (by omega)
  · obtain ⟨-, -, C3⟩ := C l hl
    simp only [cv] at C3
    simp only [← e, endc, chainCell, hn, hs, ↓reduceIte, C3, ov_oA]
    split_ifs <;> rfl

/-! ## Digits -/

theorem mdig_eq {M : Mem} {I : SigIn} {o : SigOut} (hbits : SigBits I o M.k) {i : Nat} (hi : i < 128) :
    mdig M I i = (msgDigits (digAt M.k I.md))[i]'(by rw [msgDigits_length]; exact hi) := by
  rw [msgDigit_bits (digAt M.k I.md) (fun l => (M.k (I.md + l)).val) (fun k hk => digOfW_get _ hk) hi]
  unfold mdig
  have h0 := hbits.md (2 * i) (by omega)
  have h1 := hbits.md (2 * i + 1) (by omega)
  unfold Out1 at h0 h1
  rw [Nat.add_assoc, h0, h1, bnat_bit _ (Nat.mod_lt _ (by norm_num)),
    bnat_bit _ (Nat.mod_lt _ (by norm_num)), show 2 * i / 64 = i / 32 by omega,
    show (2 * i + 1) / 64 = i / 32 by omega, show (2 * i + 1) % 64 = 2 * i % 64 + 1 by omega]

theorem wdig_lt (m : Digest) {i : Nat} (hi : i < 128) :
    (wotsDigits m)[i]'(by rw [wotsDigits_length]; simp [wotsLen]; omega) =
      (msgDigits m)[i]'(by rw [msgDigits_length]; exact hi) := by
  simp only [wotsDigits]
  rw [List.getElem_append_left]

theorem range_mdig {M : Mem} {I : SigIn} {o : SigOut} (hbits : SigBits I o M.k) :
    (List.range 128).map (fun i => 3 - mdig M I i) = (msgDigits (digAt M.k I.md)).map (3 - ·) := by
  apply List.ext_getElem (by simp [msgDigits_length])
  intro n h1 h2
  have hn : n < 128 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [mdig_eq hbits hn]

theorem cdig_eq {M : Mem} {I : SigIn} (m : Digest)
    (hC : ((msgDigits m).map (3 - ·)).sum = bitsVal (cbit M I) 10) {u : Nat} (hu : u < 5) :
    cdig M I u = (wotsDigits m)[128 + u]'(by rw [wotsDigits_length]; simp [wotsLen]; omega) := by
  rw [checksum_digit m (cbit M I) hC hu, cdig, bnat_dec, bnat_dec]
  rfl

/-! ## The key leaf and the path nodes -/

/-- **The key leaf** of the chain ends. -/
theorem leaf_digest {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {r3 r4 r5 : Ptr} {Zn : Nat}
    (hks : SigKS I o M.k) (hbits : SigBits I o M.k) (hZ : M.k Zn = 0)
    (hj : (M.k I.sg).val.toNat < 2 ^ 16)
    (hla : SegsHold c M r3 (loop [] (leafA I) r3).2) (ela : (loop [] (leafA I) r3).1 = o.msg.la)
    (hlb : SegsHold c M r4 (loop [9] (leafB I) r4).2) (elb : (loop [9] (leafB I) r4).1 = o.msg.lb)
    (hlc : SegsHold c M r5 (loop [] (leafC I Zn) r5).2) (elc : (loop [] (leafC I Zn) r5).1 = o.msg.lc) :
    digAt M.k I.yc = wotsLeaf (M.k I.sg).val.toNat
      ((List.range wotsLen).map fun i => digOfW (lanesW M.k (endc o i))) := by
  obtain ⟨sIn, sOut, hstart, hperm, hlink, hdig⟩ := hks.leaf
  rw [hdig]
  have hEk : ∀ k < 532, (M.k (I.be + 2 * k)).val = (M.k (endc o (k / 4) (k % 4))).val <<< (8 : Nat).toUInt64 ∧
      (M.k (I.be + 2 * k + 1)).val = (M.k (endc o (k / 4) (k % 4))).val >>> (56 : Nat).toUInt64 := by
    intro k hk
    have := hbits.e (k / 4) (by omega) (k % 4) (by omega)
    rw [show 2 * (4 * (k / 4) + k % 4) = 2 * k by omega] at this
    exact ⟨sOut1_val this.1, sOut1_val this.2⟩
  have hbi : (M.k I.bi).val = (M.k I.sg).val <<< (8 : Nat).toUInt64 := by rw [hbits.idx_lo]; rfl
  obtain ⟨A0, A1⟩ := leafA_spec hla (jf := 0) (by simp)
  rw [ela] at A0 A1
  have hB : ∀ m < 512, V M (o.msg.lb.cell 0 m).n =
      V M (I.be + 2 * m + 1) ^^^ V M (I.be + 2 * (m + 1)) := fun m hm => by
    rw [← elb]; exact leafB_spec hlb (by simpa using hm)
  obtain ⟨C1, C2, C3, C4⟩ := leafC_spec hlc (jf := 0) (by simp) hZ
  beta_reduce at C1 C2 C3 C4
  rw [elc] at C1 C2 C3 C4
  dsimp only [V] at A0 A1 hB C1 C2 C3 C4
  refine leaf_of_lanes (lane := fun m => (M.k (leafLane o m)).val)
    (E := fun k => (M.k (endc o (k / 4) (k % 4))).val) hj ?_ ?_ (fun m h1 h2 => ?_) ?_
    (fun l h1 h2 => ?_) ?_ (by simp [wotsLen]) (fun i hi k hk => ?_) hstart
    (fun u hu => by have := hperm u hu; rwa [xcell_leaf _ _ hu] at this) hlink
  · show (M.k (leafLane o 0)).val = _
    simp only [leafLane, show (0 : Nat) < 2 by omega, ↓reduceIte]
    rw [A0, hbi]
  · show (M.k (leafLane o 1)).val = _
    simp only [leafLane, show (1 : Nat) < 2 by omega, ↓reduceIte]
    rw [A1]; exact (hEk 0 (by omega)).1
  · show (M.k (leafLane o m)).val = _
    by_cases hm : m < 514
    · simp only [leafLane, show ¬ m < 2 by omega, hm, ↓reduceIte]
      rw [hB (m - 2) (by omega), show m - 2 + 1 = m - 1 by omega]
      exact congrArg₂ _ (hEk (m - 2) (by omega)).2 (hEk (m - 1) (by omega)).1
    · simp only [leafLane, show ¬ m < 2 by omega, hm, ↓reduceIte]
      rw [C1 (m - 514) (by omega), show 512 + (m - 514) = m - 2 by omega,
        show 513 + (m - 514) = m - 1 by omega]
      exact congrArg₂ _ (hEk (m - 2) (by omega)).2 (hEk (m - 1) (by omega)).1
  · show (M.k (leafLane o 533)).val = _
    simp only [leafLane, show ¬ (533 : Nat) < 2 by omega, show ¬ (533 : Nat) < 514 by omega,
      ↓reduceIte]
    rw [show (533 : Nat) - 514 = 19 from rfl, C2]
    exact congrArg (· ^^^ _) (hEk 531 (by omega)).2
  · show (M.k (leafLane o l)).val = _
    simp only [leafLane, show ¬ l < 2 by omega, show ¬ l < 514 by omega, ↓reduceIte]
    exact C3 (l - 514) (by omega) (by omega)
  · show (M.k (leafLane o 543)).val = _
    simp only [leafLane, show ¬ (543 : Nat) < 2 by omega, show ¬ (543 : Nat) < 514 by omega,
      ↓reduceIte]
    exact C4
  · simp only [List.getElem_map, List.getElem_range]
    rw [digOfW_get _ hk, show (4 * i + k / 8) / 4 = i by omega, show (4 * i + k / 8) % 4 = k / 8 by omega]
    rfl

/-- **A path node** (level `t`) of the mux outputs. -/
theorem node_digest {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {r : Ptr} {Zn : Nat}
    (hks : SigKS I o M.k) (hbits : SigBits I o M.k) (hZ : M.k Zn = 0)
    (h : SegsHold c M r (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).2)
    (e : (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1 = o.msg.xp) {t : Nat} (ht : t < 16) :
    digAt M.k (I.yc + 4 * (t + 1)) = sigNode (digOfW fun l => (M.k (o.pa.cell (4 + l) t).n).val)
      (digOfW fun l => (M.k (o.pa.cell (8 + l) t).n).val) := by
  obtain ⟨st, hp, hd⟩ := hks.path t ht
  rw [hd]
  rw [xcell_path _ _ ht] at hp
  have hjf : t < 2 ^ ([4] : List Nat).sum := by simpa using ht
  have ht4 : t < 2 ^ 4 := by simpa using ht
  have hd4 := loop_dims_eq [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r
  obtain ⟨L0, Lk, L4, Lb, L8, Lz, L16⟩ := two_spec h hjf hZ
  beta_reduce at L0 Lk L4 Lb L8 Lz L16
  have hlane : ∀ l, (M.k (o.msg.xp.cell l t).n).val =
      V M ((loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1.cell l t).n := by
    intro l; rw [e]
  refine node_of_lanes (lane := fun l => (M.k (o.msg.xp.cell l t).n).val)
    (A := fun k => OV M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1 t (oS (I.bp + k) 16))
    (B := fun k => OV M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) r).1 t (oS (I.bp + 8 + k) 16))
    (fun l hl => ⟨?_, ?_⟩) (fun l hl => ⟨?_, ?_⟩) (by rw [hlane]; exact L0)
    (fun k h1 h2 => by rw [hlane]; exact Lk k h1 h2) (by rw [hlane]; exact L4)
    (fun k h1 h2 => by rw [hlane]; exact Lb k h1 h2) (by rw [hlane]; exact L8)
    (fun l h1 h2 => by rw [hlane]; exact Lz l h1 h2) (by rw [hlane]; exact L16) hp
  · have := (hbits.p t ht 0 (by omega) l hl).1
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [ovS_V hd4 ht4 (show I.bp + 2 * l + 16 * t = I.bp + 2 * (8 * t + l) by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 0 (by omega) l hl).2
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [ovS_V hd4 ht4 (show I.bp + (2 * l + 1) + 16 * t = I.bp + 2 * (8 * t + l) + 1 by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 1 (by omega) l hl).1
    rw [show 4 + 4 * 1 + l = 8 + l by ring] at this
    rw [ovS_V hd4 ht4 (show I.bp + 8 + 2 * l + 16 * t = I.bp + 2 * (8 * t + 4 * 1 + l) by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl
  · have := (hbits.p t ht 1 (by omega) l hl).2
    rw [show 4 + 4 * 1 + l = 8 + l by ring] at this
    rw [ovS_V hd4 ht4
      (show I.bp + 8 + (2 * l + 1) + 16 * t = I.bp + 2 * (8 * t + 4 * 1 + l) + 1 by ring)]
    dsimp only [V]; rw [sOut1_val this]; rfl

/-! ## The index -/

theorem idx_lt {c : Ctx} {M : Mem} {I : SigIn} {o : SigOut} {q : Ptr}
    (has : Ok c M (assert0 (kc (I.bi + 17)) (kc I.flag)) q) (hg : M.k I.flag = 1)
    (hbits : SigBits I o M.k) : (M.k I.sg).val.toNat < 2 ^ 16 := by
  have a := ok_assert0 (a := kc (I.bi + 17)) rfl has
  rw [hg, one_mul] at a
  have hb := hbits.idx_hi
  unfold Out1 at hb
  rw [a] at hb
  have hw : (M.k I.sg).val >>> (16 : Nat).toUInt64 = 0 := (congrArg FK.val hb).symm
  have := congrArg UInt64.toNat hw
  simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_zero] at this
  have h16 : (16 : Nat).toUInt64.toNat % 64 = 16 := by decide
  rw [h16] at this
  exact Nat.lt_of_div_eq_zero (by norm_num) this

end Lvm.QSig.SigH
