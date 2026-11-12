-- New for ws-leaf: the hash chain `chainEnd s n` and the leaf statement on the extractor machine.
-- The Keccak rounds, the leaf block and the bit lemmas are `WlXKeccak.lean`'s (from the
-- leanvm-inspired entry, #11); the chain step's block mirrors its leaf block.
import WlXKeccak

/-!
# `digIR`: a leaf statement recomputed from a chain start, on the extractor machine

`digIR a nI` reads the four packed words of a chain start `s` (tape words `a … a+3`) into the
registers `212 … 215` and the length word `n` (tape word `nI`) into `216`, runs
`min(n, chainCap)` chain steps in place (`loopK` with the clamp `chainCap`; one step is the block of
`0x43 ‖ d` built in the lanes, the 24 rounds, lanes `0 … 3` copied back to `212 … 215`), then the
leaf statement's block, its 24 rounds, and outputs lanes `0 … 3`.

* `kcC0`, `kc_initC_run`, `kc_absorb_chain`, `chainStep_kc`: one chain step is the permuted `kcC0`
  of the packed words (the chain twin of `kcS0`, `kc_absorb_eq`, `leafStmt_kc`).
* **`digIR_sem`**: the output is `digW` of the five tape words.
-/

namespace WsLeaf.X

open RecursionFast RecursionFast.Keccak

/-- The chain loop's counter register. -/
def rCh : ℕ := 100

/-- The digest whose packed words are `a b c d`. -/
def dgW (a b c d : Word) : Digest := ⟨(wordsBytes [a, b, c, d]).toArray, by simp [wordsBytes_length]⟩

/-- **The derived leaf statement** of the packed start words `a b c d` and the length word `nw`:
`min nw chainCap` chain steps (the loop's clamp), then the leaf statement of length `nw`, packed. -/
def digW (a b c d nw : Word) : List Word :=
  packBytes (leafStmt (chainEnd (dgW a b c d) (min nw.toNat chainCap)) nw.toNat).toList

/-- The constants and the absorbed block of a chain step `0x43 ‖ d`, `d` in `212 … 215`. -/
def kcInitC : List Prim :=
  [.const 217 (BitVec.ofNat 64 1), .const 218 (BitVec.ofNat 64 2),
   .const 219 (BitVec.ofNat 64 3), .const 220 (BitVec.ofNat 64 6),
   .const 221 (BitVec.ofNat 64 8), .const 222 (BitVec.ofNat 64 9),
   .const 223 (BitVec.ofNat 64 10), .const 224 (BitVec.ofNat 64 14),
   .const 225 (BitVec.ofNat 64 15), .const 226 (BitVec.ofNat 64 18),
   .const 227 (BitVec.ofNat 64 19), .const 228 (BitVec.ofNat 64 20),
   .const 229 (BitVec.ofNat 64 21), .const 230 (BitVec.ofNat 64 23),
   .const 231 (BitVec.ofNat 64 25), .const 232 (BitVec.ofNat 64 27),
   .const 233 (BitVec.ofNat 64 28), .const 234 (BitVec.ofNat 64 36),
   .const 235 (BitVec.ofNat 64 37), .const 236 (BitVec.ofNat 64 39),
   .const 237 (BitVec.ofNat 64 41), .const 238 (BitVec.ofNat 64 43),
   .const 239 (BitVec.ofNat 64 44), .const 240 (BitVec.ofNat 64 45),
   .const 241 (BitVec.ofNat 64 46), .const 242 (BitVec.ofNat 64 49),
   .const 243 (BitVec.ofNat 64 50), .const 244 (BitVec.ofNat 64 54),
   .const 245 (BitVec.ofNat 64 55), .const 246 (BitVec.ofNat 64 56),
   .const 247 (BitVec.ofNat 64 58), .const 248 (BitVec.ofNat 64 61),
   .const 249 (BitVec.ofNat 64 62), .const 250 (BitVec.ofNat 64 63),
   .const 210 (BitVec.allOnes 64),
   .const 128 0x43, .op .shl 208 212 221, .op .or 128 128 208,
   .op .shr 208 212 246, .op .shl 209 213 221, .op .or 129 208 209, .op .shr 208 213 246,
   .op .shl 209 214 221, .op .or 130 208 209, .op .shr 208 214 246, .op .shl 209 215 221,
   .op .or 131 208 209, .op .shr 208 215 246, .const 209 0x100, .op .or 132 208 209,
   .const 133 0, .const 134 0, .const 135 0, .const 136 0, .const 137 0, .const 138 0, .const 139 0,
   .const 140 0, .const 141 0, .const 142 0, .const 143 0, .const 144 0x8000000000000000,
   .const 145 0, .const 146 0, .const 147 0, .const 148 0, .const 149 0, .const 150 0, .const 151 0,
   .const 152 0]

/-- The absorbed block of `0x43 ‖ d` from the packed words `w₀ … w₃` of `d`: lane `j < 17` is
`(P_{j−1} >> 56) | (P_j << 8)` of the packed words `P` of the padded message after its first
byte (`0x01` at byte 33, `0x80` at byte 135). -/
def kcC0 (w0 w1 w2 w3 : Word) : S25 :=
  ⟨.ofBitVec (0x43 ||| w0 <<< 8), .ofBitVec (w0 >>> 56 ||| w1 <<< 8), .ofBitVec (w1 >>> 56 ||| w2 <<< 8),
   .ofBitVec (w2 >>> 56 ||| w3 <<< 8), .ofBitVec (w3 >>> 56 ||| 0x100),
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, .ofBitVec 0x8000000000000000,
   0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Lanes `0 … 3` back into `212 … 215`. -/
def copyBackPs : List Prim :=
  [.op .or 212 128 128, .op .or 213 129 129, .op .or 214 130 130, .op .or 215 131 131]

/-- **One chain step** on `212 … 215`. -/
def chainBody : XIR := .seq (.blk kcInitC) (.seq (kcRoundsIR rc.toList) (.blk copyBackPs))

/-- The leaf statement of the chain end in `212 … 215` and the length in `216`, output. -/
def leafTail : XIR :=
  .seq (.blk kcInitPs) (.seq (kcRoundsIR rc.toList)
    (.seq (.out 128) (.seq (.out 129) (.seq (.out 130) (.out 131)))))

/-- **The derived leaf statement on the machine**: read the start (tape words `a … a+3`) and the
length (tape word `nI`), `min(n, chainCap)` chain steps, the leaf statement, output 4 words. -/
def digIR (a nI : ℕ) : XIR :=
  .seq (readAt 212 a) (.seq (readAt 213 (a + 1)) (.seq (readAt 214 (a + 2)) (.seq (readAt 215 (a + 3))
    (.seq (readAt 216 nI) (.seq (.loopK rCh 216 (BitVec.ofNat 64 chainCap) chainBody) leafTail)))))

/-! ## The chain step's block -/

theorem kcInitC_dst :
    ∀ p ∈ kcInitC, 128 ≤ p.dst ∧ p.dst < 251 ∧ (p.dst < 212 ∨ 216 < p.dst) := by decide

theorem copyBackPs_dst : ∀ p ∈ copyBackPs, 212 ≤ p.dst ∧ p.dst ≤ 215 := by decide

/-- **The chain init block** sets the constants and absorbs the block of `212 … 215`. -/
theorem kc_initC_run (R : ℕ → Word) :
    KcHoldsA (kcEval kcInitC R) (kcC0 (R 212) (R 213) (R 214) (R 215)) ∧
      KcKR (kcEval kcInitC R) := by
  simp only [KcHoldsA, KcKR, kcC0, kcInitC, kcEval, List.foldl, kcStep]
  simp only [kc_upd_apply, ↓reduceIte, Nat.reduceEqDiff, eval_or, kc_eval_shl, kc_eval_shr,
    Nat.reduceMod, Nat.reducePow]
  simp

/-- The padding of a 33-byte message: `0x01`, 101 zeros, `0x80`. -/
def kcPadC : List UInt8 := 0x01 :: (List.replicate 101 0 ++ [0x80])

theorem kc_packBytes_kcPadC (k : ℕ) :
    (packBytes kcPadC).getD k 0 = if k = 0 then 1 else if k = 12 then 0x0080000000000000 else 0 := by
  have e : packBytes kcPadC = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x0080000000000000] := by decide
  rw [e]
  by_cases hk : k < 13
  · interval_cases k <;> rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp only [show k ≠ 0 by omega, show k ≠ 12 by omega, ↓reduceIte]

/-- The chain message padded: `0x43`, then `d ‖ 0x01 ‖ 0¹⁰¹ ‖ 0x80`. -/
theorem kc_pad_chain (d : Digest) : pad (tagChain :: d.toList) = tagChain :: (d.toList ++ kcPadC) := by
  have hl : (tagChain :: d.toList).length = 33 := by simp
  simp only [pad, hl, rate, kcPadC]
  simp

theorem kc_packBytes_tailC (d : Digest) (k : ℕ) :
    (packBytes (d.toList ++ kcPadC)).getD k 0 =
      if k < 4 then (packBytes d.toList).getD k 0 else
        if k = 4 then 1 else if k = 16 then 0x0080000000000000 else 0 := by
  rw [kc_packBytes_append_getD _ _ (k := 4) (by simp), kc_packBytes_kcPadC]
  by_cases h4 : k < 4
  · simp [h4]
  · simp only [h4, ↓reduceIte]
    by_cases h5 : k = 4
    · subst h5; simp
    · by_cases h7 : k = 16
      · subst h7; simp
      · simp only [h5, h7, ↓reduceIte, show k - 4 ≠ 0 by omega, show k - 4 ≠ 12 by omega]

/-- **The absorbed block** of the chain message is `kcC0` of the packed words. -/
theorem kc_absorb_chain (d : Digest) :
    xorBlock zeroS (padB ⟨(tagChain :: d.toList).toArray⟩) 0 =
      kcC0 ((packBytes d.toList).getD 0 0) ((packBytes d.toList).getD 1 0)
        ((packBytes d.toList).getD 2 0) ((packBytes d.toList).getD 3 0) := by
  have hd : (padB ⟨(tagChain :: d.toList).toArray⟩).data.toList = tagChain :: (d.toList ++ kcPadC) := by
    rw [padB_data, ← kc_pad_chain]
  have hL := kc_laneAt_eq (padB ⟨(tagChain :: d.toList).toArray⟩)
  rw [hd] at hL
  simp only [xorBlock, zeroS, kcC0, UInt64.zero_xor]
  simp (disch := decide) only [hL, Nat.reduceMul, Nat.zero_add, Nat.reduceDiv, kc_packBytes_cons1,
    kc_packBytes_tailC, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceSub]
  simp [tagChain]

/-- **One chain step** is the permuted `kcC0` (through `KeccakFast.digestB_eq`). -/
theorem chainStep_kc (d : Digest) :
    chainStep d = outBytes (keccakFF (kcC0 ((packBytes d.toList).getD 0 0)
      ((packBytes d.toList).getD 1 0) ((packBytes d.toList).getD 2 0)
      ((packBytes d.toList).getD 3 0))) := by
  have hb : (⟨(tagChain :: d.toList).toArray⟩ : ByteArray).data.toList = tagChain :: d.toList := rfl
  rw [chainStep, ← hb, ← digestB_eq]
  have hs : (padB ⟨(tagChain :: d.toList).toArray⟩).size / rate = 1 := by
    have e := congrArg List.length (padB_data ⟨(tagChain :: d.toList).toArray⟩)
    rw [hb, kc_pad_chain] at e
    simp only [Array.length_toList, ByteArray.size_data, List.length_cons, List.length_append,
      Vector.length_toList, kcPadC, List.length_replicate] at e
    rw [e]; rfl
  show outBytes (loopB _ zeroS 0 ((padB _).size / rate)) = _
  rw [hs, loopB.eq_2, loopB.eq_1, kc_absorb_chain]

/-! ## The program's shape -/

theorem writes_kcRoundsIR_lt : ∀ (l : List UInt64) {y : ℕ}, Writes (kcRoundsIR l) y →
    128 ≤ y ∧ (y < 210 ∨ y = 211)
  | [], _, h => by simp [kcRoundsIR, Writes] at h
  | c :: l, y, h => by
    simp only [kcRoundsIR, kcRoundIR, Writes] at h
    rcases h with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | h
    · exact kcRoundPs_dst p hp
    · exact kcIotaPs_dst c p hp
    · exact writes_kcRoundsIR_lt l h

theorem writes_chainBody {y : ℕ} (h : Writes chainBody y) : 128 ≤ y ∧ y < 251 ∧ y ≠ 216 := by
  simp only [chainBody, Writes] at h
  rcases h with ⟨p, hp, rfl⟩ | h | ⟨p, hp, rfl⟩
  · have := kcInitC_dst p hp; omega
  · have := writes_kcRoundsIR_lt _ h; omega
  · have := copyBackPs_dst p hp; omega

theorem wf_chainBody : WF chainBody := by
  simp only [chainBody, WF]
  exact ⟨fun p hp => by have := (kcInitC_dst p hp).1; omega, wf_kcRoundsIR _,
    fun p hp => by have := (copyBackPs_dst p hp).1; omega⟩

theorem wf_leafTail : WF leafTail := by
  simp only [leafTail, WF, wf_kcRoundsIR, and_true]
  exact fun p hp => by have := (kcInitPs_dst p hp).1; omega

theorem wf_readAt (d pos : ℕ) (hd : 4 ≤ d) : WF (readAt d pos) := by
  simp only [readAt, WF, List.mem_singleton, forall_eq, Prim.dst, rA]
  omega

theorem kcInitC_length : kcInitC.length = 70 := rfl

theorem copyBackPs_length : copyBackPs.length = 4 := rfl

/-! ## The chain loop -/

theorem iterL_succ (f : St → St) (c k : ℕ) (s : St) :
    iterL f c (k + 1) s = iterL f c k (decS c (f s)) := rfl

theorem decS_o (c : ℕ) (s : St) : (decS c s).o = s.o := rfl

/-- The registers `212 … 215` hold the packed words of `d`. -/
def HoldsD (R : ℕ → Word) (d : Digest) : Prop :=
  R 212 = (packBytes d.toList).getD 0 0 ∧ R 213 = (packBytes d.toList).getD 1 0 ∧
    R 214 = (packBytes d.toList).getD 2 0 ∧ R 215 = (packBytes d.toList).getD 3 0

/-- **One chain step on the machine.** -/
theorem chainBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {d : Digest}
    (hd : HoldsD (rd s.M) d) :
    HoldsD (rd (semXIR I chainBody s).M) (chainStep d) ∧ (semXIR I chainBody s).o = s.o := by
  obtain ⟨h0, h1, h2, h3⟩ := hd
  have hi := kc_initC_run (rd s.M)
  rw [← kc_blk_rd (fun p hp => by have := kcInitC_dst p hp; omega) I s hM.1, h0, h1, h2, h3] at hi
  have z1 : regs ≤ (semXIR I (.blk kcInitC) s).M.size := by rw [size_sem]; exact hM.1
  have hR := kcRoundsIR_sem I rc.toList _ _ z1 hi.1 hi.2
  rw [Vector.foldl_toList, ← keccakFF] at hR
  have z2 : regs ≤ (semXIR I (kcRoundsIR rc.toList) (semXIR I (.blk kcInitC) s)).M.size := by
    rw [size_sem, size_sem]; exact hM.1
  have e3 := kc_blk_rd (ps := copyBackPs) (fun p hp => by have := copyBackPs_dst p hp; omega) I _ z2
  have hc : semXIR I chainBody s = semXIR I (.blk copyBackPs)
      (semXIR I (kcRoundsIR rc.toList) (semXIR I (.blk kcInitC) s)) := by
    simp only [chainBody, kc_sem_seq]
  rw [hc, e3]
  refine ⟨?_, by rw [kc_blk_o, hR.2, kc_blk_o]⟩
  obtain ⟨a0, a1, a2, a3, -⟩ := hR.1
  simp only [HoldsD, chainStep_kc, kc_packBytes_outBytes, copyBackPs, kcEval, List.foldl, kcStep,
    kc_upd_apply, ↓reduceIte, Nat.reduceEqDiff, eval_or, BitVec.or_self, a0, a1, a2, a3]
  simp

/-- **The chain loop**: `k` iterations hold `chainStep^[k] d` in `212 … 215`, output nothing. -/
theorem chain_iter (I : Array Word) : ∀ (k : ℕ) (s : St) (d : Digest), Inv s.M →
    HoldsD (rd s.M) d →
    HoldsD (rd (iterL (semXIR I chainBody) rCh k s).M) (chainStep^[k] d) ∧
      (iterL (semXIR I chainBody) rCh k s).o = s.o
  | 0, _, _, _, hd => ⟨hd, rfl⟩
  | k + 1, s, d, hM, hd => by
    have hb := chainBody_sem I s hM hd
    have hM' : Inv (decS rCh (semXIR I chainBody s)).M :=
      inv_of_frame (inv_sem I wf_chainBody hM) (size_decS ..)
        fun j hj => rd_decS (by simp only [rCh]; omega) _
    have hd' : HoldsD (rd (decS rCh (semXIR I chainBody s)).M) (chainStep d) := by
      obtain ⟨b0, b1, b2, b3⟩ := hb.1
      exact ⟨(rd_decS (by decide) _).trans b0, (rd_decS (by decide) _).trans b1,
        (rd_decS (by decide) _).trans b2, (rd_decS (by decide) _).trans b3⟩
    have ih := chain_iter I k _ _ hM' hd'
    rw [Function.iterate_succ_apply, iterL_succ]
    exact ⟨ih.1, ih.2.trans ((decS_o _ _).trans hb.2)⟩

/-- The loop's count: `min(M[n], K)`. -/
theorem entryK_val {c n : ℕ} {K : Word} {M : Mem} (hc : c ≠ cTmp) (hnc : n ≠ c) (hnt : n ≠ cTmp)
    (hcs : c < M.size) (hts : cTmp < M.size) :
    (rd (entryK c n K M) c).toNat = min (rd M n).toNat K.toNat := by
  unfold entryK; dsimp only
  have e1 : rd (M.setIfInBounds c K) c = K := rd_set_self hcs
  have e2 : rd (M.setIfInBounds c K) n = rd M n := rd_set_ne (Ne.symm hnc)
  rw [e1, e2]
  have hs1 : cTmp < (M.setIfInBounds c K).size := by simpa using hts
  by_cases hlt : rd M n < K
  · have hf : XOp.ltu.eval (rd M n) K = 1 := by simp [XOp.eval, hlt]
    rw [hf, rd_set_self hs1, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), rd_set_self (by simpa using hcs)]
    simp only [XOp.eval, BitVec.or_self]
    rw [rd_set_ne (Ne.symm hnt), e2]
    have := BitVec.lt_def.mp hlt; omega
  · have hf : XOp.ltu.eval (rd M n) K = 0 := by simp [XOp.eval, hlt]
    rw [hf, rd_set_self hs1, ite_eq_left_of_eq_true _ _ (eq_true rfl), rd_set_ne (Ne.symm hc), e1]
    have := BitVec.not_lt.mp hlt; rw [BitVec.le_def] at this; omega

/-- **The leaf tail on the machine**: from `h` in `212 … 215` and `n` in `216`, it outputs the
packed `leafStmt h n`. -/
theorem leafTail_sem (I : Array Word) (s : St) (hM : Inv s.M) {h : Digest} {n : ℕ}
    (hd : HoldsD (rd s.M) h) (hn : rd s.M 216 = toWord n) :
    (semXIR I leafTail s).o.toList = s.o.toList ++ packBytes (leafStmt h n).toList := by
  obtain ⟨w0, w1, w2, w3⟩ := hd
  have hi := kc_init_run (rd s.M)
  rw [← kc_blk_rd (fun p hp => by have := kcInitPs_dst p hp; omega) I s hM.1, w0, w1, w2, w3, hn]
    at hi
  have z6 : regs ≤ (semXIR I (.blk kcInitPs) s).M.size := by rw [size_sem]; exact hM.1
  have hR := kcRoundsIR_sem I rc.toList _ _ z6 hi.1 hi.2
  rw [Vector.foldl_toList, ← keccakFF] at hR
  simp only [leafTail, kc_sem_seq]
  simp only [kc_sem_out, Array.toList_push, hR.2, kc_blk_o, leafStmt_kc,
    kc_packBytes_outBytes, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨a0, a1, a2, a3, -⟩ := hR.1
  rw [a0, a1, a2, a3]

theorem kc_sem_loopK (I : Array Word) (c n : ℕ) (K : Word) (b : XIR) (s : St) :
    semXIR I (.loopK c n K b) s =
      iterL (semXIR I b) c (rd (entryK c n K s.M) c).toNat ⟨entryK c n K s.M, s.o⟩ := by
  simp only [semXIR]

/-! ## Statements (to prove) -/

theorem packBytes_dgW (a b c d : Word) : packBytes (dgW a b c d).toList = [a, b, c, d] := by
  show packBytes (wordsBytes [a, b, c, d]).toArray.toList = _
  rw [List.toList_toArray, packBytes_wordsBytes]

theorem dgW_packBytes (d : Digest) :
    dgW ((packBytes d.toList).getD 0 0) ((packBytes d.toList).getD 1 0)
      ((packBytes d.toList).getD 2 0) ((packBytes d.toList).getD 3 0) = d := by
  have hl : (packBytes d.toList).length = 4 := packBytes_digest_length d
  have hu := unpack_packBytes d.toList
  rw [List.take_of_length_le (by simp [wordsBytes_length, hl])] at hu
  have hP : [(packBytes d.toList).getD 0 0, (packBytes d.toList).getD 1 0,
      (packBytes d.toList).getD 2 0, (packBytes d.toList).getD 3 0] = packBytes d.toList := by
    generalize packBytes d.toList = L at hl ⊢
    match L, hl with
    | [_, _, _, _], _ => rfl
  apply Vector.toArray_inj.mp
  show (wordsBytes _).toArray = d.toArray
  rw [hP, hu]
  rfl

theorem digW_length (a b c d nw : Word) : (digW a b c d nw).length = 4 := by
  simp [digW, packBytes_length]

theorem wf_digIR (a nI : ℕ) : WF (digIR a nI) := by
  have hw : ¬ Writes chainBody 100 := fun h => by have := writes_chainBody h; omega
  simp only [digIR, WF, wf_readAt _ _ (by decide : 4 ≤ 212), wf_readAt _ _ (by decide : 4 ≤ 213),
    wf_readAt _ _ (by decide : 4 ≤ 214), wf_readAt _ _ (by decide : 4 ≤ 215),
    wf_readAt _ _ (by decide : 4 ≤ 216), wf_chainBody, wf_leafTail, rCh, cTmp, regs, hw]
  decide

theorem noLoopT_digIR (a nI : ℕ) : NoLoopT (digIR a nI) := by
  simp only [digIR, readAt, NoLoopT, chainBody, leafTail, noLoopT_kcRoundsIR, and_self]

/-- The registers `digIR` may write: `rA = 64`, the counter, the compiler's scratch, `128 … 250`. -/
theorem writes_digIR {a nI y : ℕ} (h : Writes (digIR a nI) y) :
    y = 64 ∨ y = rCh ∨ y = cTmp ∨ (128 ≤ y ∧ y < 251) := by
  simp only [rCh, cTmp]
  have hc : ∀ (d : ℕ) (w : Word), (Prim.const d w).dst = d := fun _ _ => rfl
  simp only [digIR, readAt, leafTail, Writes, List.mem_singleton, exists_eq_left, hc, rA, rCh,
    cTmp, or_false] at h
  rcases h with (h | h) | (h | h) | (h | h) | (h | h) | (h | h) | (h | h | h) | h | h
  all_goals first
    | omega
    | (have := writes_chainBody h; omega)
    | (obtain ⟨p, hp, rfl⟩ := h; have := kcInitPs_dst p hp; omega)
    | (have := writes_kcRoundsIR _ h; omega)

theorem outs_digIR (a nI t : ℕ) : outs (digIR a nI) t = 4 := by
  simp [digIR, readAt, leafTail, chainBody, outs, outs_kcRoundsIR]

theorem cost_digIR (a nI t : ℕ) : cost (digIR a nI) t ≤ 2 ^ 34 := by
  simp only [digIR, readAt, leafTail, chainBody, cost, cost_kcRoundsIR, rc_toList_length,
    kcInitPs_length, kcInitC_length, copyBackPs_length, List.length_singleton, blkSteps,
    BitVec.toNat_ofNat, chainCap]
  norm_num

theorem sizeIR_digIR (a nI : ℕ) : sizeIR (digIR a nI) ≤ 2 ^ 16 := by
  simp only [digIR, readAt, leafTail, chainBody, sizeIR, sizeIR_kcRoundsIR, rc_toList_length,
    kcInitPs_length, kcInitC_length, copyBackPs_length, List.length_singleton, blkSteps]
  norm_num

/-- **The derived leaf statement on the machine**: `digIR a nI` appends `digW` of tape words
`a … a+3` and `nI` to the output. -/
theorem digIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {a nI : ℕ} (ha : a + 4 < 2 ^ 64)
    (hn : nI < 2 ^ 64) :
    (semXIR I (digIR a nI) s).o.toList = s.o.toList ++
      digW (I.getD a 0) (I.getD (a + 1) 0) (I.getD (a + 2) 0) (I.getD (a + 3) 0) (I.getD nI 0) := by
  have hr : (212 : ℕ) < regs ∧ (213 : ℕ) < regs ∧ (214 : ℕ) < regs ∧ (215 : ℕ) < regs ∧
      (216 : ℕ) < regs := by decide
  obtain ⟨e1, o1, z1⟩ := kc_readAt I s hM.1 hr.1 (pos := a) (by omega)
  obtain ⟨e2, o2, z2⟩ := kc_readAt I _ z1 hr.2.1 (pos := a + 1) (by omega)
  obtain ⟨e3, o3, z3⟩ := kc_readAt I _ z2 hr.2.2.1 (pos := a + 2) (by omega)
  obtain ⟨e4, o4, z4⟩ := kc_readAt I _ z3 hr.2.2.2.1 (pos := a + 3) (by omega)
  obtain ⟨e5, o5, z5⟩ := kc_readAt I _ z4 hr.2.2.2.2 (pos := nI) hn
  have hM5 : Inv (semXIR I (readAt 216 nI) (semXIR I (readAt 215 (a + 3))
      (semXIR I (readAt 214 (a + 2)) (semXIR I (readAt 213 (a + 1))
        (semXIR I (readAt 212 a) s))))).M :=
    inv_sem I (wf_readAt _ _ (by decide)) (inv_sem I (wf_readAt _ _ (by decide))
      (inv_sem I (wf_readAt _ _ (by decide)) (inv_sem I (wf_readAt _ _ (by decide))
        (inv_sem I (wf_readAt _ _ (by decide)) hM))))
  generalize hs5 : semXIR I (readAt 216 nI) (semXIR I (readAt 215 (a + 3))
    (semXIR I (readAt 214 (a + 2)) (semXIR I (readAt 213 (a + 1))
      (semXIR I (readAt 212 a) s)))) = s5 at e5 o5 z5 hM5
  have w : ∀ i, i = 212 ∨ i = 213 ∨ i = 214 ∨ i = 215 ∨ i = 216 →
      rd s5.M i = upd (upd (upd (upd (upd (rd s.M) 212 (I.getD a 0)) 213 (I.getD (a + 1) 0)) 214
        (I.getD (a + 2) 0)) 215 (I.getD (a + 3) 0)) 216 (I.getD nI 0) i := by
    intro i hi
    rw [e5, e4, e3, e2, e1]
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [upd, rA]
  -- the loop's entry
  have hcT : cTmp < s5.M.size := by have := hM5.1; simp only [regs, cTmp] at *; omega
  have hcS : rCh < s5.M.size := by have := hM5.1; simp only [regs, rCh] at *; omega
  have hcnt : (rd (entryK rCh 216 (BitVec.ofNat 64 chainCap) s5.M) rCh).toNat =
      min (I.getD nI 0).toNat chainCap := by
    rw [entryK_val (by decide) (by decide) (by decide) hcS hcT, w 216 (by omega)]
    simp [upd, chainCap]
  have fr : ∀ i, i ≠ rCh → i ≠ cTmp →
      rd (entryK rCh 216 (BitVec.ofNat 64 chainCap) s5.M) i = rd s5.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hM0 : Inv (entryK rCh 216 (BitVec.ofNat 64 chainCap) s5.M) :=
    inv_of_frame hM5 (size_entryK ..) fun j hj => fr j (by simp only [rCh]; omega)
      (by simp only [cTmp]; omega)
  have hP := packBytes_dgW (I.getD a 0) (I.getD (a + 1) 0) (I.getD (a + 2) 0) (I.getD (a + 3) 0)
  have hD0 : HoldsD (rd (entryK rCh 216 (BitVec.ofNat 64 chainCap) s5.M))
      (dgW (I.getD a 0) (I.getD (a + 1) 0) (I.getD (a + 2) 0) (I.getD (a + 3) 0)) := by
    simp only [HoldsD, hP]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      rw [fr _ (by decide) (by decide), w _ (by omega)] <;> simp [upd]
  have hn0 : rd (entryK rCh 216 (BitVec.ofNat 64 chainCap) s5.M) 216 = I.getD nI 0 := by
    rw [fr _ (by decide) (by decide), w _ (by omega)]; simp [upd]
  -- the loop
  generalize hs0 : (⟨entryK rCh 216 (BitVec.ofNat 64 chainCap) s5.M, s5.o⟩ : St) = s0
  have hM0' : Inv s0.M := by rw [← hs0]; exact hM0
  have hD0' := hD0
  have hn0' := hn0
  rw [show entryK rCh 216 (BitVec.ofNat 64 chainCap) s5.M = s0.M by rw [← hs0]] at hD0' hn0'
  have hit := chain_iter I (min (I.getD nI 0).toNat chainCap) s0 _ hM0' hD0'
  have hinv : ∀ s', Inv s'.M → Inv (semXIR I chainBody s').M := fun s' h' => inv_sem I wf_chainBody h'
  have hM6 := iterL_inv (c := rCh) (by decide) hinv (min (I.getD nI 0).toNat chainCap) s0 hM0'
  have h216 := iterL_frame (c := rCh) (i := 216) (by decide) (by decide) hinv
    (fun s' h' => frame I chainBody s' wf_chainBody h' 216 (by decide)
      (fun h => (writes_chainBody h).2.2 rfl)) (min (I.getD nI 0).toNat chainCap) s0 hM0'
  rw [hn0'] at h216
  have hL := leafTail_sem I _ hM6 hit.1 (n := (I.getD nI 0).toNat) (by rw [h216]; simp [toWord])
  simp only [digIR, kc_sem_seq]
  rw [hs5, kc_sem_loopK, hcnt, hs0, hL, hit.2, ← hs0, o5, o4, o3, o2, o1]
  rfl

end WsLeaf.X
