-- New for lvm (WP-13a), after FR's `FRXSpec` (`parse_isK`, `tape_byte0`, `E_W`), `FRXLeaf` (`E_leaf`) and
-- `FRXNodeRun` (`E_node`, `E_node_out`; rf-k/submissions/flock-recursive/lean@kk/base): what `EX` returns.
import LvmXTop
import LvmLog
import LvmXReasm

/-!
# What the extractor returns (BLUEPRINT §6.2)

On an `S` proof (`π[0] = 'S'`, `|π| = piSize`):

* **`EX_leaf`** (`b = 0`, every log): `leafW π = leaf s n` from the header;
* **`EX_node`** (`b ≠ 0`, in the domain): if the log has no state hit (`notStateHit_of_notBad`: implied
  by WP-5's `¬ Bad`), the first-match chain answers the six fold challenges (`αd`), and the decoder of
  `C_rec` (WP-13b's `decodeRec` on the first-preimage reading `readWd` under π's cap, the challenges
  `alphaE (αd i)` and π's final `f1E π`) returns `out`, then `EX = some (Xwit π w)`, `w` the words of
  `out`: the node `c_L, leafStmt h n` with the child `⟨reassembleL tr', tr', σ'⟩` read off the decoded
  stream and the right leaf `⟨encode (leaf s n), [], σ_leaf⟩`;
* **`EX_node_out`** (`b ≠ 0`, outside the domain): the search under π's `vk`.
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## The inputs of the decoder, as pure functions of π and the log -/

/-- Word `m` of a digest. -/
def dw (d : Digest) (m : ℕ) : Word := (packBytes d.toList).getD m 0

/-- A fold challenge from its chain answer: lanes 0–2 as an `E` element (`rdE`'s coordinates). -/
def alphaE (d : Digest) : BF64.Ext3 := mkE (wK (dw d 0)) (wK (dw d 1)) (wK (dw d 2))

/-- `f₁`'s coefficient `v` from π (`E` scalars of 3 words at π word `f1Off / 8`). -/
def f1E (π : Proof) (v : ℕ) : BF64.Ext3 :=
  mkE (wK (pw π (f1Off pX / 8 + 3 * v))) (wK (pw π (f1Off pX / 8 + 3 * v + 1)))
    (wK (pw π (f1Off pX / 8 + 3 * v + 2)))

/-- `C_rec`'s cap from π: 128 digests at π word `capRecOff / 8`. -/
def capRec (π : Proof) : List Digest :=
  (List.range 128).map fun e => hdD π (capRecOff pX / 8 + 4 * e)

/-- The decoded message's words. -/
def wOut (out : List BF64) (i : ℕ) : Word := BF64.toBitVec (out.getD i 0)

/-! ## WP-5's bad events give no state hit -/

theorem notStateHit_of_notBad {L : Log} (h : ¬ Lvm.FS.Bad L) : ¬ StateHit L := by
  rintro ⟨i, j, hij, hj, hs⟩
  refine h (Or.inr (Or.inr ⟨i, j, hij, hj, ?_⟩))
  unfold stateIn at hs
  split_ifs at hs with hc
  refine ⟨hc.2, 0, hc.1, ?_⟩
  have e := (Option.some.inj hs).symm
  rw [e]
  apply Vector.ext
  intro k hk
  simp [Lvm.FS.win, Lvm.FS.dg, Lvm.FS.qb]

/-! ## The header fields: packed words and `V_S`'s byte reads -/

/-- **`hdD` is `V_S`'s `digestAt`** (`LvmDriver`) at the aligned offset `8j`. -/
theorem hdD_eq_digestAt (π : Proof) (j : ℕ) : hdD π j = digestAt π (8 * j) := by
  apply Vector.ext
  intro i hi
  simp only [hdD, digW, digestAt, Vector.getElem_ofFn]
  rw [← wordByte_eq_getD]
  have e : wordByte (wsAt (pw π) j 4) i = wordByte (packBytes π.data.toList) (8 * j + i) := by
    simp only [wordByte, wsAt, pw]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
      show (8 * j + i) / 8 = j + i / 8 by omega, show (8 * j + i) % 8 = i % 8 by omega]
  rw [e, wordByte_packBytes]
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  first
    | rfl
    | (simp only [ByteArray.get!]; rfl)
    | (cases π; simp only [ByteArray.get!, getElem!_def]; split <;> simp_all <;> rfl)

/-! ## The parse on an `S` proof -/

theorem lowByte (w : Word) : (w &&& 0xFF).toNat = w.toNat % 256 := by
  rw [BitVec.toNat_and, show (0xFF : Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The low byte of tape word 5 is the proof's first byte (FR `tape_byte0`). -/
theorem tape_byte0 (c : Digest) (π : Proof) (L : Log) {b : UInt8} (h0 : π.data[0]? = some b) :
    ((extractorInput c π L).getD 5 0).toNat % 256 = b.toNat := by
  have hpos : 0 < π.size := by
    rcases Nat.eq_zero_or_pos π.size with h | h
    · simp [ByteArray.size, Array.size_eq_zero_iff.mp h] at h0
    · exact h
  have := tape_getD_proof c π L (j := 0) (by omega)
  rw [Nat.add_zero] at this
  rw [this]
  have hw := wordByte_packBytes π.data.toList 0
  simp only [wordByte, Nat.zero_div, Nat.zero_mod, pow_zero, Nat.div_one] at hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [packBytes_length, ← WitnessSending.size_eq_length]; omega), Option.getD_some] at hw
  have h1 : π.data.toList.getD 0 0 = b := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, h0, Option.getD_some]
  rw [h1] at hw
  rw [← hw, Nat.toUInt8_eq, UInt8.toNat_ofNat']

theorem parse_isK (pz : ℕ) (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I (parseIR pz) s).M rIsK = (if I.getD 5 0 &&& 0xFF = kindS then 1 else 0) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [parseIR, readAt, kindPs, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rB0,
    rIsK, rT, rIsSz]
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne, XOp.eval]

/-- **The SNARK branch's run**: on an `S` proof of `piSize` bytes the program's denotation is the
SNARK branch's output from the parse's state. -/
theorem den_S (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (h0 : π.data[0]? = some 0x53) :
    ∃ s1 : St, Inv s1.M ∧ s1.M.size = memX + mpwX * (extractorInput c π L).length ∧ s1.o = #[] ∧
      den memX mpwX (extIRWith (piSize pX) decX) (extractorInput c π L) =
        (semXIR (extractorInput c π L).toArray decX s1).o.toList := by
  set I := (extractorInput c π L).toArray with hI
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0' : Inv (initSt (memX + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  refine ⟨semXIR I (parseIR (piSize pX)) (initSt (memX + mpwX * (extractorInput c π L).length)),
    inv_sem I (wf_extIRWith (pz := piSize pX) wf_decX).1 h0', by rw [size_sem, initSt_M, size_runPrims,
      Array.size_replicate], by rw [parse_o, initSt_o], ?_⟩
  have hk : rd (semXIR I (parseIR (piSize pX)) (initSt (memX + mpwX * (extractorInput c π L).length))).M
      rIsK ≠ 0 := by
    rw [parse_isK _ I _ h0']
    have hb := tape_byte0 c π L h0
    have e : I.getD 5 0 &&& 0xFF = kindS := by
      apply BitVec.eq_of_toNat_eq
      rw [lowByte, hI, getD_toArray, hb]; rfl
    rw [if_pos e]; decide
  have hz : rd (semXIR I (parseIR (piSize pX)) (initSt (memX + mpwX * (extractorInput c π L).length))).M
      rIsSz ≠ 0 := by
    rw [parse_regs _ I _ h0', hI, getD_toArray, tape_getD4, hs]
    rw [if_pos (by rfl)]; decide
  rw [den, extIRWith, semXIR_seq, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]

/-! ## The leaf -/

theorem pw_lt (π : Proof) (j : ℕ) : (pw π j).toNat < 2 ^ 64 := (pw π j).isLt

theorem readAt_val (I : Array Word) (s : St) (hM : Inv s.M) {d pos : ℕ} (hd : d < regs) (hd4 : 4 ≤ d)
    (hda : d ≠ rA) (hp : pos < 2 ^ 64) :
    rd (semXIR I (readAt d pos) s).M d = I.getD pos 0 ∧
    (∀ y, y ≠ d → y ≠ rA → rd (semXIR I (readAt d pos) s).M y = rd s.M y) ∧
    Inv (semXIR I (readAt d pos) s).M ∧ (semXIR I (readAt d pos) s).M.size = s.M.size ∧
    (semXIR I (readAt d pos) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs hd
  refine ⟨rd_readAt I s hM hd hp, fun y h1 h2 => ?_, inv_sem I (by
    simp only [readAt, WF, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false, forall_eq, rA]
    exact ⟨by decide, hd4⟩) hM, size_sem .., rfl⟩
  simp only [readAt, semXIR, runPrims, List.foldl, Prim.run]
  rw [rd_set_ne (Ne.symm h1), rd_set_ne (Ne.symm h2)]

/-- **`EX` on an `S` proof with `b = 0`**, on every log: the leaf witness of its header. -/
theorem EX_leaf (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 = 0) :
    EX A c π L = some (leafW π) := by
  by_cases hD : InDomE c π L
  · rw [EX, if_pos hD, EdX, Eden]
    obtain ⟨s1, hM1, -, ho1, hden⟩ := den_S c π L hs h0
    rw [hden]
    set I := (extractorInput c π L).toArray with hI
    obtain ⟨b1, -, hM2, -, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
      (by decide) (by norm_num)
    rw [decX, semXIR_seq]
    generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 bo
    have h6 : I.getD 6 0 = 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pw c π L hs (by norm_num), hb]
    rw [semXIR_ite, if_pos (by rw [b1, h6]), leafIR, semXIR_seq]
    obtain ⟨e1, -⟩ := emitIR_sem I s2 hM2 (toWord 0)
    have hM3 := inv_sem I (wf_emitIR (toWord 0)) hM2
    generalize semXIR I (emitIR (toWord 0)) s2 = s3 at e1 hM3
    obtain ⟨t1, -⟩ := tcpIR_sem I s3 hM3 (a := 15) (n := 5) (by norm_num)
    rw [t1, e1, bo, ho1]
    have t2 := wsAt_tape c π L hs (a := 10) (n := 5) (by norm_num)
    simp only [show (5 + 10 : ℕ) = 15 from rfl] at t2
    rw [t2]
    have hw : witWords (leafW π) = toWord 0 :: wsAt (pw π) 10 5 := by
      simp only [leafW, witWords, hdD, packBytes_digW (length_wsAt _ _ _), toWord_toNat',
        show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
      simp [wsAt]
    rw [Array.toList_empty, List.nil_append, List.singleton_append, ← hw]
    exact decodeWit_witWords _ (pw π 14).isLt
  · rw [EX, if_neg hD, EoutX, if_pos h0, if_pos hs, if_pos hb]

/-- **`EX` on an `S` node proof outside the domain**: the search under the key the proof carries. -/
theorem EX_node_out (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : ¬ InDomE c π L) (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0) :
    EX A c π L = search A (hdD π 2) c := by
  rw [EX, if_neg hD, EoutX, if_pos h0, if_pos hs, if_neg hb]

/-! ## The node -/

theorem hasOut_storesIR : ∀ (b : ℕ) (ws : List Word), hasOut (storesIR b ws) = false
  | _, [] => rfl
  | b, _ :: ws => by simp only [storesIR, hasOut, hasOut_storesIR (b + 1) ws, Bool.or_false]

/-- `hasOut` of a `seq`, as a rewrite (not an `rfl`-lemma: `simp` records the step, so the kernel
does not re-derive it by evaluating `hasOut` on the operands). -/
theorem hasOut_seq (p q : XIR) : hasOut (.seq p q) = (hasOut p || hasOut q) :=
  (rfl : hasOut (.seq p q) = _).trans rfl

theorem hasOut_chainL : hasOut chainL = false := by
  simp only [chainL, chainIR, hasOut_seq, hasOut_storesIR, cntIR, cntBody, readAt, sdL, startPs, wordIR,
    lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, st4IR, stNext, nextIR, nextPre]
  simp only [hasOut, Bool.or_false]

theorem hasOut_idx : hasOut (idxIR4 memX pLX) = false := by
  simp [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, stepIR, blockIR,
    cmpIR, cmpWord, aposIR, readAt, hasOut]

theorem wf_chainL : WF chainL :=
  wf_chainIR (posL (piSize pX)) (nChain pX) chTabL wf_sdL (nw_sdL _ (by decide) (by decide) (by decide))

theorem blk_const_val (I : Array Word) (s : St) (hM : Inv s.M) {d : ℕ} (hd : d < regs) (w : Word) :
    rd (semXIR I (.blk [.const d w]) s).M d = w := by
  have hs := hM.1
  rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
  exact rd_set_self (by omega)

theorem blk_const_ne (I : Array Word) (s : St) {d : ℕ} (w : Word) {y : ℕ} (hy : y ≠ d) :
    rd (semXIR I (.blk [.const d w]) s).M y = rd s.M y :=
  rd_blk_of_not_dst I _ s (by simp [Prim.dst]; exact Ne.symm hy)

theorem rdK_toBitVec (M : Mem) (a : ℕ) : BF64.toBitVec (rdK M a) = rd M a := rfl

theorem rdE_eq (M : Mem) (a : ℕ) : rdE M a = mkE (wK (rd M a)) (wK (rd M (a + 1))) (wK (rd M (a + 2))) := rfl

theorem alphaPos_eq (j : ℕ) : alphaPos pX j = 1035 + j := by
  rw [alphaPos, layout_P20.1]

/-- One 3-word copy of the `α` copies. -/
theorem mcp3 (I : Array Word) (s : St) (hM : Inv s.M) (hsz : 2 ^ 25 ≤ s.M.size) {src dst : ℕ}
    (hd : regs ≤ dst) (hd2 : dst + 3 ≤ 2 ^ 24) (hsr : 2 ^ 24 ≤ src) (hsr2 : src + 3 ≤ 2 ^ 25) :
    (∀ i < 3, rd (semXIR I (mcpIR 3 src 1 dst) s).M (dst + i) = rd s.M (src + i)) ∧
    (∀ r, regs ≤ r → (r < dst ∨ dst + 3 ≤ r) → rd (semXIR I (mcpIR 3 src 1 dst) s).M r = rd s.M r) ∧
    Inv (semXIR I (mcpIR 3 src 1 dst) s).M ∧ (semXIR I (mcpIR 3 src 1 dst) s).M.size = s.M.size ∧
    (semXIR I (mcpIR 3 src 1 dst) s).o = s.o := by
  obtain ⟨a1, a2, a3⟩ := mcpIR_sem I s hM (n := 3) (src := src) (str := 1) (dst := dst) (by norm_num)
    (by omega) (by norm_num) hd (by omega) (by omega) (fun i hi => .inr (by omega))
    (fun i hi => by simp only [regs] at *; omega)
  exact ⟨fun i hi => by rw [a1 i hi, Nat.one_mul], a2, a3, size_sem .., sem_o I _ s rfl⟩

/-- **The `α` copies**: `α_j`'s answer words 0–2 at `aB + 3j`. -/
theorem acpIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hsz : 2 ^ 25 ≤ s.M.size) :
    (∀ j < 6, ∀ m < 3, rd (semXIR I acpIR s).M (aBX + 3 * j + m) = rd s.M (ansB + 4 * alphaPos pX j + m)) ∧
    (∀ r, regs ≤ r → (r < aBX ∨ aBX + 18 ≤ r) → rd (semXIR I acpIR s).M r = rd s.M r) ∧
    Inv (semXIR I acpIR s).M ∧ (semXIR I acpIR s).M.size = s.M.size ∧ (semXIR I acpIR s).o = s.o := by
  have hA : ∀ j, ansB + 4 * alphaPos pX j = 16793600 + 4 * (1035 + j) := fun j => by
    rw [alphaPos_eq, ansB_eq]
  simp only [acpIR, hA]
  simp only [aBX]
  obtain ⟨p1, q1, i1, z1, o1⟩ := mcp3 I s hM hsz (src := 16793600 + 4 * (1035 + 0)) (dst := 2 ^ 19)
    (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1035 + 0)) 1 (2 ^ 19)) s = s1 at p1 q1 i1 z1 o1
  obtain ⟨p2, q2, i2, z2, o2⟩ := mcp3 I s1 i1 (by omega) (src := 16793600 + 4 * (1035 + 1))
    (dst := 2 ^ 19 + 3) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1035 + 1)) 1 (2 ^ 19 + 3)) s1 = s2 at p2 q2 i2 z2 o2
  obtain ⟨p3, q3, i3, z3, o3⟩ := mcp3 I s2 i2 (by omega) (src := 16793600 + 4 * (1035 + 2))
    (dst := 2 ^ 19 + 6) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1035 + 2)) 1 (2 ^ 19 + 6)) s2 = s3 at p3 q3 i3 z3 o3
  obtain ⟨p4, q4, i4, z4, o4⟩ := mcp3 I s3 i3 (by omega) (src := 16793600 + 4 * (1035 + 3))
    (dst := 2 ^ 19 + 9) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1035 + 3)) 1 (2 ^ 19 + 9)) s3 = s4 at p4 q4 i4 z4 o4
  obtain ⟨p5, q5, i5, z5, o5⟩ := mcp3 I s4 i4 (by omega) (src := 16793600 + 4 * (1035 + 4))
    (dst := 2 ^ 19 + 12) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1035 + 4)) 1 (2 ^ 19 + 12)) s4 = s5 at p5 q5 i5 z5 o5
  obtain ⟨p6, q6, i6, z6, o6⟩ := mcp3 I s5 i5 (by omega) (src := 16793600 + 4 * (1035 + 5))
    (dst := 2 ^ 19 + 15) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1035 + 5)) 1 (2 ^ 19 + 15)) s5 = s6 at p6 q6 i6 z6 o6
  have hR : ∀ r, regs ≤ r → (r < 2 ^ 19 ∨ 2 ^ 19 + 18 ≤ r) → rd s6.M r = rd s.M r := fun r hr h => by
    rw [q6 r hr (by omega), q5 r hr (by omega), q4 r hr (by omega), q3 r hr (by omega), q2 r hr (by omega),
      q1 r hr (by omega)]
  have hsrc : ∀ j < 6, ∀ m < 3, regs ≤ 16793600 + 4 * (1035 + j) + m ∧
      (16793600 + 4 * (1035 + j) + m < 2 ^ 19 ∨ 2 ^ 19 + 18 ≤ 16793600 + 4 * (1035 + j) + m) :=
    fun j _ m _ => ⟨by simp only [regs]; omega, .inr (by omega)⟩
  refine ⟨fun j hj m hm => ?_, hR, i6, by rw [z6, z5, z4, z3, z2, z1], by rw [o6, o5, o4, o3, o2, o1]⟩
  have hr : regs ≤ 2 ^ 19 + 3 * j + m := by simp only [regs]; omega
  interval_cases j
  · rw [q6 _ hr (by omega), q5 _ hr (by omega), q4 _ hr (by omega), q3 _ hr (by omega),
      q2 _ hr (by omega), show 2 ^ 19 + 3 * 0 + m = 2 ^ 19 + m by omega, p1 m hm]
  · rw [q6 _ hr (by omega), q5 _ hr (by omega), q4 _ hr (by omega), q3 _ hr (by omega),
      show 2 ^ 19 + 3 * 1 + m = 2 ^ 19 + 3 + m by omega, p2 m hm, q1 _ (hsrc 1 (by norm_num) m hm).1
        (by omega)]
  · rw [q6 _ hr (by omega), q5 _ hr (by omega), q4 _ hr (by omega),
      show 2 ^ 19 + 3 * 2 + m = 2 ^ 19 + 6 + m by omega, p3 m hm,
      q2 _ (hsrc 2 (by norm_num) m hm).1 (by omega), q1 _ (hsrc 2 (by norm_num) m hm).1 (by omega)]
  · rw [q6 _ hr (by omega), q5 _ hr (by omega), show 2 ^ 19 + 3 * 3 + m = 2 ^ 19 + 9 + m by omega,
      p4 m hm, q3 _ (hsrc 3 (by norm_num) m hm).1 (by omega), q2 _ (hsrc 3 (by norm_num) m hm).1 (by omega),
      q1 _ (hsrc 3 (by norm_num) m hm).1 (by omega)]
  · rw [q6 _ hr (by omega), show 2 ^ 19 + 3 * 4 + m = 2 ^ 19 + 12 + m by omega, p5 m hm,
      q4 _ (hsrc 4 (by norm_num) m hm).1 (by omega), q3 _ (hsrc 4 (by norm_num) m hm).1 (by omega),
      q2 _ (hsrc 4 (by norm_num) m hm).1 (by omega), q1 _ (hsrc 4 (by norm_num) m hm).1 (by omega)]
  · rw [show 2 ^ 19 + 3 * 5 + m = 2 ^ 19 + 15 + m by omega, p6 m hm,
      q5 _ (hsrc 5 (by norm_num) m hm).1 (by omega), q4 _ (hsrc 5 (by norm_num) m hm).1 (by omega),
      q3 _ (hsrc 5 (by norm_num) m hm).1 (by omega), q2 _ (hsrc 5 (by norm_num) m hm).1 (by omega),
      q1 _ (hsrc 5 (by norm_num) m hm).1 (by omega)]

/-- **After the decoder**: with the flag set and the message `w` at `mB`, the node output. -/
theorem okXIR_sem (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) (s8 : St)
    (hM8 : Inv s8.M) (hsz : sgB + nCp ≤ s8.M.size) (hf : rd s8.M (okB dBX) = 1) (w : ℕ → Word)
    (hw : ∀ i < 2 ^ 19, rd s8.M (mB dBX + i) = w i) :
    (semXIR (extractorInput c π L).toArray okXIR s8).o.toList = s8.o.toList ++ outWords π w := by
  have hs8 := hM8.1
  simp only [regs] at hs8
  rw [okXIR, semXIR_seq]
  have e1 := blk_const_val (extractorInput c π L).toArray s8 hM8 (d := eA) (by decide) (toWord (okB dBX))
  have g1 : ∀ y, y ≠ eA → rd (semXIR (extractorInput c π L).toArray (.blk [.const eA (toWord (okB dBX))]) s8).M y =
      rd s8.M y := fun y hy => blk_const_ne _ s8 _ hy
  have hM9 := inv_sem (extractorInput c π L).toArray (P := .blk [.const eA (toWord (okB dBX))])
    (by simp +decide [WF, Prim.dst, eA]) hM8
  have z9 := size_sem (extractorInput c π L).toArray (.blk [.const eA (toWord (okB dBX))]) s8
  have o9 : (semXIR (extractorInput c π L).toArray (.blk [.const eA (toWord (okB dBX))]) s8).o = s8.o := rfl
  generalize semXIR (extractorInput c π L).toArray (.blk [.const eA (toWord (okB dBX))]) s8 = s9 at e1 g1 hM9 z9 o9
  have hok64 : okB dBX < 2 ^ 64 := by simp only [okB, dBX]; norm_num
  have hs9 := hM9.1
  simp only [regs] at hs9
  have eL : semXIR (extractorInput c π L).toArray (.load eW eA) s9 =
      ⟨s9.M.setIfInBounds eW (rd s9.M (rd s9.M eA).toNat), s9.o⟩ := rfl
  have l1 : rd (semXIR (extractorInput c π L).toArray (.load eW eA) s9).M eW = rd s9.M (okB dBX) := by
    rw [eL]; show rd (s9.M.setIfInBounds eW _) eW = _
    rw [rd_set_self (by simp only [eW]; omega), e1, toNat_toWord hok64]
  have l2 : ∀ i, i ≠ eW → rd (semXIR (extractorInput c π L).toArray (.load eW eA) s9).M i = rd s9.M i :=
    fun i hi => by rw [eL]; exact rd_set_ne (Ne.symm hi)
  have hM10 := inv_sem (extractorInput c π L).toArray (P := .load eW eA) (show 4 ≤ eW by decide) hM9
  have z10 := size_sem (extractorInput c π L).toArray (.load eW eA) s9
  have o10 : (semXIR (extractorInput c π L).toArray (.load eW eA) s9).o = s9.o := rfl
  rw [semXIR_seq]
  generalize semXIR (extractorInput c π L).toArray (.load eW eA) s9 = s10 at l1 l2 hM10 z10 o10
  have hflag : rd s10.M eW ≠ 0 := by
    rw [l1, g1 _ (by simp only [okB, dBX, eA]; omega), hf]; decide
  rw [semXIR_ite, if_neg hflag]
  have hw10 : ∀ i < 2 ^ 19, rd s10.M (mB dBX + i) = w i := fun i hi => by
    rw [l2 _ (by simp only [mB, dBX, eW]; omega), g1 _ (by simp only [mB, dBX, eA]; omega), hw i hi]
  have hsz10 : sgB + nCp ≤ s10.M.size := by rw [z10, z9]; exact hsz
  rw [outIR_sem c π L hs s10 hM10 (mB := mB dBX) (by simp only [regs, mB, dBX]; norm_num)
    (by simp only [mB, dBX, sgB]; norm_num) hsz10 w hw10, o10, o9]

/-- **`EX` on an `S` node proof in the domain** (BLUEPRINT §6.2): with no state hit, the six fold
challenges answered by the first-match chain, and the decoder returning `out`, the node witness
`Xwit π (wOut out)`. -/
theorem EX_node (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : InDomE c π L) (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0)
    (hS : ¬ StateHit L) (αd : ℕ → Digest)
    (hα : ∀ j < 6, fmAns (fsQL π) zeroDL L (alphaPos pX j) = some (αd j)) (out : List BF64)
    (hdec : decodeRec (readWd L (capRec π)) (fun i => alphaE (αd i)) (f1E π) = some out) :
    EX A c π L = some (Xwit π (wOut out)) := by
  obtain ⟨hπ, hq, ht⟩ := hD
  rw [EX, if_pos ⟨hπ, hq, ht⟩, EdX, Eden]
  obtain ⟨s1, hM1, z1, ho1, hden⟩ := den_S c π L hs h0
  rw [hden]
  set I := (extractorInput c π L).toArray with hI
  have hLt : L.length ≤ (extractorInput c π L).length := by
    have h1 := length_logEntries L
    rw [tape_eq]
    simp only [List.length_append, logWords, List.length_cons]
    omega
  simp only [memX, mpwX] at z1
  -- the flag
  obtain ⟨b1, -, hM2, z2, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
    (by decide) (by norm_num)
  rw [decX, semXIR_seq]
  generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 z2 bo
  have h6 : I.getD 6 0 ≠ 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pw c π L hs (by norm_num)]; exact hb
  rw [semXIR_ite, if_neg (by rw [b1]; exact h6), nodeIR, semXIR_seq]
  -- 1. the index
  have hM3 := inv_sem I (wf_idxIR4 memX pLX) hM2
  have z3 := size_sem I (idxIR4 memX pLX) s2
  have o3 := sem_o I (idxIR4 memX pLX) s2 hasOut_idx
  rw [semXIR_seq]
  generalize hs3 : semXIR I (idxIR4 memX pLX) s2 = s3 at hM3 z3 o3
  -- 2. the chain
  obtain ⟨ch1, ch2⟩ := chainL_spec c π L hs hq ht hS s3 hM3 (by rw [z3, z2, z1]; simp only [chEnd]; omega)
  have hM4 := inv_sem I wf_chainL hM3
  have z4 := size_sem I chainL s3
  have o4 := sem_o I chainL s3 hasOut_chainL
  rw [semXIR_seq]
  generalize semXIR I chainL s3 = s4 at ch1 ch2 hM4 z4 o4
  -- 3. the column reads
  have hcO : capRecOff pX / 8 = 1727 := by rw [layout_P20.2.2.2.2.1]
  have hcap : ∀ e (he : e < (capRec π).length), ∀ m < 4,
      I.getD (capWX + 4 * e + m) 0 = (packBytes (capRec π)[e].toList).getD m 0 := fun e he m hm => by
    have he' : e < 128 := by simpa [capRec] using he
    simp only [capRec, List.getElem_map, List.getElem_range, hdD, packBytes_digW (length_wsAt _ _ _)]
    rw [List.getD_eq_getElem _ _ (by simpa using hm)]
    simp only [wsAt, List.getElem_map, List.getElem_range]
    rw [show capWX + 4 * e + m = 5 + (capRecOff pX / 8 + 4 * e + m) by simp only [capWX]; omega,
      tape_pw c π L hs (by rw [hcO]; omega)]
  have hX4 : ∀ a < L.length, rd s4.M (memX + a) = rd (semXIR I (idxIR4 memX pLX) s2).M (memX + a) :=
    fun a ha => by
      rw [hs3, ch2 _ (by simp only [regs, memX]; omega) (.inr (by simp only [chEnd, memX]; omega))]
  obtain ⟨r1, r2, r3, hM5⟩ := readIR_sem (bX := memX) (pL := pLX) (by simp only [regs, memX]; norm_num)
    (by simp only [memX]; norm_num) (by rw [layoutX.1]; norm_num) c π L (hs_posL hs) hq ht
    s2 hM2 (by rw [z2, z1]; simp only [memX]; omega) s4 hM4 (by rw [z4, z3, z2, z1]; simp only [memX]; omega) hX4 (capW := capWX) (wB := wBX)
    (cap := capRec π) (by simp [capRec]) (by simp only [capWX, hcO]; norm_num) hcap
    (by simp only [regs, wBX]; norm_num) (by simp only [wBX, memX]; norm_num)
  have z5 := size_sem I (readIR memX pLX capWX wBX) s4
  have o5 := readIR_o I s4 memX pLX capWX wBX
  rw [semXIR_seq]
  generalize semXIR I (readIR memX pLX capWX wBX) s4 = s5 at r1 r2 r3 hM5 z5 o5
  -- 4. the fold challenges
  have hsz5 : 2 ^ 25 ≤ s5.M.size := by rw [z5, z4, z3, z2, z1]; omega
  obtain ⟨a1, a2, hM6, z6, o6⟩ := acpIR_sem I s5 hM5 hsz5
  rw [semXIR_seq]
  generalize semXIR I acpIR s5 = s6 at a1 a2 hM6 z6 o6
  -- 5. `f₁`
  have hf1 : f1WX = 5 + f1Off pX / 8 := by rw [layoutX.2.2.1, layout_P20.2.2.2.1]
  obtain ⟨f1, f2, hM7, z7, o7⟩ := thcpIR_sem I s6 hM6 (a := f1WX) (dst := fBX) (n := 3 * 2 ^ 13)
    (by rw [layoutX.2.2.1]; norm_num) (by simp only [regs, fBX]; norm_num)
    (by simp only [fBX]; norm_num) (by rw [z6]; simp only [fBX]; omega)
  rw [semXIR_seq]
  generalize semXIR I (thcpIR f1WX fBX (3 * 2 ^ 13)) s6 = s7 at f1 f2 hM7 z7 o7
  have hsz7 : 2 ^ 25 ≤ s7.M.size := by rw [z7, z6]; exact hsz5
  -- the decoder's inputs
  have hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK s7.M (wBX + 64 * q + t) = readWd L (capRec π) q t :=
    fun q hq t ht' => by
      have hx : regs ≤ wBX + 64 * q + t := by simp only [regs, wBX]; omega
      simp only [rdK]
      rw [f2 _ hx (.inr (by simp only [fBX, wBX]; omega)), a2 _ hx (.inr (by simp only [aBX, wBX]; omega))]
      exact r1 q hq t ht'
  have hAl : ∀ i < 6, rdE s7.M (aBX + 3 * i) = alphaE (αd i) := fun i hi => by
    have hc : ∀ m < 3, rd s7.M (aBX + 3 * i + m) = dw (αd i) m := fun m hm => by
      have hp : alphaPos pX i < nChain pX := by rw [alphaPos_eq, nChain_eq]; omega
      rw [f2 _ (by simp only [regs, aBX]; omega) (.inl (by simp only [aBX, fBX]; omega)), a1 i hi m hm,
        r2 _ (by simp only [regs, ansB_eq]; omega) (.inr (by simp only [wBX, ansB_eq]; omega)),
        ch1 _ hp _ (hα i hi) m (by omega)]
      rfl
    have c0 := hc 0 (by norm_num)
    rw [Nat.add_zero] at c0
    rw [rdE_eq, alphaE, ← c0, ← hc 1 (by norm_num), ← hc 2 (by norm_num)]
  have hF : ∀ v < 2 ^ 13, rdE s7.M (fBX + 3 * v) = f1E π v := fun v hv => by
    have hc : ∀ m < 3, rd s7.M (fBX + 3 * v + m) = pw π (f1Off pX / 8 + 3 * v + m) := fun m hm => by
      rw [Nat.add_assoc, f1 _ (by omega), hf1, show 5 + f1Off pX / 8 + (3 * v + m) =
        5 + (f1Off pX / 8 + 3 * v + m) by omega, tape_pw c π L hs (by rw [layout_P20.2.2.2.1]; omega)]
    have c0 := hc 0 (by norm_num)
    rw [Nat.add_zero, Nat.add_zero] at c0
    rw [rdE_eq, f1E, ← c0, ← hc 1 (by norm_num), ← hc 2 (by norm_num)]
  -- 6. the decoder
  obtain ⟨d1, d2, d3, hM8⟩ := decIR_sem I s7 hM7
    (show DecLay dBX wBX aBX fBX s7.M.size from decLay_example _ hsz7) (readWd L (capRec π))
    (fun i => alphaE (αd i)) (f1E π) hW hAl hF
  have z8 := size_sem I (decIR dBX wBX aBX fBX) s7
  have o8 := decIR_o I s7 dBX wBX aBX fBX
  have hok : 2 ^ 13 ≤ (agreeL (readWd L (capRec π)) (fun i => alphaE (αd i)) (f1E π)).length := by
    by_contra hn
    rw [decodeRec, if_neg hn] at hdec
    cases hdec
  rw [decide_eq_true hok] at d1
  have hmsg := d2 out hdec
  generalize semXIR I (decIR dBX wBX aBX fBX) s7 = s8 at d1 hmsg d3 hM8 z8 o8
  -- 7. the flag and the node output
  have hsz8 : sgB + nCp ≤ s8.M.size := by
    rw [z8, z7, z6, z5, z4, z3, z2, z1]; simp only [sgB, nCp]; omega
  have hw : ∀ i < 2 ^ 19, rd s8.M (mB dBX + i) = wOut out i := fun i hi => by
    rw [← rdK_toBitVec, hmsg i hi]; rfl
  rw [okXIR_sem c π L hs s8 hM8 hsz8 d1 (wOut out) hw, o8, o7, o6, o5, o4, o3, bo, ho1,
    Array.toList_empty, List.nil_append]
  exact decodeWit_outWords π (wOut out)

/-! ## The `W` kind (FR `run_W_tape`, `run_W`, `E_W`) -/

theorem run_W_tape (inp : List Word) (a : ℕ) (ha : a < 2 ^ 64)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hk : a ≠ 0 → ¬ (inp.toArray.getD 5 0 &&& 0xFF = kindS)) :
    extX.run inp (fuel inp.length) =
      some ((List.range ((a + 7) / 8)).map fun j => inp.toArray.getD (5 + j) 0) := by
  have hd := decOk_decX
  have hwf := wf_extIRWith (pz := piSize pX) hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I (parseIR (piSize pX)) s0).M := inv_sem I hwf.1 h0
  have hz0 : a = 0 → rd (semXIR I (parseIR (piSize pX)) s0).M rIsSz = 0 := by
    intro h
    rw [parse_regs _ I s0 h0, h4, h, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [piSize_eq]; omega),
      piSize_eq] at this
    omega
  have hk' : a ≠ 0 → rd (semXIR I (parseIR (piSize pX)) s0).M rIsK = 0 := fun h => by
    rw [parse_isK _ I s0 h0, if_neg (hk h)]
  have hpo : (semXIR I (parseIR (piSize pX)) s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 ha]
  generalize hs1 : semXIR I (parseIR (piSize pX)) s0 = s1 at h1 hz0 hk' hpo
  have hB : BoundsOk I inp.length (extIRWith (piSize pX) decX) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk1 : rd s1.M rIsK = 0
    · rw [if_pos hk1]
      exact boundsOk_of_safe (safe_wIR ha h4 (by omega)) hwf.2.2 _ h1
    · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
      rw [if_neg hk1, boundsOk_ite, if_pos (hz0 ha0)]; trivial
  have hrun := run_toProg (P := extIRWith (piSize pX) decX) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  by_cases hk1 : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith (piSize pX) decX) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk1]
    rw [congrArg (fun s' : St => s'.o.toList) e, wIR_sem I _ h1 (by omega), hpo, hw]
    rfl
  · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
    have e : semXIR I (extIRWith (piSize pX) decX) s0 = semXIR I (.blk []) s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos (hz0 ha0)]
    rw [congrArg (fun s' : St => s'.o.toList) e, ha0]
    simp [semXIR, hpo]

/-- **`EX` on a `W` proof** (first byte not `'S'`), on every log: `WitnessSending.decode π`. -/
theorem EX_W (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hW : π.data[0]? ≠ some 0x53) : EX A c π L = WitnessSending.decode π := by
  by_cases hD : InDomE c π L
  · rw [EX, if_pos hD, EdX]
    have hπ : π.size < 2 ^ 64 := by have := hD.1; rw [outCap] at this; omega
    have hrun := run_W_tape (extractorInput c π L) π.size hπ (by rw [getD_toArray, tape_getD4])
      (tape_length c π L) (fun hne he => by
        obtain ⟨b, hb⟩ : ∃ b, π.data[0]? = some b := by
          rcases h : π.data[0]? with _ | b
          · rw [Array.getElem?_eq_none_iff] at h; exact (hne (Nat.le_zero.mp h)).elim
          · exact ⟨b, rfl⟩
        have h1 := tape_byte0 c π L hb
        have h2 := congrArg BitVec.toNat he
        rw [lowByte, getD_toArray, h1] at h2
        exact hW (by rw [hb]; congr 1; exact UInt8.toNat_inj.mp h2))
    rw [Eden, ← den_of_run (by simp only [regs, memX]; norm_num) (wf_extIRWith decOk_decX.wf) hrun,
      WitnessSending.decode]
    congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · rw [EX, if_neg hD, EoutX, if_neg hW]

/-- **The node witness with WP-11b-QL's `reassemble`** (`LvmReassemble`): the left child's proof is
`reassemble pX tr'` of its trace. -/
theorem Xwit_eq_replay (π : Proof) (w : ℕ → Word) : Xwit π w =
    .node (hdD π 6) (leafStmt (hdD π 15) (pw π 14).toNat)
      ⟨Lvm.Replay.reassemble pX (readTraceL (laneOf w)), readTraceL (laneOf w), sigOfF (sigCol w)⟩
      ⟨WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat), [], sigOfF fun j => pw π (19 + j)⟩ := by
  rw [Xwit, reassemble_readTraceL]

end Lvm.X
