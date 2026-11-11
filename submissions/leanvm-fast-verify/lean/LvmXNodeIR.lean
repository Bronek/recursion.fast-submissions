-- New for lvm (WP-13a), after FR's `FRXSpec` (`outIR`, `seg_step`, `setR`; rf-k/submissions/
-- flock-recursive/lean@kk/base): the node witness's output program and its semantics.
import LvmXEmit
import LvmXKeccak

/-!
# The node output program (BLUEPRINT §6.2 step 7)

`outIR mB` emits `outWords π w` (`LvmXNode`) when the decoded message `w` sits at `mB`:
the tag, `c_L`, `leafStmt h n` (Keccak), `|π'|`, then the stream is copied to `sgB` and the proof's
and trace's segments are emitted over it, the signature column, the right child. **`outIR_sem`**.
-/

namespace Lvm.X

open RecursionFast Lvm

/-- Point the segment compiler at the source `R` (base offset 0, kind flag off). -/
def setR (R : ℕ) : XIR := .blk [.const oR (toWord R), .const oKF 0, .const (oBd 0) 0]

/-- The signature column's base. -/
def sigB (mB : ℕ) : ℕ := mB + 17 * 2 ^ 14

/-- **The node output.** -/
def outIR (mB : ℕ) : XIR :=
  .seq (emitIR (toWord 1)) (.seq (tcpIR 11 4) (.seq (leafStmtIR 20 19)
  (.seq (emitIR (toWord (piSize pX))) (.seq (copyIR mB)
  (.seq (setR sgB) (.seq (segIR apC 0 pSegL) (.seq (segIR apC 0 trSegL)
  (.seq (setR (sigB mB)) (.seq (segIR apC 0 (.cp 0 597))
  (.seq (emitIR (toWord 48)) (.seq (emitIR (toWord 0)) (.seq (tcpIR 15 5)
  (.seq (emitIR (toWord 0)) (tcpIR 24 597))))))))))))))

/-! ## Steps -/

theorem setR_sem (I : Array Word) (t : St) (hM : Inv t.M) (R : ℕ) :
    Inv (semXIR I (setR R) t).M ∧ (semXIR I (setR R) t).M.size = t.M.size ∧
    (∀ y, regs ≤ y → rd (semXIR I (setR R) t).M y = rd t.M y) ∧
    rd (semXIR I (setR R) t).M oR = toWord R ∧ rd (semXIR I (setR R) t).M oKF = 0 ∧
    rd (semXIR I (setR R) t).M (oBd 0) = toWord 0 ∧ (semXIR I (setR R) t).o = t.o := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨inv_sem I (by simp +decide [setR, WF, Prim.dst, oR, oKF, oBd]) hM, size_sem .., fun y hy => ?_,
    ?_, ?_, ?_, rfl⟩
  · exact rd_blk_of_not_dst I _ t (by simp only [regs] at hy; simp [Prim.dst, oR, oKF, oBd]; omega)
  · rw [setR, semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_ne (by decide), rd_set_self (by simp only [oR]; omega)]
  · rw [setR, semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [size_set, oKF]; omega)]
  · rw [setR, semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, oBd]; omega)]; rfl

/-- A segment from a state in context with base 0: its words, the context and the base kept. -/
theorem seg_step (I : Array Word) {M₀ : Mem} {R : ℕ} (hA : ∀ x, regs ≤ (addrW apC (toWord R) x).toNat)
    (seg : Seg) (hok : okSeg seg = true) (hd : depthSeg seg ≤ 2) (t : St) (hc : Ctx M₀ R false t)
    (hb : rd t.M (oBd 0) = toWord 0) :
    (semXIR I (segIR apC 0 seg) t).o.toList = t.o.toList ++ segOut (src M₀ apC R) false 0 seg ∧
    Ctx M₀ R false (semXIR I (segIR apC 0 seg) t) ∧ rd (semXIR I (segIR apC 0 seg) t).M (oBd 0) = toWord 0 :=
  ⟨segIR_sem I apC hA seg 0 0 t hok (by omega) hc hb, ctx_segIR I apC seg 0 (by omega) hc,
    (frame I _ t (wf_segIR apC seg 0 (by omega)) hc.inv _ (by simp [oBd, regs])
      (noW_segIR apC seg 0 _ (.inr (.inr (.inr rfl))))).trans hb⟩

/-- π's packed words on the tape. -/
theorem tape_pw (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) {j : ℕ}
    (hj : j < 136514) : (extractorInput c π L).toArray.getD (5 + j) 0 = pw π j := by
  have hp : π.size = 1180192 := hs.trans piSize_eq
  rw [getD_toArray, tape_getD_proof c π L (by rw [hp]; omega), pw, List.getD_eq_getElem]

theorem wsAt_tape (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) {a n : ℕ}
    (h : a + n ≤ 136514) :
    (List.range n).map (fun j => (extractorInput c π L).toArray.getD (5 + a + j) 0) = wsAt (pw π) a n :=
  List.map_congr_left fun j hj => by
    rw [Nat.add_assoc, tape_pw c π L hs (by simp at hj; omega)]

/-- **The node output**: from a state whose heap holds the decoded message `w` at `mB`, on the tape
of an `S` proof, `outIR mB` appends `outWords π w`. -/
theorem outIR_sem (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) (s : St)
    (hM : Inv s.M) {mB : ℕ} (hmB : regs ≤ mB) (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size)
    (w : ℕ → Word) (hw : ∀ i < 2 ^ 19, rd s.M (mB + i) = w i) :
    (semXIR (extractorInput c π L).toArray (outIR mB) s).o.toList = s.o.toList ++ outWords π w := by
  set I := (extractorInput c π L).toArray with hI
  have hs0 := hM.1
  simp only [regs] at hs0 hmB
  -- 1. the tag
  have hwf1 := wf_emitIR (toWord 1)
  obtain ⟨o1, f1⟩ := emitIR_sem I s hM (toWord 1)
  have hM1 := inv_sem I hwf1 hM
  have z1 := size_sem I (emitIR (toWord 1)) s
  rw [outIR, semXIR_seq]
  generalize semXIR I (emitIR (toWord 1)) s = s1 at o1 f1 hM1 z1
  -- 2. `c_L`
  obtain ⟨o2, f2, hM2, z2⟩ := tcpIR_sem I s1 hM1 (a := 11) (n := 4) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (tcpIR 11 4) s1 = s2 at o2 f2 hM2 z2
  -- 3. `leafStmt h n`
  obtain ⟨o3, f3⟩ := leafStmtIR_sem I s2 hM2 (hW := 20) (nW := 19) (hdD π 15) (pw π 14).toNat
    (fun i hi => by
      rw [hdD, packBytes_digW (length_wsAt _ _ _), wsAt, List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map, List.getElem_range, show 20 + i = 5 + (15 + i) by omega,
        tape_pw c π L hs (by omega)])
    (by rw [show 19 = 5 + 14 from rfl, tape_pw c π L hs (by omega), toWord_toNat'])
    (pw π 14).isLt (by norm_num) (by norm_num)
  have hM3 := inv_sem I (wf_leafStmtIR 20 19) hM2
  have z3 := size_sem I (leafStmtIR 20 19) s2
  rw [semXIR_seq]
  generalize semXIR I (leafStmtIR 20 19) s2 = s3 at o3 f3 hM3 z3
  -- 4. `|π'|`
  obtain ⟨o4, f4⟩ := emitIR_sem I s3 hM3 (toWord (piSize pX))
  have hM4 := inv_sem I (wf_emitIR (toWord (piSize pX))) hM3
  have z4 := size_sem I (emitIR (toWord (piSize pX))) s3
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord (piSize pX))) s3 = s4 at o4 f4 hM4 z4
  -- the heap so far
  have h4 : ∀ y, regs ≤ y → rd s4.M y = rd s.M y := fun y hy => by
    simp only [regs] at hy
    rw [f4 y (by simp only [eW]; omega), f3 y (by simp only [regs]; omega),
      f2 y (by simp only [eW]; omega) (by simp only [eP]; omega) (by simp only [eN]; omega)
        (by simp only [eC]; omega) (by simp only [cTmp]; omega), f1 y (by simp only [eW]; omega)]
  have zz4 : s4.M.size = s.M.size := by rw [z4, z3, z2, z1]
  -- 5. the stream copy
  obtain ⟨c1, c2, hM5, z5, o5⟩ := copyIR_sem I s4 hM4 (mB := mB) (by simp only [regs]; omega) hmB2
    (by rw [zz4]; exact hsz)
  rw [semXIR_seq]
  generalize semXIR I (copyIR mB) s4 = s5 at c1 c2 hM5 z5 o5
  -- the stream's lanes and the signature column in the heap
  have hlane : ∀ u < nCp, rd s5.M (sgB + u) = laneOf w u := fun u hu => by
    rw [c1 u hu, h4 _ (by simp only [regs]; omega), hw _ (crecIdx_lt hu)]; rfl
  have hsig : ∀ j < 597, rd s5.M (sigB mB + j) = sigCol w j := fun j hj => by
    rw [c2 _ (by simp only [regs, sigB]; omega) (.inl (by simp only [sigB]; omega)), sigB,
      Nat.add_assoc, h4 _ (by simp only [regs]; omega), hw _ (by omega)]; rfl
  -- 6–8. the proof's and the trace's segments
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := setR_sem I s5 hM5 sgB
  rw [semXIR_seq]
  generalize semXIR I (setR sgB) s5 = s6 at r1 r2 r3 r4 r5 r6 r7
  have hc6 : Ctx s5.M sgB false s6 := ⟨r1, r2, r3, r4, by rw [r5]; simp⟩
  have hA := hA_apC (R := sgB) (by simp only [regs, sgB]; norm_num) (by simp only [sgB]; norm_num)
  obtain ⟨g1, g2, g3⟩ := seg_step I hA pSegL segs_ok.2.2.1 segs_ok.2.2.2 s6 hc6 r6
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 pSegL) s6 = s7 at g1 g2 g3
  obtain ⟨k1, k2, k3⟩ := seg_step I hA trSegL segs_ok.1 segs_ok.2.1 s7 g2 g3
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 trSegL) s7 = s8 at k1 k2 k3
  -- the source is the stream below `T`
  have hT : streamLanes pX = 250044 := sizes_P20.2.2.2.2.2.2.1
  have hsrc : ∀ v < streamLanes pX, src s5.M apC sgB v = laneOf w v := fun v hv => by
    rw [src_apC _ (by simp only [sgB]; omega), hlane v (by simp only [nCp]; omega)]
  have eP : segOut (src s5.M apC sgB) false 0 pSegL = pWords (laneOf w) := by
    rw [segOut_pSegL, ← packBytes_reassembleL, readTraceL_congr hsrc, packBytes_reassembleL]
  have eT : segOut (src s5.M apC sgB) false 0 trSegL = trWords (laneOf w) := by
    rw [segOut_trSegL, ← logWords_readTraceL, readTraceL_congr hsrc, logWords_readTraceL]
  -- 9–10. the signature column
  have hM8 := k2.inv
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := setR_sem I s8 hM8 (sigB mB)
  rw [semXIR_seq]
  generalize semXIR I (setR (sigB mB)) s8 = s9 at u1 u2 u3 u4 u5 u6 u7
  have hc9 : Ctx s5.M (sigB mB) false s9 :=
    ⟨u1, by rw [u2, k2.size], fun y hy => by rw [u3 y hy, k2.heap y hy], u4, by rw [u5]; simp⟩
  have hA' := hA_apC (R := sigB mB) (by simp only [regs, sigB]; omega) (by simp only [sigB, sgB] at hmB2 ⊢; omega)
  obtain ⟨v1, v2, v3⟩ := seg_step I hA' (.cp 0 597) (by decide) (by decide) s9 hc9 u6
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 (.cp 0 597)) s9 = s10 at v1 v2 v3
  have eS : segOut (src s5.M apC (sigB mB)) false 0 (.cp 0 597) = wsAt (sigCol w) 0 597 := by
    simp only [segOut, wsAt, Nat.zero_add]
    exact List.map_congr_left fun j hj => by
      rw [src_apC _ (by simp only [sigB, sgB] at hmB2 ⊢; simp at hj; omega), hsig j (by simpa using hj)]
  -- 11–15. the right child
  have hM10 := v2.inv
  obtain ⟨p1, -⟩ := emitIR_sem I s10 hM10 (toWord 48)
  have hM11 := inv_sem I (wf_emitIR (toWord 48)) hM10
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 48)) s10 = s11 at p1 hM11
  obtain ⟨p2, -⟩ := emitIR_sem I s11 hM11 (toWord 0)
  have hM12 := inv_sem I (wf_emitIR (toWord 0)) hM11
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 0)) s11 = s12 at p2 hM12
  obtain ⟨p3, -, hM13, -⟩ := tcpIR_sem I s12 hM12 (a := 15) (n := 5) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (tcpIR 15 5) s12 = s13 at p3 hM13
  obtain ⟨p4, -⟩ := emitIR_sem I s13 hM13 (toWord 0)
  have hM14 := inv_sem I (wf_emitIR (toWord 0)) hM13
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 0)) s13 = s14 at p4 hM14
  obtain ⟨p5, -, -, -⟩ := tcpIR_sem I s14 hM14 (a := 24) (n := 597) (by norm_num)
  -- the words
  rw [p5, p4, p3, p2, p1, v1, u7, k1, g1, r7, o5, o4, o3, o2, o1, eP, eT, eS]
  have t1 := wsAt_tape c π L hs (a := 6) (n := 4) (by norm_num)
  have t2 := wsAt_tape c π L hs (a := 10) (n := 5) (by norm_num)
  have t3 := wsAt_tape c π L hs (a := 19) (n := 597) (by norm_num)
  simp only [show (5 + 6 : ℕ) = 11 from rfl, show (5 + 10 : ℕ) = 15 from rfl,
    show (5 + 19 : ℕ) = 24 from rfl] at t1 t2 t3
  rw [t1, t2, t3, outWords, show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
  have e19 : wsAt (pw π) 19 597 = wsAt (fun j => pw π (19 + j)) 0 597 := by
    simp only [wsAt, Nat.zero_add]
  rw [e19]
  simp [wsAt, List.append_assoc]

end Lvm.X
