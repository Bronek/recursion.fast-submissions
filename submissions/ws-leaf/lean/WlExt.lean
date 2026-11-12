-- New for ws-leaf: the extractor program and its `Computes` proof. The copy loop, the parse
-- registers and the tape lemmas are `WlXComputes.lean`'s (from the leanvm-inspired entry, #11).
import WlChain

/-!
# The extractor: copy the proof, recomputing the derived leaf statements

A proof is read as its packed words `ws` (`packBytes π`, `m = ⌈|π|/8⌉` words, tape words
`5 … 4 + m`). A **derived** proof (`WlVerifier.lean`) is an 11-word header, `tag ‖ sA ‖ nA ‖ sB ‖ nB`
(`tag` 2 or 3), then the words of a node witness whose derived child statements are zero:

* `tag = 2`: the right child's statement is derived from `(sB, nB)`, the left one is sent;
* `tag = 3`: both are derived, the left from `(sA, nA)`.

`fillW ws` is the witness words the extractor outputs: for a derived proof, `1`, the left child's
statement (derived, or the sent words `12 … 15`), the right child's derived statement, then words
`20 …` (the two signed children); for every other proof, `ws` itself (the library's
witness-sending copy). A derived statement is `digW` (`WlChain.lean`): `min(n, chainCap)` chain
steps from the start, then the leaf statement.

* `extW`: the program (`parseW`, then `decW` or the library copy `wIR`);
* **`extW_sem`**: on every domain tape the output is `fillW ws`;
* **`computes`**: `Computes ext Ex fuelW`, `Ex c π L = decodeWit (fillW ws)`.
-/

namespace WsLeaf.X

open RecursionFast

/-! ## The specification -/

/-- **The extractor's output words** for the packed words `ws` of a proof. -/
def fillW (ws : List Word) : List Word :=
  if (ws.getD 0 0 = 2 ∨ ws.getD 0 0 = 3) ∧ 20 ≤ ws.length then
    1 :: ((if ws.getD 0 0 = 3 then
        digW (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) (ws.getD 4 0) (ws.getD 5 0)
      else [ws.getD 12 0, ws.getD 13 0, ws.getD 14 0, ws.getD 15 0]) ++
      digW (ws.getD 6 0) (ws.getD 7 0) (ws.getD 8 0) (ws.getD 9 0) (ws.getD 10 0) ++ ws.drop 20)
  else ws

/-- **The extractor's specification**: the witness the output words denote. -/
def Ex (_ : Digest) (π : Proof) (_ : Log) : Option Wit := decodeWit (fillW (packBytes π.data.toList))

theorem fillW_length_le (ws : List Word) : (fillW ws).length ≤ ws.length := by
  unfold fillW
  split_ifs with h h3
  · simp only [List.length_cons, List.length_append, digW_length, List.length_drop]; omega
  · simp only [List.length_cons, List.length_append, digW_length, List.length_drop,
      List.length_cons, List.length_nil]; omega
  · exact le_rfl

/-! ## The program -/

/-- The tag word. -/ def rTg : ℕ := 80
/-- `1` iff the tag is `2`. -/ def rE2 : ℕ := 81
/-- `1` iff the tag is `3`. -/ def rE3 : ℕ := 82
/-- `1` iff the proof is derived. -/ def rCd : ℕ := 83
/-- The constant `1`. -/ def rOne : ℕ := 84
/-- The count of the rest. -/ def rN2 : ℕ := 86
/-- Scratch. -/ def rT2 : ℕ := 87
/-- Constant scratch. -/ def rK2 : ℕ := 88

/-- `rE3 := tag = 3`, `rCd := (tag = 2 ∨ tag = 3) ∧ ¬ ⌈|π|/8⌉ < 20`. -/
def condPs : List Prim :=
  [.const rK2 2, .op .eq rE2 rTg rK2, .const rK2 3, .op .eq rE3 rTg rK2, .op .or rCd rE2 rE3,
   .const rK2 20, .op .ltu rT2 rCnt rK2, .const rK2 1, .op .xor rT2 rT2 rK2, .op .and rCd rCd rT2]

/-- The parse: `|π|`, the word count, the tag (tape word 5), the flags. -/
def parseW : XIR := .seq wPre (.seq (readAt rTg 5) (.blk condPs))

/-- Output tape words `17 … 20` (proof words `12 … 15`: the sent left statement). -/
def copy4 : XIR :=
  .seq (readAt rW 17) (.seq (.out rW) (.seq (readAt rW 18) (.seq (.out rW)
    (.seq (readAt rW 19) (.seq (.out rW) (.seq (readAt rW 20) (.out rW)))))))

/-- The rest's count `(m − 20) · [m ≥ 20]` and its start (tape word 25). -/
def restPs : List Prim :=
  [.const rK2 20, .op .sub rN2 rCnt rK2, .op .ltu rT2 rCnt rK2, .const rK2 1, .op .xor rT2 rT2 rK2,
   .op .mul rN2 rN2 rT2, .const rPos 25]

/-- Copy proof words `20 … m − 1` (tape words `25 …`). -/
def restIR : XIR := .seq (.seq wPre (.blk restPs)) (.loopT rC rN2 ⟨0, 1, 1⟩ wBody)

/-- **The derived branch**: `1`, the left statement, the right statement, the rest. -/
def decW : XIR :=
  .seq (.blk [.const rOne 1]) (.seq (.out rOne) (.seq (.ite rE3 (digIR 6 10) copy4)
    (.seq (digIR 11 15) restIR)))

/-- **The extractor's program** (as `XIR`). -/
def extW : XIR := .seq parseW (.ite rCd decW wIR)

/-- The memory: the registers only. -/
def memW : ℕ := 256

/-- **The extractor's program.** -/
def ext : XProg := toProg memW 0 extW

/-- `claim.json`'s `fuel_base`: `2^36`. -/
def fuelBaseW : ℕ := 68719476736

/-- `claim.json`'s `fuel_per_word`. -/
def fuelPerWordW : ℕ := 16

/-- **The declared fuel.** -/
def fuelW (t : ℕ) : ℕ := fuelBaseW + fuelPerWordW * t

/-! ## Well formed, cost, size -/

theorem wf_copy4 : WF copy4 := by
  simp [copy4, readAt, WF, Prim.dst, rA, rW]

theorem wf_restIR : WF restIR := by
  simp [restIR, wPre, readAt, wCntPs, restPs, wBody, WF, Writes, Prim.dst, rA, rLen, rK, rCnt, rT,
    rW, rPos, rC, rN2, rT2, rK2, regs, cTmp, cOne]

theorem wf_parseW : WF parseW := by
  simp [parseW, wPre, readAt, wCntPs, condPs, WF, Prim.dst, rA, rLen, rK, rCnt, rT, rPos, rTg, rE2,
    rE3, rCd, rT2, rK2]

theorem wf_decW : WF decW := by
  refine ⟨by simp [WF, Prim.dst, rOne], trivial, ⟨wf_digIR _ _, wf_copy4⟩, wf_digIR _ _, wf_restIR⟩

theorem wf_extW : WF extW := ⟨wf_parseW, wf_decW, wf_wIR⟩

theorem cost_extW (t : ℕ) : cost extW t ≤ 2 ^ 35 + 2 ^ 10 + 8 * t := by
  have h1 := cost_digIR 6 10 t
  have h2 := cost_digIR 11 15 t
  simp only [extW, parseW, decW, copy4, restIR, wIR, wPre, readAt, wCntPs, condPs, restPs, wBody,
    cost, blkSteps, List.length_cons, List.length_nil, Aff.eval, Nat.div_one] at h1 h2 ⊢
  norm_num
  omega

theorem sizeIR_extW : sizeIR extW ≤ 2 ^ 18 := by
  have h1 := sizeIR_digIR 6 10
  have h2 := sizeIR_digIR 11 15
  simp only [extW, parseW, decW, copy4, restIR, wIR, wPre, readAt, wCntPs, condPs, restPs, wBody,
    sizeIR, blkSteps, List.length_cons, List.length_nil] at h1 h2 ⊢
  norm_num
  omega

theorem fuelW_covers (t : ℕ) : memW + 0 * t + cost extW t + 8 ≤ fuelW t := by
  have := cost_extW t
  simp only [memW, fuelW, fuelBaseW, fuelPerWordW] at *
  omega

theorem fuelW_le_budget (t : ℕ) : fuelW t ≤ extractorBudget t := by
  simp only [fuelW, fuelBaseW, fuelPerWordW, extractorBudget]; omega

theorem size_ext : ext.body.size ≤ progCap := by
  have := sizeIR_extW
  simp only [ext, toProg, size_compile, sizeIR, initPs, blkSteps, List.length_cons,
    List.length_nil, progCap] at *
  norm_num
  omega

/-! ## Registers -/

/-- What the parse leaves: the count, the tag flag `rE3`, the derived flag `rCd`. -/
theorem parseW_regs (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parseW s).M rE3 = (if I.getD 5 0 = 3 then 1 else 0) ∧
    rd (semXIR I parseW s).M rCd =
      (if (I.getD 5 0 = 2 ∨ I.getD 5 0 = 3) ∧ ¬ ceil8 (I.getD 4 0) < 20 then 1 else 0) := by
  have hs := hM.1
  simp only [regs] at hs
  have hc : rd (semXIR I wPre s).M rCnt = ceil8 (I.getD 4 0) := (wPre_regs I s hM).1
  have hs' : 256 ≤ (semXIR I wPre s).M.size := by rw [size_sem]; exact hs
  have e : semXIR I parseW s = semXIR I (.seq (readAt rTg 5) (.blk condPs)) (semXIR I wPre s) := rfl
  rw [e]
  generalize semXIR I wPre s = s1 at hc hs'
  simp only [rCnt] at hc
  simp only [readAt, condPs, semXIR, runPrims, List.foldl, Prim.run, rA, rTg, rE2, rE3, rCd, rT2,
    rK2, rCnt]
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
    rd_set_ne, XOp.eval, hc, BitVec.toNat_ofNat]
  refine ⟨trivial, ?_⟩
  simp only [Nat.reducePow, Nat.reduceMod]
  by_cases hl : ceil8 (I.getD 4 0) < 20 <;> by_cases h2 : I.getD 5 0 = 2 <;>
    by_cases h3 : I.getD 5 0 = 3 <;> simp only [hl, h2, h3, ite_true, ite_false] <;> decide

theorem o_parseW (I : Array Word) (s : St) : (semXIR I parseW s).o = s.o := by
  simp [parseW, wPre, readAt, semXIR]

/-- What the rest's prefix leaves: the count `⌈w/8⌉ − 20` (natural subtraction) and the start
position `25`. -/
theorem restPre_regs (I : Array Word) (s : St) (hM : Inv s.M) :
    (rd (semXIR I (.seq wPre (.blk restPs)) s).M rN2).toNat = (ceil8 (I.getD 4 0)).toNat - 20 ∧
      rd (semXIR I (.seq wPre (.blk restPs)) s).M rPos = toWord 25 := by
  have hs := hM.1
  simp only [regs] at hs
  have hc : rd (semXIR I wPre s).M rCnt = ceil8 (I.getD 4 0) := (wPre_regs I s hM).1
  have hs' : 256 ≤ (semXIR I wPre s).M.size := by rw [size_sem]; exact hs
  have e : semXIR I (.seq wPre (.blk restPs)) s = semXIR I (.blk restPs) (semXIR I wPre s) := rfl
  rw [e]
  generalize semXIR I wPre s = s1 at hc hs'
  simp only [rCnt] at hc
  simp only [restPs, semXIR, runPrims, List.foldl, Prim.run, rN2, rT2, rK2, rPos, rCnt]
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
    rd_set_ne, XOp.eval, hc]
  refine ⟨?_, rfl⟩
  generalize ceil8 (I.getD 4 0) = x
  by_cases hl : x < 20
  · have hx : x.toNat < 20 := hl
    simp only [hl, ite_true]
    rw [show ((1 : Word) ^^^ 1) = 0 from rfl]
    simp; omega
  · have hx : ¬ x.toNat < 20 := hl
    simp only [hl, ite_false]
    rw [show ((0 : Word) ^^^ 1) = 1 from rfl]
    have := x.isLt
    have h20 : (20 : Word).toNat = 20 := rfl
    have h1 : (1 : Word).toNat = 1 := rfl
    simp only [BitVec.toNat_mul, BitVec.toNat_sub, h20, h1]
    omega

/-- **The rest's copy**: the tape words `25 …`, `⌈w/8⌉ − 20` of them. -/
theorem restIR_sem (I : Array Word) (s : St) (hM : Inv s.M)
    (hw : (ceil8 (I.getD 4 0)).toNat + 25 < 2 ^ 64) :
    (semXIR I restIR s).o.toList = s.o.toList ++ (List.range ((ceil8 (I.getD 4 0)).toNat - 20)).map
      (fun j => I.getD (25 + j) 0) := by
  have hwf : WF (.seq wPre (.blk restPs)) := by
    simp [wPre, readAt, wCntPs, restPs, WF, Prim.dst, rA, rLen, rK, rCnt, rT, rPos, rN2, rT2, rK2]
  have hM' := inv_sem I hwf hM
  obtain ⟨hcnt, hpos⟩ := restPre_regs I s hM
  have ho : (semXIR I (.seq wPre (.blk restPs)) s).o = s.o := by simp [wPre, readAt, semXIR]
  have e : semXIR I restIR s =
      semXIR I (.loopT rC rN2 ⟨0, 1, 1⟩ wBody) (semXIR I (.seq wPre (.blk restPs)) s) := rfl
  rw [e]
  generalize semXIR I (.seq wPre (.blk restPs)) s = s1 at hM' hcnt hpos ho
  have hs := hM'.1
  simp only [regs] at hs
  have h0 : Inv (entryT rC rN2 s1.M) := inv_of_frame hM'
    (size_entryT ..) fun i hi => entryT_frame _ (by simp only [rC]; omega)
  have hc : rC < s1.M.size := by simp only [rC]; omega
  have hp : rd (entryT rC rN2 s1.M) rPos = toWord 25 := by
    rw [entryT_frame _ (by simp only [rC, rPos]; omega), hpos]
  have e2 : semXIR I (.loopT rC rN2 ⟨0, 1, 1⟩ wBody) s1 = iterL (semXIR I wBody) rC
      ((ceil8 (I.getD 4 0)).toNat - 20) ⟨entryT rC rN2 s1.M, s1.o⟩ := by
    simp only [semXIR, rd_entryT hc, hcnt]
  refine (congrArg (fun s' : St => s'.o.toList) e2).trans ?_
  rw [ho]
  generalize entryT rC rN2 s1.M = M0 at h0 hp
  exact wLoop I _ 25 ⟨M0, s.o⟩ h0 hp (by omega)

/-- **The sent left statement**: tape words `17 … 20`. -/
theorem copy4_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    (semXIR I copy4 s).o.toList =
      s.o.toList ++ [I.getD 17 0, I.getD 18 0, I.getD 19 0, I.getD 20 0] := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [copy4, readAt, semXIR, runPrims, List.foldl, Prim.run, rA, rW]
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
    BitVec.toNat_ofNat, Array.toList_push, List.append_assoc, List.cons_append,
    List.nil_append, Nat.reducePow, Nat.reduceMod]


/-! ## The output on a domain tape -/

section Tape

variable (c : Digest) (π : Proof) (L : Log)

theorem tapeA_getD {j : ℕ} (hj : j < (packBytes π.data.toList).length) :
    (extractorInput c π L).toArray.getD (5 + j) 0 = (packBytes π.data.toList).getD j 0 := by
  have hj' : j < (π.size + 7) / 8 := by
    rwa [packBytes_length, ← WitnessSending.size_eq_length] at hj
  rw [getD_toArray, tape_getD_proof c π L hj', List.getD_eq_getElem]

theorem ceil8_tape (hπ : π.size < 2 ^ 64) :
    (ceil8 ((extractorInput c π L).toArray.getD 4 0)).toNat = (packBytes π.data.toList).length := by
  rw [getD_toArray, tape_getD4, toNat_ceil8 hπ, packBytes_length, ← WitnessSending.size_eq_length]

theorem map_range_drop (I : Array Word) (ws : List Word) (a b : ℕ)
    (hget : ∀ j, j < ws.length → I.getD (a + j) 0 = ws.getD j 0) :
    (List.range (ws.length - b)).map (fun j => I.getD (a + b + j) 0) = ws.drop b := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
  simp only [List.length_map, List.length_range] at h1
  rw [Nat.add_assoc, hget (b + j) (by omega), List.getD_eq_getElem]

/-- **The program's output on a domain tape is `fillW` of the proof's words.** -/
theorem extW_sem (hπ : π.size ≤ 8 * outCap) (s : St) (hM : Inv s.M) (ho : s.o = #[]) :
    (semXIR (extractorInput c π L).toArray extW s).o.toList = fillW (packBytes π.data.toList) := by
  have hπ64 : π.size < 2 ^ 64 := by unfold outCap at hπ; omega
  generalize hI : (extractorInput c π L).toArray = I
  have hm : (ceil8 (I.getD 4 0)).toNat = (packBytes π.data.toList).length := by
    rw [← hI]; exact ceil8_tape c π L hπ64
  have hget : ∀ j, j < (packBytes π.data.toList).length →
      I.getD (5 + j) 0 = (packBytes π.data.toList).getD j 0 := fun j hj => by
    rw [← hI]; exact tapeA_getD c π L hj
  have hmb : (packBytes π.data.toList).length ≤ 2 ^ 24 := by
    rw [packBytes_length, ← WitnessSending.size_eq_length]; unfold outCap at hπ; omega
  generalize packBytes π.data.toList = ws at hm hget hmb
  have hml : (ceil8 (I.getD 4 0)).toNat + 25 < 2 ^ 64 := by rw [hm]; omega
  obtain ⟨h3, hcd⟩ := parseW_regs I s hM
  have hM1 := inv_sem I wf_parseW hM
  have ho1 : (semXIR I parseW s).o = #[] := by rw [o_parseW, ho]
  rw [extW, semXIR_seq]
  generalize semXIR I parseW s = s1 at h3 hcd hM1 ho1
  have hlt : ceil8 (I.getD 4 0) < 20 ↔ ws.length < 20 := by
    rw [BitVec.lt_def, hm]; rfl
  by_cases hc : (ws.getD 0 0 = 2 ∨ ws.getD 0 0 = 3) ∧ 20 ≤ ws.length
  · have h5 : I.getD 5 0 = ws.getD 0 0 := hget 0 (by omega)
    have hcd1 : rd s1.M rCd ≠ 0 := by
      rw [hcd, if_pos ⟨by rw [h5]; exact hc.1, by rw [hlt]; omega⟩]; decide
    rw [semXIR_ite, if_neg hcd1]
    have hs := hM1.1
    simp only [regs] at hs
    rw [decW, semXIR_seq, semXIR_seq, semXIR_seq]
    have hwf1 : WF (.blk [Prim.const rOne 1]) := by simp [WF, Prim.dst, rOne]
    have hM2 := inv_sem I hwf1 hM1
    have h2one : rd (semXIR I (.blk [.const rOne 1]) s1).M rOne = 1 := by
      simp only [semXIR, runPrims, List.foldl, Prim.run, rOne]
      rw [rd_set_self (by omega)]
    have h2e3 : rd (semXIR I (.blk [.const rOne 1]) s1).M rE3 = rd s1.M rE3 :=
      frame I _ s1 hwf1 hM1 rE3 (by decide) (by simp [Writes, Prim.dst, rOne, rE3])
    have ho2 : (semXIR I (.blk [.const rOne 1]) s1).o = #[] := ho1
    generalize semXIR I (.blk [.const rOne 1]) s1 = s2 at hM2 h2one h2e3 ho2
    have ho3 : (semXIR I (.out rOne) s2).o.toList = [1] := by
      simp [semXIR, ho2, h2one]
    have hM3 : Inv (semXIR I (.out rOne) s2).M := hM2
    have h3e3 : rd (semXIR I (.out rOne) s2).M rE3 = if ws.getD 0 0 = 3 then 1 else 0 := by
      show rd s2.M rE3 = _
      rw [h2e3, h3, h5]
    generalize semXIR I (.out rOne) s2 = s3 at ho3 hM3 h3e3
    have g : ∀ j, j < 20 → I.getD (5 + j) 0 = ws.getD j 0 := fun j hj => hget j (by omega)
    have ho4 : (semXIR I (.ite rE3 (digIR 6 10) copy4) s3).o.toList = [1] ++
        (if ws.getD 0 0 = 3 then
          digW (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) (ws.getD 4 0) (ws.getD 5 0)
        else [ws.getD 12 0, ws.getD 13 0, ws.getD 14 0, ws.getD 15 0]) := by
      by_cases h33 : ws.getD 0 0 = 3
      · have hne : rd s3.M rE3 ≠ 0 := by rw [h3e3, if_pos h33]; decide
        rw [semXIR_ite, if_neg hne]
        rw [digIR_sem I s3 hM3 (by omega) (by omega), ho3, if_pos h33, g 1 (by omega),
          g 2 (by omega), g 3 (by omega), g 4 (by omega), g 5 (by omega)]
      · have he : rd s3.M rE3 = 0 := by rw [h3e3, if_neg h33]
        rw [semXIR_ite, if_pos he]
        rw [copy4_sem I s3 hM3, ho3, if_neg h33, g 12 (by omega), g 13 (by omega), g 14 (by omega),
          g 15 (by omega)]
    have hM4 : Inv (semXIR I (.ite rE3 (digIR 6 10) copy4) s3).M :=
      inv_sem I (P := .ite rE3 (digIR 6 10) copy4) ⟨wf_digIR 6 10, wf_copy4⟩ hM3
    generalize semXIR I (.ite rE3 (digIR 6 10) copy4) s3 = s4 at ho4 hM4
    rw [semXIR_seq, restIR_sem I _ (inv_sem I (wf_digIR 11 15) hM4) hml,
      digIR_sem I s4 hM4 (by omega) (by omega), ho4, hm, g 6 (by omega), g 7 (by omega),
      g 8 (by omega), g 9 (by omega), g 10 (by omega), fillW, if_pos hc]
    have hr := map_range_drop I ws 5 20 hget
    simp only [Nat.reduceAdd] at hr
    rw [hr]
    simp
  · have hcd0 : rd s1.M rCd = 0 := by
      rw [hcd, if_neg]
      rintro ⟨h1, h2⟩
      refine hc ⟨?_, by rw [hlt] at h2; omega⟩
      have : 1 ≤ ws.length := by rw [hlt] at h2; omega
      rwa [← hget 0 this]
    rw [semXIR_ite, if_pos hcd0, wIR_sem I s1 hM1 (by omega), ho1, hm, fillW, if_neg hc]
    simpa using map_range_drop I ws 5 0 hget

end Tape


theorem noLoopT_parseW : NoLoopT parseW := by simp [parseW, wPre, readAt, NoLoopT]

theorem noLoopT_copy4 : NoLoopT copy4 := by simp [copy4, readAt, NoLoopT]

/-- The loop bounds hold on every tape of a proof below `2^64` bytes. -/
theorem safe_extW (c : Digest) (π : Proof) (L : Log) (hπ : π.size < 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length extW := by
  have h4 : (extractorInput c π L).toArray.getD 4 0 = toWord π.size := by
    rw [getD_toArray, tape_getD4]
  have hlen := tape_length c π L
  refine .seq (safe_of_noLoopT noLoopT_parseW) (.ite ?_ (safe_wIR hπ h4 (by omega)))
  refine .seq (.blk _) (.seq (.out _) (.seq (.ite (safe_of_noLoopT (noLoopT_digIR 6 10))
    (safe_of_noLoopT noLoopT_copy4)) (.seq (safe_of_noLoopT (noLoopT_digIR 11 15)) ?_)))
  refine .loopT (safe_of_noLoopT (by simp [wPre, readAt, NoLoopT])) (fun s hM => ?_)
    (safe_of_noLoopT (by simp [wBody, NoLoopT]))
  rw [(restPre_regs _ s hM).1, h4, toNat_ceil8 hπ]
  simp only [Aff.eval, Nat.div_one]; omega

/-- **The program computes the extractor `Ex` within `fuelW`.** -/
theorem computes : Computes ext Ex fuelW := by
  intro c π L h1 _ _
  have hπ64 : π.size < 2 ^ 64 := by unfold outCap at h1; omega
  have hreg : regs ≤ memW := le_rfl
  have h0 : Inv (initSt (memW + 0 * (extractorInput c π L).length)).M :=
    inv_initSt (by simp [memW, regs])
  have hB := boundsOk_of_safe (safe_extW c π L hπ64) wf_extW _ h0
  have hr := run_toProg (mem := memW) (mpw := 0) (input := extractorInput c π L)
    (f := fuelW (extractorInput c π L).length) hreg wf_extW hB (fuelW_covers _)
  have hs := extW_sem c π L h1 _ h0 (initSt_o _)
  refine ⟨_, hr, ?_, ?_⟩
  · rw [hs]
    refine (fillW_length_le _).trans ?_
    rw [packBytes_length, ← WitnessSending.size_eq_length]
    unfold outCap at h1 ⊢; omega
  · rw [hs]; rfl

end WsLeaf.X
