-- New for lvm (WP-13a), after FR's `FRXSpec` (`outIR`, `slotIR`, the node output) and `FRXLeaf`
-- (rf-k/submissions/flock-recursive/lean@kk/base): lvm's node witness and its output program.
import LvmXOutSeg
import LvmXChainL

/-!
# The node witness and the output program (BLUEPRINT §6.2 step 7)

**The witness** `Xwit π w` of an `S` proof with `b = 1` whose `C_rec` decodes to the message
words `w` (`2^19`; column `l` at words `l·2^14 + i`, stream lane `17i + l` = `crecIdx`, the
signature column 17):

`node c_L (leafStmt h n) ⟨reassembleL tr', tr', σ'⟩ ⟨encode (leaf s n), [], σ_leaf⟩`

with `c_L, s, n, h, σ_leaf` π's header fields (packed words 6–9, 10–13, 14, 15–18, 19–615), `tr'`
the trace read off the stream (`readTraceL`), `σ'` the signature column's 597 words.
**`witWords_Xwit`**: its output words are `outWords π w`.

**The program** `outIR mB` (after the decoder left `w` at `mB`): the tag, `c_L` (tape copy),
`leafStmt h n` (`LvmXKeccak`), `|π'|`, the stream copied to `sgB` (`copyIR`), the proof's and the
trace's segments over it (`LvmXOutSeg`), the signature column, the right child. **`outIR_sem`**.
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## The witness -/

/-- π's packed word `j`. -/
def pw (π : Proof) (j : ℕ) : Word := (packBytes π.data.toList).getD j 0

/-- A signature from its 597 words: the index, 133 chain values, 16 path digests. -/
def sigOfF (f : ℕ → Word) : Sig :=
  ⟨(f 0).toNat, (List.range wotsLen).map fun k => digW (wsAt f (1 + 4 * k) 4),
    (List.range sigHeight).map fun k => digW (wsAt f (1 + 4 * wotsLen + 4 * k) 4)⟩

theorem flatMap_digW (f : ℕ → Word) (a : ℕ) : ∀ m : ℕ,
    ((List.range m).map fun k => digW (wsAt f (a + 4 * k) 4)).flatMap (fun d => packBytes d.toList) =
      wsAt f a (4 * m)
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_digW f a m, List.map_singleton,
      List.flatMap_singleton, packBytes_digW (length_wsAt _ _ _), show 4 * (m + 1) = 4 * m + 4 by ring,
      wsAt_add]

theorem sigWords_sigOfF (f : ℕ → Word) : sigWords (sigOfF f) = wsAt f 0 597 := by
  have h1 := flatMap_digW f 1 wotsLen
  have h2 := flatMap_digW f (1 + 4 * wotsLen) sigHeight
  simp only [sigWords, sigOfF, h1, h2, toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show (597 : ℕ) = 1 + (4 * wotsLen + 4 * sigHeight) from rfl, wsAt_add, wsAt_add]
  simp [wsAt, wotsLen]

/-- The stream lane `u` of a decoded `C_rec` message: column `u mod 17`, row `⌊u/17⌋`. -/
def crecIdx (u : ℕ) : ℕ := u % 17 * 2 ^ 14 + u / 17

/-- The stream's lanes. -/
def laneOf (w : ℕ → Word) (u : ℕ) : Word := w (crecIdx u)

/-- The signature column (column 17). -/
def sigCol (w : ℕ → Word) (j : ℕ) : Word := w (17 * 2 ^ 14 + j)

/-- `π`'s header digest at packed word `j`. -/
def hdD (π : Proof) (j : ℕ) : Digest := digW (wsAt (pw π) j 4)

/-- **The node witness** of an `S` proof (`b = 1`) whose `C_rec` decodes to `w`. -/
def Xwit (π : Proof) (w : ℕ → Word) : Wit :=
  .node (hdD π 6) (leafStmt (hdD π 15) (pw π 14).toNat)
    ⟨reassembleL (readTraceL (laneOf w)), readTraceL (laneOf w), sigOfF (sigCol w)⟩
    ⟨WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat), [], sigOfF fun j => pw π (19 + j)⟩

/-- **The node output's words.** -/
def outWords (π : Proof) (w : ℕ → Word) : List Word :=
  toWord 1 :: wsAt (pw π) 6 4 ++ packBytes (leafStmt (hdD π 15) (pw π 14).toNat).toList ++
    (toWord (piSize pX) :: pWords (laneOf w)) ++ trWords (laneOf w) ++ wsAt (sigCol w) 0 597 ++
    (toWord 48 :: toWord 0 :: wsAt (pw π) 10 4 ++ [pw π 14]) ++ [toWord 0] ++
    wsAt (fun j => pw π (19 + j)) 0 597

theorem toWord_toNat' (x : Word) : toWord x.toNat = x := by simp [toWord]

theorem signed_left (w : ℕ → Word) :
    signedWords ⟨reassembleL (readTraceL (laneOf w)), readTraceL (laneOf w), sigOfF (sigCol w)⟩ =
      (toWord (piSize pX) :: pWords (laneOf w)) ++ trWords (laneOf w) ++ wsAt (sigCol w) 0 597 := by
  have hl : (reassembleL (readTraceL (laneOf w))).data.toList.length = piSize pX := by
    rw [Array.length_toList]; exact size_reassembleL _
  rw [signedWords, bytesWords, hl, packBytes_reassembleL, logWords_readTraceL, sigWords_sigOfF]

theorem signed_right (π : Proof) :
    signedWords ⟨WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat), [], sigOfF fun j => pw π (19 + j)⟩ =
      (toWord 48 :: toWord 0 :: wsAt (pw π) 10 4 ++ [pw π 14]) ++ [toWord 0] ++
        wsAt (fun j => pw π (19 + j)) 0 597 := by
  have hl : (WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat)).data.toList.length = 48 := by
    rw [Array.length_toList]; exact WitnessSending.size_encode_leaf _ _
  rw [signedWords, bytesWords, hl, WitnessSending.encode_data, packBytes_wordsBytes, sigWords_sigOfF]
  simp only [witWords, hdD, packBytes_digW (length_wsAt _ _ _), toWord_toNat', logWords,
    List.length_nil, List.flatMap_nil, List.cons_append, List.append_assoc]

theorem witWords_Xwit (π : Proof) (w : ℕ → Word) : witWords (Xwit π w) = outWords π w := by
  rw [Xwit, witWords, signed_left, signed_right, hdD, packBytes_digW (length_wsAt _ _ _), outWords]
  simp only [List.cons_append, List.append_assoc]

theorem fits_Xwit (π : Proof) (w : ℕ → Word) : (Xwit π w).Fits := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [size_reassembleL, piSize_eq]; norm_num
  · rw [length_readTraceL, qS_P20.1]; norm_num
  · intro e he
    simp only [readTraceL, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨x, hx, rfl⟩
    · simp [q0Ent, wordBytes_length]
    · obtain ⟨-, h2⟩ := walk_lt 6 lensL x (hx)
      have h3 := lanes_T
      have h4 : streamLanes pX = 222625 := sizes_P20.2.2.2.2.2.2.1
      simp only [entAt, bArr_size, wordsBytes_length, length_wsAt]
      omega
  · exact (sigCol w 0).isLt
  · simp [sigOfF]
  · simp [sigOfF]
  · rw [WitnessSending.size_encode_leaf]; norm_num
  · simp
  · simp
  · exact (pw π 19).isLt
  · simp [sigOfF]
  · simp [sigOfF]

/-- **The node output denotes the node witness.** -/
theorem decodeWit_outWords (π : Proof) (w : ℕ → Word) : decodeWit (outWords π w) = some (Xwit π w) := by
  rw [← witWords_Xwit, decodeWit_witWords _ (fits_Xwit π w)]

end Lvm.X
