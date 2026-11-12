-- From relay-echo (#12), `lean/FastSpecParse.lean` (Apache-2.0), unchanged except the module names of
-- its imports.
/-
  The statements that tie the byte-array format code of `FastDefs.lean` to the library's proof
  format (`WitnessSending.encode`, `witWords` and `decodeWit`, `Library/Words.lean`).

  * **L5a** `encodeB_eq`: `encodeB` is `WitnessSending.encode`. It rests on one writer fact per
    field, each the bytes of the field's words (`pushString_data`, `pushTrace_data`,
    `pushSig_data`, `pushSigned_data`, so `encodeB_data`), and on the bytes of packed words
    (`wordsBytes_packBytes`: the bytes, then zeros up to a multiple of 8).
  * **L5b** `parseB_encode`: `parseB` reads the encoding of every fitting witness back. It rests
    on one reader fact per field, each reading the field's bytes at their index in any byte array
    (`rdNat_enc64`, `rdDigest_toList`, `rdDigests_flatMap`, `rdString_bytesWords`,
    `rdEntries_flatMap`, `rdSig_sigWords`, `rdSigned_signedWords`), in the order of the
    library's readers (`readNat_toWord`, …, `readSigned_signedWords`, `Library/Words.lean`).
  * L5 (`check'_eq`, `FastSpec.lean`) follows by strong induction on the proof's size. If
    `check'` accepts, its conjuncts make the witness fit, so `encodeB_eq` and
    `WitnessSending.decode_encode` give the library's decoding. If `check` accepts,
    `WitnessSending.check_iff` gives a fitting witness whose encoding is the proof, and
    `parseB_encode` reads it back.
-/
import WlFastDefs
import WlFastParseBytes

namespace RecursionFast.FastCheck
open RecursionFast

/-! ## L5a: the writers -/

/-- `pushZeros` appends `k` zero bytes. -/
theorem pushZeros_data (b : ByteArray) (k : ℕ) :
    (pushZeros b k).data.toList = b.data.toList ++ List.replicate k 0 := by
  induction k generalizing b with
  | zero => simp [pushZeros]
  | succ k ih => simp [pushZeros, ih, List.replicate_succ, List.append_assoc]

/-- The bytes of packed words are the bytes, then zeros up to a multiple of 8. -/
theorem wordsBytes_packBytes (l : List UInt8) :
    wordsBytes (packBytes l) = l ++ List.replicate ((8 - l.length % 8) % 8) 0 := by
  exact ParseProof.packed_bytes l

/-- The bytes of a number's word are the 8 little-endian bytes of the number. -/
theorem wordBytes_toWord (n : ℕ) : wordBytes (toWord n) = enc64 n := by
  exact ParseProof.word_to_bytes n

/-- `pushString` appends the bytes of `bytesWords`. -/
theorem pushString_data (b x : ByteArray) :
    (pushString b x).data.toList = b.data.toList ++ wordsBytes (bytesWords x.data.toList) := by
  simp [pushString, pushZeros_data, pushU64_data, bytesWords, wordsBytes_cons',
    wordBytes_toWord, wordsBytes_packBytes, List.append_assoc]

/-- `pushTrace` appends the bytes of `logWords`. -/
theorem pushTrace_data (b : ByteArray) (tr : Trace) :
    (pushTrace b tr).data.toList = b.data.toList ++ wordsBytes (logWords tr) := by
  have fold (es : Trace) (a : ByteArray) :
      (es.foldl (fun b e => pushDigest (pushString b e.1) e.2) a).data.toList =
        a.data.toList ++ wordsBytes (es.flatMap fun e =>
          bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    induction es generalizing a with
    | nil => simp [wordsBytes_nil']
    | cons e es ih =>
      simp [ih, pushDigest_data, pushString_data, wordsBytes_append',
        ParseProof.wordsBytes_digest, List.append_assoc]
  simp [pushTrace, fold, pushU64_data, logWords, wordsBytes_cons', wordBytes_toWord,
    List.append_assoc]

/-- `pushSig` appends the bytes of `sigWords`. -/
theorem pushSig_data (b : ByteArray) (σ : Sig) :
    (pushSig b σ).data.toList = b.data.toList ++ wordsBytes (sigWords σ) := by
  simp [pushSig, foldl_pushDigest_data, pushU64_data, sigWords, wordsBytes_cons',
    wordsBytes_append', wordBytes_toWord, ParseProof.wordsBytes_digests, List.append_assoc]

/-- `pushSigned` appends the bytes of `signedWords`. -/
theorem pushSigned_data (b : ByteArray) (p : Signed) :
    (pushSigned b p).data.toList = b.data.toList ++ wordsBytes (signedWords p) := by
  simp [pushSigned, pushSig_data, pushTrace_data, pushString_data, signedWords,
    wordsBytes_append', List.append_assoc]

/-- The bytes of `encodeB w` are the bytes of `witWords w`. -/
theorem encodeB_data (w : Wit) : (encodeB w).data.toList = wordsBytes (witWords w) := by
  cases w with
  | leaf s n =>
    simp [encodeB, witWords, pushU64_data, pushDigest_data, wordsBytes_append', wordsBytes_cons',
      wordsBytes_nil', ParseProof.wordsBytes_digest, wordBytes_toWord]
  | node c₁ c₂ p₁ p₂ =>
    simp [encodeB, witWords, pushSigned_data, pushU64_data, pushDigest_data, wordsBytes_append',
      wordsBytes_cons', ParseProof.wordsBytes_digest, wordBytes_toWord]

/-- **L5a.** The byte-array encoder is the library's, on every witness. -/
theorem encodeB_eq : encodeB = WitnessSending.encode := by
  funext w
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [encodeB_data, WitnessSending.encode_data]

/-! ## L5b: the readers

Each reader reads a field's bytes at their index, whatever precedes and follows them. -/

/-- The word at byte `i` is the little-endian number of the 8 bytes there. -/
theorem u64At_toNat (b : ByteArray) (i : ℕ) (h : i + 8 ≤ b.size) :
    (u64At b i h).toNat = ofLE ((b.data.toList.drop i).take 8) := by
  have hs : (b.data.toList.drop i).take 8 =
      [b[i], b[i + 1], b[i + 2], b[i + 3], b[i + 4], b[i + 5], b[i + 6], b[i + 7]] := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, Array.length_toList,
        ByteArray.size_data, List.length_cons, List.length_nil]
      omega
    · intro j hj hk
      have hj8 : j < 8 := by simpa using hk
      simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList]
      interval_cases j <;> rfl
  rw [hs]
  exact ParseProof.pack8_toNat _ _ _ _ _ _ _ _

/-- `rdNat` reads a number's 8 bytes back. -/
theorem rdNat_enc64 {b : ByteArray} {pre post : List UInt8} {n : ℕ} (hn : n < 2 ^ 64)
    (hb : b.data.toList = pre ++ enc64 n ++ post) :
    rdNat b pre.length = some (n, (pre ++ enc64 n).length) := by
  have hl := congrArg List.length hb
  simp only [List.length_append, enc64_length, Array.length_toList, ByteArray.size_data] at hl
  have hs := ParseProof.slice_mid hb
  rw [enc64_length] at hs
  rw [rdNat, dite_eq_left (by omega), u64At_toNat, hs, ofLE_enc64, Nat.mod_eq_of_lt hn]
  simp [enc64_length]

/-- `rdDigest` reads a digest's 32 bytes back. -/
theorem rdDigest_toList {b : ByteArray} {pre post : List UInt8} (d : Digest)
    (hb : b.data.toList = pre ++ d.toList ++ post) :
    rdDigest b pre.length = some (d, (pre ++ d.toList).length) := by
  have hl := congrArg List.length hb
  simp only [List.length_append, Vector.length_toList, Array.length_toList,
    ByteArray.size_data] at hl
  rw [rdDigest, dite_eq_left (by omega), ParseProof.digestAt_mid d hb]
  simp

/-- `rdDigests` reads a list of digests back. -/
theorem rdDigests_flatMap {b : ByteArray} {pre post : List UInt8} (ds : List Digest)
    (hb : b.data.toList = pre ++ ds.flatMap Vector.toList ++ post) :
    rdDigests b pre.length ds.length = some (ds, (pre ++ ds.flatMap Vector.toList).length) := by
  have hl := congrArg List.length hb
  simp only [List.length_append, ParseProof.digests_length, Array.length_toList,
    ByteArray.size_data] at hl
  rw [rdDigests, dite_eq_left (by omega), ParseProof.digestsAt_mid ds hb]
  simp [Nat.mul_comm]

/-- `rdString` reads the bytes of `bytesWords` back, its padding skipped. -/
theorem rdString_bytesWords {b : ByteArray} {pre post : List UInt8} (x : ByteArray)
    (hx : x.size < 2 ^ 64)
    (hb : b.data.toList = pre ++ wordsBytes (bytesWords x.data.toList) ++ post) :
    rdString b pre.length = some (x, (pre ++ wordsBytes (bytesWords x.data.toList)).length) := by
  have hw : wordsBytes (bytesWords x.data.toList) =
      enc64 x.size ++ x.data.toList ++ List.replicate ((8 - x.size % 8) % 8) 0 := by
    simp [bytesWords, wordsBytes_cons', wordBytes_toWord, wordsBytes_packBytes,
      List.append_assoc]
  have hb0 : b.data.toList = pre ++ enc64 x.size ++
      (x.data.toList ++ List.replicate ((8 - x.size % 8) % 8) 0 ++ post) := by
    simpa [hw, List.append_assoc] using hb
  have hb1 : b.data.toList = (pre ++ enc64 x.size) ++ x.data.toList ++
      (List.replicate ((8 - x.size % 8) % 8) 0 ++ post) := by
    simpa [List.append_assoc] using hb0
  have r0 := rdNat_enc64 hx hb0
  have hs := ParseProof.extract_mid hb1
  have hl := congrArg List.length hb0
  simp only [List.length_append, enc64_length, Array.length_toList, ByteArray.size_data,
    List.length_replicate] at hl
  have he : (pre ++ enc64 x.size).length + 8 * ((x.size + 7) / 8) ≤ b.size := by
    simp only [List.length_append, enc64_length]
    omega
  simp only [rdString, r0, Option.bind_eq_bind, Option.bind_some, ite_eq_left he, hs]
  congr 2
  simp only [hw, List.length_append, enc64_length, Array.length_toList,
    ByteArray.size_data, List.length_replicate]
  omega

/-- `rdEntries` reads the entries of `logWords` back, after the entries `acc`. -/
theorem rdEntries_flatMap {b : ByteArray} {pre post : List UInt8} (tr : Trace)
    (hq : ∀ e ∈ tr, e.1.size < 2 ^ 64) (acc : Trace)
    (hb : b.data.toList = pre ++ wordsBytes (tr.flatMap fun e =>
      bytesWords e.1.data.toList ++ packBytes e.2.toList) ++ post) :
    rdEntries b tr.length pre.length acc = some (acc.reverse ++ tr, (pre ++ wordsBytes
      (tr.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList)).length) := by
  induction tr generalizing pre acc with
  | nil => simp [rdEntries, wordsBytes_nil']
  | cons e tr ih =>
    let rest := wordsBytes (tr.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList)
    have hb0 : b.data.toList = pre ++ wordsBytes (bytesWords e.1.data.toList) ++
        (e.2.toList ++ rest ++ post) := by
      simpa [rest, wordsBytes_append', ParseProof.wordsBytes_digest, List.append_assoc] using hb
    have hb1 : b.data.toList = (pre ++ wordsBytes (bytesWords e.1.data.toList)) ++
        e.2.toList ++ (rest ++ post) := by simpa [List.append_assoc] using hb0
    have hb2 : b.data.toList = (pre ++ wordsBytes (bytesWords e.1.data.toList) ++ e.2.toList) ++
        rest ++ post := by simpa [List.append_assoc] using hb0
    have r0 := rdString_bytesWords e.1 (hq e (by simp)) hb0
    have r1 := rdDigest_toList e.2 hb1
    have r2 := ih (pre := pre ++ wordsBytes (bytesWords e.1.data.toList) ++ e.2.toList)
      (fun q hq' => hq q (by simp [hq'])) (e :: acc) hb2
    simp only [List.length_cons, rdEntries, rdEntry, r0, Option.bind_eq_bind,
      Option.bind_some, r1, pure, r2]
    simp [wordsBytes_append', ParseProof.wordsBytes_digest, List.append_assoc]

/-- `rdSig` reads the bytes of `sigWords` back. -/
theorem rdSig_sigWords {b : ByteArray} {pre post : List UInt8} (σ : Sig) (hi : σ.idx < 2 ^ 64)
    (ho : σ.ots.length = wotsLen) (hp : σ.path.length = sigHeight)
    (hb : b.data.toList = pre ++ wordsBytes (sigWords σ) ++ post) :
    rdSig b pre.length = some (σ, (pre ++ wordsBytes (sigWords σ)).length) := by
  have hw : wordsBytes (sigWords σ) =
      enc64 σ.idx ++ σ.ots.flatMap Vector.toList ++ σ.path.flatMap Vector.toList := by
    simp [sigWords, wordsBytes_cons', wordsBytes_append', wordBytes_toWord,
      ParseProof.wordsBytes_digests, List.append_assoc]
  have hb0 : b.data.toList = pre ++ enc64 σ.idx ++
      (σ.ots.flatMap Vector.toList ++ σ.path.flatMap Vector.toList ++ post) := by
    simpa [hw, List.append_assoc] using hb
  have hb1 : b.data.toList = (pre ++ enc64 σ.idx) ++ σ.ots.flatMap Vector.toList ++
      (σ.path.flatMap Vector.toList ++ post) := by simpa [List.append_assoc] using hb0
  have hb2 : b.data.toList = (pre ++ enc64 σ.idx ++ σ.ots.flatMap Vector.toList) ++
      σ.path.flatMap Vector.toList ++ post := by simpa [List.append_assoc] using hb0
  have r0 := rdNat_enc64 hi hb0
  have r1 := rdDigests_flatMap σ.ots hb1
  have r2 := rdDigests_flatMap σ.path hb2
  rw [ho] at r1
  rw [hp] at r2
  simp only [rdSig, r0, Option.bind_eq_bind, Option.bind_some, r1, r2, pure]
  simp [hw, List.append_assoc]

/-- `rdSigned` reads the bytes of `signedWords` back. -/
theorem rdSigned_signedWords {b : ByteArray} {pre post : List UInt8} (p : Signed) (h : p.Fits)
    (hb : b.data.toList = pre ++ wordsBytes (signedWords p) ++ post) :
    rdSigned b pre.length = some (p, (pre ++ wordsBytes (signedWords p)).length) := by
  obtain ⟨hπ, ht, hq, hi, ho, hp⟩ := h
  let entries := wordsBytes (p.tr.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList)
  have hw : wordsBytes (signedWords p) = wordsBytes (bytesWords p.π.data.toList) ++
      enc64 p.tr.length ++ entries ++ wordsBytes (sigWords p.σ) := by
    simp [signedWords, logWords, wordsBytes_append', wordsBytes_cons', wordBytes_toWord,
      entries, List.append_assoc]
  have hb0 : b.data.toList = pre ++ wordsBytes (bytesWords p.π.data.toList) ++
      (enc64 p.tr.length ++ entries ++ wordsBytes (sigWords p.σ) ++ post) := by
    simpa [hw, List.append_assoc] using hb
  have hb1 : b.data.toList = (pre ++ wordsBytes (bytesWords p.π.data.toList)) ++ enc64 p.tr.length ++
      (entries ++ wordsBytes (sigWords p.σ) ++ post) := by simpa [List.append_assoc] using hb0
  have hb2 : b.data.toList = (pre ++ wordsBytes (bytesWords p.π.data.toList) ++ enc64 p.tr.length) ++
      entries ++ (wordsBytes (sigWords p.σ) ++ post) := by simpa [List.append_assoc] using hb0
  have hb3 : b.data.toList =
      (pre ++ wordsBytes (bytesWords p.π.data.toList) ++ enc64 p.tr.length ++ entries) ++
      wordsBytes (sigWords p.σ) ++ post := by simpa [List.append_assoc] using hb0
  have r0 := rdString_bytesWords p.π hπ hb0
  have r1 := rdNat_enc64 ht hb1
  have r2 := rdEntries_flatMap p.tr hq [] hb2
  have r3 := rdSig_sigWords p.σ hi ho hp hb3
  dsimp only [entries] at r3
  simp only [rdSigned, r0, Option.bind_eq_bind, Option.bind_some, r1, r2, r3, pure]
  simp [hw, entries, List.append_assoc]

/-- **L5b.** `parseB` reads the encoding of every fitting witness back. -/
theorem parseB_encode (w : Wit) (h : w.Fits) : parseB (WitnessSending.encode w) = some w := by
  have hd := WitnessSending.encode_data w
  cases w with
  | leaf s n =>
    have h0 : (WitnessSending.encode (.leaf s n)).data.toList =
        [] ++ enc64 0 ++ (s.toList ++ enc64 n) := by
      rw [hd]; simp [witWords, wordsBytes_append', wordsBytes_cons', wordsBytes_nil',
        ParseProof.wordsBytes_digest, wordBytes_toWord]
    have h1 : (WitnessSending.encode (.leaf s n)).data.toList =
        enc64 0 ++ s.toList ++ (enc64 n ++ []) := by rw [h0]; simp
    have h2 : (WitnessSending.encode (.leaf s n)).data.toList =
        (enc64 0 ++ s.toList) ++ enc64 n ++ [] := by rw [h0]; simp
    have r0 := rdNat_enc64 (by norm_num) h0
    have r1 := rdDigest_toList s h1
    have r2 := rdNat_enc64 (show n < 2 ^ 64 from h) h2
    simp only [List.length_nil, List.nil_append, List.length_append, enc64_length,
      Vector.length_toList] at r0 r1 r2
    simp [parseB, r0, r1, r2]
  | node c₁ c₂ p₁ p₂ =>
    obtain ⟨f₁, f₂⟩ := h
    have e : (WitnessSending.encode (.node c₁ c₂ p₁ p₂)).data.toList =
        enc64 1 ++ c₁.toList ++ c₂.toList ++ wordsBytes (signedWords p₁) ++
          wordsBytes (signedWords p₂) := by
      rw [hd]; simp [witWords, wordsBytes_append', wordsBytes_cons', ParseProof.wordsBytes_digest,
        wordBytes_toWord]
    have r0 := rdNat_enc64 (n := 1) (pre := []) (post := c₁.toList ++ c₂.toList ++
      wordsBytes (signedWords p₁) ++ wordsBytes (signedWords p₂)) (by norm_num) (by rw [e]; simp)
    have r1 := rdDigest_toList (pre := enc64 1) (post := c₂.toList ++
      wordsBytes (signedWords p₁) ++ wordsBytes (signedWords p₂)) c₁ (by rw [e]; simp)
    have r2 := rdDigest_toList (pre := enc64 1 ++ c₁.toList) (post :=
      wordsBytes (signedWords p₁) ++ wordsBytes (signedWords p₂)) c₂ (by rw [e]; simp)
    have r3 := rdSigned_signedWords (pre := enc64 1 ++ c₁.toList ++ c₂.toList)
      (post := wordsBytes (signedWords p₂)) p₁ f₁ (by rw [e])
    have r4 := rdSigned_signedWords (pre := enc64 1 ++ c₁.toList ++ c₂.toList ++
      wordsBytes (signedWords p₁)) (post := []) p₂ f₂ (by rw [e]; simp)
    simp only [List.length_nil, List.length_append, enc64_length, Vector.length_toList] at r0 r1 r2 r3 r4
    simp [parseB, r0, r1, r2, r3, r4]

end RecursionFast.FastCheck
