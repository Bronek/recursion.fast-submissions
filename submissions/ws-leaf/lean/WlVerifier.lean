-- New for ws-leaf: the verifier, the honest prover and the certificate. The byte-level reader and
-- writer (`parseB`, `encodeB`), the chain in lanes (`chainEndH4`) and their statements are
-- relay-echo's (#12, Apache-2.0), in `WlFast*.lean`.
import WlExt
import WlFastSpec

/-!
# A witness-sending verifier that recomputes the leaf statements

The library's witness-sending argument (`RecursionFast.Library.WitnessSending`, #7) sends a node's
two child statements in the proof, so a prover must walk each new chain to name its leaf. This
verifier accepts, besides the library's proofs, **derived** proofs whose leaf statements it
recomputes itself; the extractor recomputes them on the contract's machine (`WlExt.lean`).

**Format.** A derived proof is `hdrB t sA nA sB nB ++ encodeB (.node c₁ c₂ p₁ p₂)`: a header of
11 words (the tag `t`, a chain start and length, another start and length), then a library node
encoding whose derived statements are zero.

* `t = 2`: the right child `p₂` is the leaf proof of `(sB, nB)`; its statement is recomputed
  (`lstmt sB nB`); the left child's statement `c₁` is sent and `p₁` is checked recursively
  (`sA = 0`, `nA = 0`).
* `t = 3`: both children are leaf proofs, of `(sA, nA)` and `(sB, nB)`; both statements are
  recomputed.

Every other proof is read as the library's (`parseB`, compared with `encodeB` of what was read).

* `check`: the decision; `V`, `P` (the library's encoding), `E := X.Ex`, `wsSub`.
* **`check_sound`**: an accepted proof is extracted to a witness of the relation, on every log.
* **`check_encode`**: the library's encoding of every witness of the relation is accepted.
* **`certificate`**: knowledge error `0`, completeness error `0`, `qV = 0`, fuel `2^36 + 16 t`.
-/

namespace WsLeaf

open RecursionFast RecursionFast.FastCheck WsLeaf.X

/-! ## The decision -/

/-- The zero digest (the derived statements' slots). -/
def zeroD : Digest := Vector.replicate 32 0

/-- The header of a derived proof: the tag, `(sA, nA)`, `(sB, nB)`, 88 bytes. -/
def hdrB (t : ℕ) (sA : Digest) (nA : ℕ) (sB : Digest) (nB : ℕ) : ByteArray :=
  pushU64 (pushDigest (pushU64 (pushDigest (pushU64 (ByteArray.emptyWithCapacity 88) t) sA) nA) sB)
    nB

/-- The leaf statement of a chain, the chain run in lanes (relay-echo's `chainEndH4`). -/
def lstmt (s : Digest) (n : ℕ) : Digest := leafStmtF (ofH4 (chainEndH4 (toH4 s) n)) n

/-- The start and length of a canonical leaf proof within `chainCap`. -/
def leafOf (p : Proof) : Option (Digest × ℕ) :=
  match parseB p with
  | some (.leaf s n) => if encodeB (.leaf s n) = p ∧ n ≤ chainCap then some (s, n) else none
  | _ => none

/-- A child's conjuncts of `acc` besides its verifier (`qV = 0`: an empty trace). -/
def sigOk (vk : Digest) (p : Signed) : Bool :=
  decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ 0) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOkF vk (traceDigestF p.tr) p.σ && p.tr.isEmpty

/-- The first word of a proof of at least 88 bytes (`0` for a shorter one). -/
def dtag (π : Proof) : ℕ := if h : 88 ≤ π.size then (u64At π 0 (by omega)).toNat else 0

/-- A derived node of tag `t`: the right child a leaf proof of `(sB, nB)`; for `t = 3` the left
child a leaf proof of `(sA, nA)`, otherwise the left statement sent and decided by `rec`. -/
def nodeD (vk c : Digest) (π : Proof) (t : ℕ) (c₁ c₂ : Digest) (p₁ p₂ : Signed)
    (rec : Unit → Bool) : Bool :=
  match leafOf p₂.π with
  | some (sB, nB) =>
    if t = 3 then
      match leafOf p₁.π with
      | some (sA, nA) =>
        decide (π = hdrB 3 sA nA sB nB ++ encodeB (.node c₁ c₂ p₁ p₂)) &&
          decide (c₁ = zeroD) && decide (c₂ = zeroD) &&
          decide (c = nodeStmtF (lstmt sA nA) (lstmt sB nB)) && sigOk vk p₁ && sigOk vk p₂
      | none => false
    else
      decide (π = hdrB 2 zeroD 0 sB nB ++ encodeB (.node c₁ c₂ p₁ p₂)) &&
        decide (c₂ = zeroD) && decide (c = nodeStmtF c₁ (lstmt sB nB)) &&
        (sigOk vk p₁ && rec ()) && sigOk vk p₂
  | none => false

/-- A library leaf: canonical, within `chainCap`, its statement. -/
def leafL (c : Digest) (π : Proof) (s : Digest) (n : ℕ) : Bool :=
  decide (encodeB (.leaf s n) = π) && decide (n ≤ chainCap) && decide (c = lstmt s n)

/-- A library node: canonical, its statement, its children (decided by `rec₁`, `rec₂`). -/
def nodeL (vk c : Digest) (π : Proof) (c₁ c₂ : Digest) (p₁ p₂ : Signed)
    (rec₁ rec₂ : Unit → Bool) : Bool :=
  if encodeB (.node c₁ c₂ p₁ p₂) = π then
    decide (c = nodeStmtF c₁ c₂) && (sigOk vk p₁ && rec₁ ()) && (sigOk vk p₂ && rec₂ ())
  else false

/-- A derived proof's node encoding: the bytes after the 88-byte header (irreducible, so that the
recursion's elaboration does not unfold the copy). -/
@[irreducible] def tailB (π : Proof) : ByteArray := π.extract 88 π.size

/-- **One level of the decision**, the children decided by `rec`: a derived proof (tag 2 or 3)
or a library proof. -/
def stepB (vk c : Digest) (π : Proof) (rec : Digest → Proof → Bool) : Bool :=
  if dtag π = 2 ∨ dtag π = 3 then
    match parseB (tailB π) with
    | some (.node c₁ c₂ p₁ p₂) => nodeD vk c π (dtag π) c₁ c₂ p₁ p₂ (fun _ => rec c₁ p₁.π)
    | _ => false
  else
    match parseB π with
    | some (.leaf s n) => leafL c π s n
    | some (.node c₁ c₂ p₁ p₂) =>
      nodeL vk c π c₁ c₂ p₁ p₂ (fun _ => rec c₁ p₁.π) (fun _ => rec c₂ p₂.π)
    | none => false

/-- **The decision**: `stepB`, each child (shorter than `π`) decided by `check`. -/
def check (vk c : Digest) (π : Proof) : Bool :=
  stepB vk c π fun c' π' => if _h : π'.size < π.size then check vk c' π' else false
termination_by π.size

/-- The verifier: `check`, with no oracle query. -/
def V (vk c : Digest) (π : Proof) : OProg Bool := .ret (check vk c π)

/-- The honest prover (the Lean side): the library's encoding of the witness. The native prover
sends derived proofs instead. -/
def P (_ _ : Digest) (w : Wit) : OProg Proof := .ret (encodeB w)

/-- **The submission.** -/
def wsSub : Submission where
  V := V
  P := P
  E := Ex
  ext := ext
  ε := 0
  δ := 0
  qV := 0
  fuel := fuelW

/-! ## Acceptance -/

/-- **What `acc` of this submission decides**: a child's conjuncts, then `check`. -/
theorem acc_eq (vk c : Digest) (p : Signed) : wsSub.acc vk c p = (sigOk vk p && check vk c p.π) := by
  have h : wsSub.acc vk c p = (decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ 0) &&
      decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOk vk (traceDigest p.tr) p.σ &&
      (p.tr.isEmpty && check vk c p.π)) :=
    congrArg (_ && ·) (WitnessSending.runSeq_ret_eq _ _)
  rw [h, sigOk, SigOkF_eq, traceDigestF_eq]
  simp only [Bool.and_assoc]

/-- A child that passes `sigOk` fits the output format. -/
theorem fits_of_sigOk {vk : Digest} {p : Signed} (h : sigOk vk p = true) : p.Fits := by
  simp only [sigOk, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, SigOkF_eq, SigOk] at h
  obtain ⟨⟨⟨⟨hπ, -⟩, -⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, htr⟩ := h
  exact ⟨hπ, by simp [htr], by simp [htr], hi.trans (by decide), ho, hp⟩

theorem lstmt_eq (s : Digest) (n : ℕ) : lstmt s n = leafStmt (chainEnd s n) n := by
  rw [lstmt, chainEnd_lanes, leafStmtF_eq, chainEndF_eq]

theorem leafOf_spec {p : Proof} {s : Digest} {n : ℕ} (h : leafOf p = some (s, n)) :
    encodeB (.leaf s n) = p ∧ n ≤ chainCap := by
  unfold leafOf at h
  split at h
  · split_ifs at h with hc
    cases h
    exact hc
  · cases h

theorem size_encodeB_leaf (s : Digest) (n : ℕ) : (encodeB (.leaf s n)).size = 48 := by
  rw [encodeB_eq]; exact WitnessSending.size_encode_leaf s n

theorem dtag_small {π : Proof} (h : π.size < 88) : dtag π = 0 := by
  simp [dtag, show ¬ 88 ≤ π.size by omega]

/-- **A canonical leaf proof is accepted for its statement**, with no recursion. -/
theorem check_leaf (vk : Digest) {p : Proof} {s : Digest} {n : ℕ} (h : leafOf p = some (s, n)) :
    check vk (lstmt s n) p = true := by
  obtain ⟨he, hn⟩ := leafOf_spec h
  have hp : parseB p = some (.leaf s n) := by
    rw [← he, encodeB_eq, parseB_encode _ (lt_of_le_of_lt hn (by decide))]
  have hd : dtag p = 0 := dtag_small (by rw [← he, size_encodeB_leaf]; omega)
  rw [check, stepB, hd]
  simp only [show ¬ ((0 : ℕ) = 2 ∨ (0 : ℕ) = 3) by omega, ite_false, hp, leafL, he, hn,
    decide_true, Bool.and_self]

/-! ## The extractor's words -/

/-- The header's words. -/
def hdrW (t : ℕ) (sA : Digest) (nA : ℕ) (sB : Digest) (nB : ℕ) : List Word :=
  toWord t :: packBytes sA.toList ++ toWord nA :: packBytes sB.toList ++ [toWord nB]

theorem hdrB_data (t : ℕ) (sA : Digest) (nA : ℕ) (sB : Digest) (nB : ℕ) :
    (hdrB t sA nA sB nB).data.toList = wordsBytes (hdrW t sA nA sB nB) := by
  simp [hdrB, hdrW, pushU64_data, pushDigest_data, wordsBytes_append', wordsBytes_cons',
    wordsBytes_nil', ParseProof.wordsBytes_digest, wordBytes_toWord]

theorem packBytes_encodeB (w : Wit) : packBytes (encodeB w).data.toList = witWords w := by
  rw [encodeB_data, packBytes_wordsBytes]

theorem packBytes_derived (t : ℕ) (sA : Digest) (nA : ℕ) (sB : Digest) (nB : ℕ) (w : Wit) :
    packBytes (hdrB t sA nA sB nB ++ encodeB w).data.toList = hdrW t sA nA sB nB ++ witWords w := by
  rw [ByteArray.data_append, Array.toList_append, hdrB_data, encodeB_data, ← wordsBytes_append',
    packBytes_wordsBytes]

/-- A digest's packed words, as a four-element list. -/
theorem packBytes_four (d : Digest) : packBytes d.toList = [(packBytes d.toList).getD 0 0,
    (packBytes d.toList).getD 1 0, (packBytes d.toList).getD 2 0, (packBytes d.toList).getD 3 0] := by
  have h4 := packBytes_digest_length d
  refine List.ext_getElem (by simp [h4]) fun j h1 h2 => ?_
  have hj : j < 4 := by simpa using h2
  interval_cases j <;> simp [h4]

/-- The derived leaf statement of a header's start and length is the leaf statement. -/
theorem digW_lstmt (s : Digest) {n : ℕ} (hn : n ≤ chainCap) :
    digW ((packBytes s.toList).getD 0 0) ((packBytes s.toList).getD 1 0)
      ((packBytes s.toList).getD 2 0) ((packBytes s.toList).getD 3 0) (toWord n) =
      packBytes (lstmt s n).toList := by
  have hn64 : n < 2 ^ 64 := lt_of_le_of_lt hn (by decide)
  rw [digW, dgW_packBytes, toNat_toWord hn64, Nat.min_eq_left hn, lstmt_eq]

/-- **`fillW` on a derived proof's words**: the derived statements written in. -/
theorem fillW_derived (t : ℕ) (ht : t = 2 ∨ t = 3) (sA : Digest) (nA : ℕ) (sB : Digest) (nB : ℕ)
    (c₁ c₂ : Digest) (p₁ p₂ : Signed) :
    fillW (hdrW t sA nA sB nB ++ witWords (.node c₁ c₂ p₁ p₂)) =
      1 :: ((if t = 3 then
          digW ((packBytes sA.toList).getD 0 0) ((packBytes sA.toList).getD 1 0)
            ((packBytes sA.toList).getD 2 0) ((packBytes sA.toList).getD 3 0) (toWord nA)
        else packBytes c₁.toList) ++
        digW ((packBytes sB.toList).getD 0 0) ((packBytes sB.toList).getD 1 0)
          ((packBytes sB.toList).getD 2 0) ((packBytes sB.toList).getD 3 0) (toWord nB) ++
        (signedWords p₁ ++ signedWords p₂)) := by
  obtain ⟨a0, a1, a2, a3, hA⟩ : ∃ a0 a1 a2 a3, packBytes sA.toList = [a0, a1, a2, a3] :=
    ⟨_, _, _, _, packBytes_four sA⟩
  obtain ⟨b0, b1, b2, b3, hB⟩ : ∃ a0 a1 a2 a3, packBytes sB.toList = [a0, a1, a2, a3] :=
    ⟨_, _, _, _, packBytes_four sB⟩
  obtain ⟨e0, e1, e2, e3, hC⟩ : ∃ a0 a1 a2 a3, packBytes c₁.toList = [a0, a1, a2, a3] :=
    ⟨_, _, _, _, packBytes_four c₁⟩
  obtain ⟨f0, f1, f2, f3, hD⟩ : ∃ a0 a1 a2 a3, packBytes c₂.toList = [a0, a1, a2, a3] :=
    ⟨_, _, _, _, packBytes_four c₂⟩
  rw [hdrW, witWords, hA, hB, hC, hD]
  rcases ht with rfl | rfl
  · simp [fillW, toWord]
  · simp [fillW, toWord]

/-- A node's words, regrouped as `fillW_derived` writes them. -/
theorem witWords_node (c₁ c₂ : Digest) (p₁ p₂ : Signed) : witWords (.node c₁ c₂ p₁ p₂) =
    1 :: (packBytes c₁.toList ++ packBytes c₂.toList ++ (signedWords p₁ ++ signedWords p₂)) := by
  simp only [witWords, List.append_assoc]
  rfl

/-- `fillW` leaves the words of a library witness alone (its first word is `0` or `1`). -/
theorem fillW_witWords (w : Wit) : fillW (witWords w) = witWords w := by
  cases w <;> simp [fillW, witWords, toWord]


/-! ## Knowledge soundness -/

/-- A child accepted by the guarded recursion is accepted. -/
theorem rec_true {vk c : Digest} {π π' : Proof}
    (h : (if _h : π'.size < π.size then check vk c π' else false) = true) : check vk c π' = true := by
  split_ifs at h
  exact h

/-- **An accepted proof is extracted to a witness of the relation**, on every log. -/
theorem check_sound {vk c : Digest} {π : Proof} (h : check vk c π = true) (L : Log) :
    ∃ w, Ex c π L = some w ∧ Rel (wsSub.acc vk) c w := by
  rw [check] at h
  have hrec : ∀ c' π', (fun c' (π' : Proof) => if _h : π'.size < π.size then check vk c' π' else
      false) c' π' = true → check vk c' π' = true := fun _ _ h => rec_true h
  generalize (fun c' (π' : Proof) => if _h : π'.size < π.size then check vk c' π' else false) = rec
    at h hrec
  unfold stepB at h
  split_ifs at h with hd
  · split at h
    next c₁ c₂ p₁ p₂ _ =>
      unfold nodeD at h
      split at h
      next sB nB hB =>
        obtain ⟨-, hnB⟩ := leafOf_spec hB
        split_ifs at h with h3
        · split at h
          next sA nA hA =>
            obtain ⟨-, hnA⟩ := leafOf_spec hA
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨⟨hπ, -⟩, -⟩, hc⟩, hs1⟩, hs2⟩ := h
            refine ⟨.node (lstmt sA nA) (lstmt sB nB) p₁ p₂, ?_, ?_⟩
            · rw [Ex, hπ, packBytes_derived, fillW_derived 3 (Or.inr rfl), if_pos rfl,
                digW_lstmt sA hnA, digW_lstmt sB hnB, ← witWords_node]
              exact decodeWit_witWords (.node _ _ p₁ p₂) ⟨fits_of_sigOk hs1, fits_of_sigOk hs2⟩
            · exact ⟨by rw [hc, nodeStmtF_eq], by rw [acc_eq, hs1, check_leaf vk hA]; rfl,
                by rw [acc_eq, hs2, check_leaf vk hB]; rfl⟩
          next => cases h
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨hπ, -⟩, hc⟩, hs1, hr1⟩, hs2⟩ := h
          refine ⟨.node c₁ (lstmt sB nB) p₁ p₂, ?_, ?_⟩
          · rw [Ex, hπ, packBytes_derived, fillW_derived 2 (Or.inl rfl), if_neg (by omega),
              digW_lstmt sB hnB, ← witWords_node]
            exact decodeWit_witWords (.node _ _ p₁ p₂) ⟨fits_of_sigOk hs1, fits_of_sigOk hs2⟩
          · exact ⟨by rw [hc, nodeStmtF_eq], by rw [acc_eq, hs1, hrec _ _ hr1]; rfl,
              by rw [acc_eq, hs2, check_leaf vk hB]; rfl⟩
      next => cases h
    next => cases h
  · split at h
    next s n _ =>
      simp only [leafL, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨he, hn⟩, hc⟩ := h
      refine ⟨.leaf s n, ?_, hn, by rw [hc, lstmt_eq]⟩
      rw [Ex, ← he, packBytes_encodeB, fillW_witWords]
      exact decodeWit_witWords _ (lt_of_le_of_lt hn (by decide))
    next c₁ c₂ p₁ p₂ _ =>
      unfold nodeL at h
      split_ifs at h with he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hc, hs1, hr1⟩, hs2, hr2⟩ := h
      refine ⟨.node c₁ c₂ p₁ p₂, ?_, by rw [hc, nodeStmtF_eq],
        by rw [acc_eq, hs1, hrec _ _ hr1]; rfl, by rw [acc_eq, hs2, hrec _ _ hr2]; rfl⟩
      rw [Ex, ← he, packBytes_encodeB, fillW_witWords]
      exact decodeWit_witWords _ ⟨fits_of_sigOk hs1, fits_of_sigOk hs2⟩
    next => cases h

/-! ## Completeness -/

/-- The first word of the library's encoding is its tag, `0` or `1`. -/
theorem dtag_encodeB (w : Wit) : dtag (encodeB w) < 2 := by
  unfold dtag
  split_ifs with h
  · rw [u64At_toNat, List.drop_zero, encodeB_data]
    cases w <;>
      simp only [witWords, List.cons_append, wordsBytes_cons', List.take_left' (wordBytes_length _),
        ofLE_wordBytes, toWord] <;> decide
  · omega

/-- **The library's encoding of every witness of the relation is accepted.** -/
theorem check_encode {vk c : Digest} {w : Wit} (hR : Rel (wsSub.acc vk) c w) :
    check vk c (encodeB w) = true := by
  have hfit : w.Fits := by
    cases w with
    | leaf s n => exact lt_of_le_of_lt hR.1 (by decide)
    | node c₁ c₂ p₁ p₂ =>
      obtain ⟨-, h1, h2⟩ := hR
      rw [acc_eq, Bool.and_eq_true] at h1 h2
      exact ⟨fits_of_sigOk h1.1, fits_of_sigOk h2.1⟩
  have hd := dtag_encodeB w
  rw [check, stepB, if_neg (by omega), encodeB_eq, parseB_encode w hfit, ← encodeB_eq]
  cases w with
  | leaf s n =>
    simp only [leafL, decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hR.1, by rw [lstmt_eq]; exact hR.2⟩
  | node c₁ c₂ p₁ p₂ =>
    have hs := WitnessSending.size_child_lt c₁ c₂ p₁ p₂
    rw [← encodeB_eq] at hs
    obtain ⟨hc, h1, h2⟩ := hR
    rw [acc_eq] at h1 h2
    simp only [nodeL, ite_true, dite_eq_left hs.1, dite_eq_left hs.2]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    exact ⟨⟨by rw [nodeStmtF_eq]; exact hc, h1⟩, h2⟩

/-! ## The certificate -/

/-- The knowledge state under `vk`: the potential `0`. -/
def kstate (vk : Digest) : KState (Rel (wsSub.acc vk)) (wsSub.V vk) wsSub.E 0 :=
  KState.zero 0 fun L _ _ h => check_sound (Option.some.inj h) L

theorem ks (vk : Digest) : KS (Rel (wsSub.acc vk)) (wsSub.V vk) wsSub.E wsSub.ε wsSub.qV :=
  (kstate vk).ks fun _ _ _ => le_rfl

theorem complete_perfect (vk : Digest) :
    Complete (Rel (wsSub.acc vk)) (wsSub.P vk) (wsSub.V vk) := fun _ _ _ hR => check_encode hR

/-- **The certificate**, for every public key. -/
theorem certificate : Certificate wsSub where
  secure := ks
  complete vk := complete_withError_zero (complete_perfect vk)
  computes := computes
  cap := ⟨zero_le, zero_le, Nat.zero_le _, fuelW_le_budget, size_ext⟩


end WsLeaf
