-- WP-14 (ASM). Adapted from rf-k/submissions/flock-recursive/lean/FRVerifierC4.lean@8bff272b
-- (`V4with`, `accWith4`, `acc_eq4`, `V4_W`, `V4_W_sound`, `V4_encode`, `complete4`, `V4_queries_le`)
-- and FRVIRSpecCore.lean@8bff272b (`encode_byte0`): two kinds (`S`, `W`) instead of five.
import RecursionFast.Library.WitnessSending
import RecursionFast.Library.Completeness

/-!
# The verifier `V`: dispatch on `π[0]` (BLUEPRINT §1)

`Vwith VS vk c π` reads byte 0 of `π`:

* `'S'` (`0x53`): the SNARK branch `VS vk c π` (`V_S`, WP-11a's `LvmVerifierS.VS`);
* anything else: the **witness-sending branch** (`W`): the Library's `WitnessSending.check`,
  with **this** verifier for a node's children (`accWith`, well-founded recursion on `|π|`, as
  FR's `V4with`). It asks no query. An honest witness-sending proof `encode w` starts with its tag
  word's low byte, `0` or `1` (`encode_byte0`), so it is never read as `'S'`.

BLUEPRINT §1 writes the `W` proof as `'W' ‖ encode w`; here it is `encode w` itself (any first byte
other than `'S'`), as in FR: then `E`'s `W` branch is the Library's `decode` and the right child of
an `S, b = 1` node, `⟨encode (leaf s n), [], σ_leaf⟩`, is a `W` proof with no prefix.

* **`acc_eq`**: the contract's `Submission.acc` with `V = Vwith VS` and `qV = qVlvm` is `accV VS`.
* **`V_S`**, **`V_W`**: the two branches; **`V_W_sound`**: an accepted `W` proof decodes to a witness
  of the relation; **`V_encode`**, **`complete`**: perfect completeness of `P := encode` (`δ = 0`).
* **`V_queries_le`**: `Vwith VS` asks at most `qVlvm` queries whenever `VS` does (`W` asks none).
-/

namespace Lvm.T

open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode decodeF encodeF decodeF_eq encodeF_eq
  size_child_lt)

/-- The declared verifier query bound (`claim.json`'s `qV`; `qS = 11,809` at `P20`). -/
def qVlvm : ℕ := 16384

/-- The SNARK kind byte `'S'`. -/
def sByte : UInt8 := 0x53

/-- **The kind of a proof**: `true` for the SNARK kind (first byte `'S'`). -/
def isS (π : Proof) : Bool := π.data.getD 0 0 == sByte

/-- A witness-sending proof's first byte is its tag word's: `0` or `1` (FR `encode_byte0`). -/
theorem encode_byte0 (w : Wit) : (encode w).data[0]? = some 0 ∨ (encode w).data[0]? = some 1 := by
  cases w <;> simp [encode, witWords, wordsBytes, wordBytes, enc64, toWord]

/-- An honest witness-sending proof is of the `W` kind. -/
theorem isS_encode (w : Wit) : isS (encode w) = false := by
  unfold isS
  rw [Array.getD_eq_getD_getElem?]
  rcases encode_byte0 w with h | h <;> rw [h] <;> decide

/-- **The dispatch is sound (A18)**: a witness-sending proof `encode w` carries no tag byte; its
first byte is the low byte of the leaf/node tag word (`0x00` or `0x01`, Library
`WitnessSending.encode`, `witWords`), never `'S'`, so `Vwith` sends every honest proof to the `W`
branch. -/
theorem encode_first_byte (w : Wit) :
    ((encode w).data.getD 0 0 = 0 ∨ (encode w).data.getD 0 0 = 1) ∧ (encode w).data.getD 0 0 ≠ sByte := by
  rw [Array.getD_eq_getD_getElem?]
  rcases encode_byte0 w with h | h <;> rw [h] <;> decide

/-- **Acceptance of a signed proof** with the verifier's program `v ()` (`Submission.acc` with
`qVlvm` and the Library's fast hashes). -/
def accWith (vk : Digest) (p : Signed) (v : Unit → OProg Bool) : Bool :=
  decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ qVlvm) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOkF vk (traceDigestF p.tr) p.σ &&
    decide ((v ()).runSeq p.tr = some true)

/-- The SNARK branch's type. -/
abbrev SProg := Digest → Digest → Proof → OProg Bool

/-- **The verifier**: `'S'` → `VS`; otherwise the witness-sending decision with this verifier for
the children. -/
def Vwith (VS : SProg) (vk c : Digest) (π : Proof) : OProg Bool :=
  if isS π then VS vk c π else
    match decodeF π with
    | some (.leaf s n) =>
      .ret (decide (encodeF (.leaf s n) = π) && decide (n ≤ chainCap) &&
        decide (c = leafStmtF (chainEndF s n) n))
    | some (.node c₁ c₂ p₁ p₂) =>
      if _h : encodeF (.node c₁ c₂ p₁ p₂) = π then
        .ret (decide (c = nodeStmtF c₁ c₂) && accWith vk p₁ (fun _ => Vwith VS vk c₁ p₁.π) &&
          accWith vk p₂ (fun _ => Vwith VS vk c₂ p₂.π))
      else .ret false
    | none => .ret false
termination_by π.size
decreasing_by
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).1
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).2

/-- **The acceptance predicate of the relation.** -/
def accV (VS : SProg) (vk c : Digest) (p : Signed) : Bool :=
  accWith vk p fun _ => Vwith VS vk c p.π

/-- **`acc_eq`**: `Submission.acc` is `accV VS` for a submission with verifier `Vwith VS` and query
bound `qVlvm`. -/
theorem acc_eq (VS : SProg) (S : Submission) (hV : S.V = Vwith VS) (hq : S.qV = qVlvm) :
    S.acc = accV VS := by
  funext vk c p
  rw [Submission.acc, accV, accWith, hV, hq, SigOkF_eq, traceDigestF_eq]

section Branches
variable (VS : SProg) (vk c : Digest) (π : Proof)

/-- The `S` branch. -/
theorem V_S (h : isS π = true) : Vwith VS vk c π = VS vk c π := by
  rw [Vwith, if_pos h]

/-- The `W` branch, with the specification functions. -/
theorem V_W (h : isS π = false) : Vwith VS vk c π = .ret (
    match decode π with
    | some (.leaf s n) =>
      decide (encode (.leaf s n) = π) && decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
    | some (.node c₁ c₂ p₁ p₂) =>
      if encode (.node c₁ c₂ p₁ p₂) = π then
        decide (c = nodeStmt c₁ c₂) && accV VS vk c₁ p₁ && accV VS vk c₂ p₂
      else false
    | none => false) := by
  rw [Vwith, if_neg (by simp [h])]
  simp only [decodeF_eq, encodeF_eq, leafStmtF_eq, chainEndF_eq, nodeStmtF_eq, accV]
  split <;> (try split) <;> simp_all

/-- **An accepted `W` proof is the canonical encoding of a witness of the relation.** -/
theorem V_W_sound (h : isS π = false) (hacc : Vwith VS vk c π = .ret true) :
    ∃ w, decode π = some w ∧ encode w = π ∧ Rel (accV VS vk) c w := by
  rw [V_W VS vk c π h, OProg.ret.injEq] at hacc
  split at hacc
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
    exact ⟨.leaf s n, hd, hacc.1.1, hacc.1.2, hacc.2⟩
  next c₁ c₂ p₁ p₂ hd =>
    split at hacc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
      exact ⟨.node c₁ c₂ p₁ p₂, hd, ‹_›, hacc.1.1, hacc.1.2, hacc.2⟩
    · cases hacc
  · cases hacc

/-- An accepted `W` proof on any log: the witness, and the relation. -/
theorem V_W_runLog (h : isS π = false) {L : Log} (hacc : (Vwith VS vk c π).runLog L = some true) :
    ∃ w, decode π = some w ∧ Rel (accV VS vk) c w := by
  rw [V_W VS vk c π h] at hacc
  obtain ⟨w, hw, -, hR⟩ := V_W_sound VS vk c π h (by
    rw [V_W VS vk c π h]; simpa [OProg.runLog] using hacc)
  exact ⟨w, hw, hR⟩

end Branches

/-! ## Queries (`KS`'s first conjunct) -/

/-- **`Vwith VS`'s queries** under `H`: at most `qVlvm`, given that bound for `VS`. The `W`
branch asks none. -/
theorem V_queries_le (VS : SProg) (H : ByteArray → Digest)
    (hS : ∀ vk c π, isS π = true → ((VS vk c π).queries H).length ≤ qVlvm) (vk c : Digest)
    (π : Proof) : ((Vwith VS vk c π).queries H).length ≤ qVlvm := by
  cases h : isS π
  · rw [V_W VS vk c π h]; exact Nat.zero_le _
  · rw [V_S VS vk c π h]; exact hS vk c π h

/-! ## Completeness (`δ = 0`, the `W` kind) -/

theorem fits_of_accWith {vk : Digest} {p : Signed} {v : Unit → OProg Bool}
    (h : accWith vk p v = true) : p.Fits := by
  simp only [accWith, Bool.and_eq_true, decide_eq_true_eq, SigOkF_eq, SigOk] at h
  obtain ⟨⟨⟨⟨hπ, htr⟩, hq⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, -⟩ := h
  exact ⟨hπ, htr.trans_lt (by decide), fun e he => (hq e he).trans_lt (by decide),
    hi.trans (by decide), ho, hp⟩

theorem fits_of_rel {VS : SProg} {vk c : Digest} {w : Wit} (h : Rel (accV VS vk) c w) : w.Fits := by
  cases w with
  | leaf s n => exact h.1.trans_lt (by decide)
  | node c₁ c₂ p₁ p₂ => exact ⟨fits_of_accWith h.2.1, fits_of_accWith h.2.2⟩

/-- **The honest proof of a witness of the relation is accepted, with no query.** -/
theorem V_encode (VS : SProg) {vk c : Digest} {w : Wit} (hR : Rel (accV VS vk) c w) :
    Vwith VS vk c (encode w) = .ret true := by
  rw [V_W VS vk c _ (isS_encode w), decode_encode w (fits_of_rel hR)]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ p₁ p₂ => simp [hR.1, hR.2.1, hR.2.2]

/-- **Perfect completeness** of `P vk c w := ret (encodeF w)`, for every key (Library
`complete_withError_zero`). -/
theorem complete (VS : SProg) (S : Submission) (hV : S.V = Vwith VS) (hq : S.qV = qVlvm)
    (hP : S.P = fun _ _ w => .ret (encodeF w)) (vk : Digest) :
    CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) 0 := by
  refine complete_withError_zero fun H c w hR => ?_
  rw [acc_eq VS S hV hq] at hR
  rw [hP, hV]
  show (Vwith VS vk c (encodeF w)).run H = true
  rw [encodeF_eq, V_encode VS hR]; rfl

/-! ## Controls -/

/-- (+) A witness-sending leaf proof of a true leaf statement is accepted with no query (any `VS`). -/
theorem ctrl_W_leaf (VS : SProg) (vk s : Digest) :
    Vwith VS vk (leafStmt (chainEnd s 0) 0) (encode (.leaf s 0)) = .ret true :=
  V_encode VS (c := leafStmt (chainEnd s 0) 0) (w := .leaf s 0) ⟨Nat.zero_le _, rfl⟩

/-- (+) A proof starting with `'S'` goes to the SNARK branch. -/
theorem ctrl_S (VS : SProg) (vk c : Digest) : Vwith VS vk c ⟨#[0x53]⟩ = VS vk c ⟨#[0x53]⟩ :=
  V_S VS vk c _ rfl

end Lvm.T
