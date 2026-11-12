-- WP-5 (FS). New for lvm (BLUEPRINT §2.2, §7.3): the Fiat–Shamir compilation of a verifier
-- program onto the contract's oracle, the first-preimage reading of committed words, and the
-- specification extractor.
import LvmProg
import RecursionFast.Library.Security

/-!
# The compiled verifier (`compile P` of BLUEPRINT §7.3)

A **scheme** (`Scheme`) fixes the statement type, the interactive program `P x` of each statement,
the statement's bytes in the seed, the proof's header parser, the native statement check, the cap
level of each commitment shape, the constant first query `q₀`, and the byte decoders of `E`
scalars, `K` words and challenges (with the uniformity of the challenge map, `chal_sum`).

**The compiled verifier** `S.V c π` (BLUEPRINT §2.2, generic in the program):

* parse the header `x` of `π` (`hdr`), check `ok c x` natively; ask `q₀` (answer `a₀`), then the
  seed `a₀ ‖ enc x` (answer: the state `st₀`);
* run `P x` on the body with a state `st` and a buffer `buf` of absorbed-but-unsqueezed bytes:
  a `read` takes 24 bytes of the body into `buf`; a `commit` takes the cap (`2^c` digests,
  `c = capOf height width`) into `buf` and records it; a `sample` asks `st ‖ buf` (one query per
  challenge: the answer is the new state, its first 24 bytes the challenge, `chal`) and empties
  `buf`; a `query` opens each position from the body: the leaf's bytes (the row's last `occ`
  words, `Scheme.occ`; the words before them read as zero) are a leaf query, each
  sibling a node query `left ‖ right` (the position's bit at the level choosing the side), and the
  last answer must be the cap node above the position; `ret b` accepts iff `b` and the body is used
  up exactly; `fail` and `grind` (no proofs of work) reject;
* every Fiat–Shamir query is checked against `queryCap` before it is asked.

**The first-preimage reading** (`wordOf L ci`): the row at a position is read from the log by
walking down from the cap node over the *first* entry whose answer is the node (`findA`), taking
the half of a 64-byte query the position's bit names, then the first entry whose answer is the
leaf digest: its query's bytes are the leaf, read as the row by `padRow`; a missing entry reads as the empty byte
string (an erasure). Under no bad event (`LvmLog`) the reading of a cap absorbed into a query of
the log never changes when the log grows (`LvmForest`), and agrees with every Merkle opening the
verifier accepts.

**`trun`** runs the same program on a log and returns the interactive history it follows, words
read by `wordOf`; **`Ex ext`**, the specification extractor, runs it on the final log and applies
the certificate's extraction map (`KCert.ext`). It rebuilds each Fiat–Shamir query exactly
(state ‖ message from `π`) and looks the whole query up (BLUEPRINT A4).

`LengthRule` (BLUEPRINT §2.2, A8/R0) is recorded for the extractor program; the compiler theorem
does not need it: a log entry is classified by the program, never by its length.
-/

namespace Lvm.FS

open LeanVM.Parameters RecursionFast
open LeanVM.Protocol.Compile hiding Proof  -- INT-1: WP-2's DSL also has a `Proof`; here it is `RecursionFast.Proof`
open scoped NNReal

/-- Byte strings. -/
abbrev Bytes : Type := List UInt8

/-- The bytes of a query. -/
def qb (q : ByteArray) : Bytes := q.data.toList

/-- The query of a byte string. -/
def toQ (b : Bytes) : ByteArray := ⟨b.toArray⟩

@[simp] theorem qb_toQ (b : Bytes) : qb (toQ b) = b := by simp [qb, toQ]

@[simp] theorem size_toQ (b : Bytes) : (toQ b).size = b.length := by
  simp [toQ, ByteArray.size]

theorem size_eq_length_qb (q : ByteArray) : q.size = (qb q).length := by
  cases q; simp only [qb, ByteArray.size, Array.length_toList]

theorem toQ_qb (q : ByteArray) : toQ (qb q) = q := by
  cases q; simp only [qb, toQ, Array.toArray_toList]

theorem toQ_injective : Function.Injective toQ := fun a b h => by
  rw [← qb_toQ a, h, qb_toQ]

/-- The digest of the first 32 bytes of a byte string (zero-padded). -/
def dg (b : Bytes) : Digest := Vector.ofFn fun i => b.getD i 0

/-- The 32-byte window of a query at offset `k`. -/
def win (q : ByteArray) (k : ℕ) : Digest := dg ((qb q).drop k)

/-- `n` digests from consecutive 32-byte blocks. -/
def digestsOf (b : Bytes) (n : ℕ) : List Digest := (List.range n).map fun i => dg (b.drop (32 * i))

/-- A row of `w` words from consecutive 8-byte blocks. -/
def rowOf (dec : Bytes → K) (w : ℕ) (b : Bytes) : List K :=
  (List.range w).map fun i => dec ((b.drop (8 * i)).take 8)

@[simp] theorem length_rowOf (dec : Bytes → K) (w : ℕ) (b : Bytes) : (rowOf dec w b).length = w := by
  simp [rowOf]

/-- A row of `wd` words from a leaf that carries only the row's last `min oc wd` words (consecutive
8-byte blocks of `b`): the words before them read as zero. -/
def padRowOf (dec : Bytes → K) (wd oc : ℕ) (b : Bytes) : List K :=
  List.replicate (wd - min oc wd) 0 ++ rowOf dec (min oc wd) b

@[simp] theorem length_padRowOf (dec : Bytes → K) (wd oc : ℕ) (b : Bytes) :
    (padRowOf dec wd oc b).length = wd := by
  simp only [padRowOf, List.length_append, List.length_replicate, length_rowOf]
  omega

/-- A leaf that carries the whole row is the row. -/
theorem padRowOf_full (dec : Bytes → K) {wd oc : ℕ} (h : wd ≤ oc) (b : Bytes) :
    padRowOf dec wd oc b = rowOf dec wd b := by
  rw [padRowOf, Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append]

/-- A commitment as the compiled verifier holds it: height, width, cap level, cap nodes. -/
structure CapI where
  /-- `2^ht` rows. -/
  ht : ℕ
  /-- `wd` words per row. -/
  wd : ℕ
  /-- The cap is level `lv`: `2^lv` nodes. -/
  lv : ℕ
  /-- The cap nodes. -/
  cap : List Digest

/-- **A scheme**: the data the compiler needs besides the program. -/
structure Scheme where
  /-- The statements of the interactive proof. -/
  Stmt : Type
  /-- The interactive program of each statement. -/
  P : Stmt → VerifierProgram Bool
  /-- The statement's bytes in the seed query. -/
  enc : Stmt → Bytes
  enc_inj : Function.Injective enc
  /-- The proof's header and body. -/
  hdr : Proof → Option (Stmt × Bytes)
  /-- The native check of the contract statement against the header. -/
  ok : Digest → Stmt → Bool
  /-- The cap level of a commitment of `2^height` rows of `width` words. -/
  capOf : ℕ → ℕ → ℕ
  /-- The first query. -/
  q0 : Bytes
  q0_short : q0.length < 32
  /-- 24 bytes as a scalar. -/
  decE : Bytes → E
  /-- 8 bytes as a word. -/
  decK : Bytes → K
  /-- The challenge of an answer. -/
  chal : Digest → E
  /-- Uniform answers give uniform challenges: every challenge has `2^64` answers. -/
  chal_sum : ∀ f : E → ℝ≥0, ∑ a : Digest, f (chal a) = 2 ^ 64 * ∑ c : E, f c
  /-- The occupied words of a commitment of `2^height` rows of `width` words: a leaf carries only
  the row's last `min (occ height width) width` words, and the verifier reads the others as zero
  (the prover leaves them empty). By default every leaf carries its whole row. -/
  occ : ℕ → ℕ → ℕ := fun _ w => w

namespace Scheme

variable (S : Scheme)

/-- The cap bytes of a commitment shape. -/
def capBytes (ht w : ℕ) : ℕ := 32 * 2 ^ S.capOf ht w

/-- The commitment record of a cap read from `b`. -/
def capI (ht w : ℕ) (b : Bytes) : CapI :=
  ⟨ht, w, S.capOf ht w, digestsOf (b.take (S.capBytes ht w)) (2 ^ S.capOf ht w)⟩

/-! ## The compiled verifier -/

/-- Climb `n` levels from the digest `d` at position `q`, one sibling (32 bytes of the body) per
level: the node query is `d ‖ s` when the position's bit is `0`, else `s ‖ d`. Returns the top
digest and the rest of the body; `none` if the body runs out. -/
def climb : ℕ → Digest → ℕ → Bytes → OProg (Option (Digest × Bytes))
  | 0, d, _, body => .ret (some (d, body))
  | n + 1, d, q, body =>
    if body.length < 32 then .ret none else
    .query (toQ (if q % 2 = 0 then d.toList ++ body.take 32 else body.take 32 ++ d.toList))
      fun d' => climb n d' (q / 2) (body.drop 32)

/-- The bytes a leaf of `ci` carries: its row's occupied words. -/
def lb (ci : CapI) : ℕ := 8 * min (S.occ ci.ht ci.wd) ci.wd

/-- The row of `ci` a leaf's bytes give: zero words, then the occupied words. -/
def padRow (ci : CapI) (b : Bytes) : List K := padRowOf S.decK ci.wd (S.occ ci.ht ci.wd) b

@[simp] theorem length_padRow (ci : CapI) (b : Bytes) : (S.padRow ci b).length = ci.wd :=
  length_padRowOf _ _ _ _

/-- A commitment whose leaves carry their whole rows reads them as before. -/
theorem padRow_of_full (ci : CapI) (b : Bytes) (h : S.occ ci.ht ci.wd = ci.wd) :
    S.padRow ci b = rowOf S.decK ci.wd b :=
  padRowOf_full _ (le_of_eq h.symm) _

theorem lb_of_full (ci : CapI) (h : S.occ ci.ht ci.wd = ci.wd) : S.lb ci = 8 * ci.wd := by
  rw [lb, h, Nat.min_self]

/-- Open one position of a commitment: the leaf (`lb ci` bytes of the body: the row's occupied
words) as a leaf query, then the climb to the cap level, compared with the cap node above the
position; the row is the leaf read by `padRow`. -/
def openOne (ci : CapI) (p : ℕ) (body : Bytes) : OProg (Option (List K × Bytes)) :=
  if body.length < S.lb ci then .ret none else
  .query (toQ (body.take (S.lb ci))) fun d₀ =>
    (climb (ci.ht - ci.lv) d₀ (p % 2 ^ ci.ht) (body.drop (S.lb ci))).bind fun
      | some (top, rest) =>
        .ret (if ci.cap[p % 2 ^ ci.ht / 2 ^ (ci.ht - ci.lv)]? = some top then
          some (S.padRow ci (body.take (S.lb ci)), rest) else none)
      | none => .ret none

/-- Open positions in order. -/
def openAll (ci : CapI) : List ℕ → Bytes → OProg (Option (List (List K) × Bytes))
  | [], body => .ret (some ([], body))
  | p :: ps, body => (S.openOne ci p body).bind fun
      | some (r, rest) => (openAll ci ps rest).bind fun
          | some (rs, rest') => .ret (some (r :: rs, rest'))
          | none => .ret none
      | none => .ret none

/-- **The compiled run** of a program from state `st`, buffer `buf`, commitments `caps` on the
proof body `body`. -/
def run : VerifierProgram Bool → Digest → Bytes → List CapI → Bytes → OProg Bool
  | .ret b, _, _, _, body => .ret (b && body.isEmpty)
  | .fail, _, _, _, _ => .ret false
  | .grind _ _, _, _, _, _ => .ret false
  | .read k, st, buf, caps, body =>
    if body.length < 24 then .ret false else
    run (k (S.decE (body.take 24))) st (buf ++ body.take 24) caps (body.drop 24)
  | .sample k, st, buf, caps, body =>
    if 32 + buf.length ≤ queryCap then
      .query (toQ (st.toList ++ buf)) fun a => run (k (S.chal a)) a [] caps body
    else .ret false
  | .commit ht w k, st, buf, caps, body =>
    if body.length < S.capBytes ht w then .ret false else
    run k st (buf ++ body.take (S.capBytes ht w)) (caps ++ [S.capI ht w body])
      (body.drop (S.capBytes ht w))
  | .query i ps k, st, buf, caps, body =>
    match caps[i]? with
    | none => .ret false
    | some ci => (S.openAll ci ps body).bind fun
      | some (rows, rest) => run (k rows) st buf caps rest
      | none => .ret false

/-- The seed query of a statement after the answer `a₀` to `q₀`. -/
def seedQ (a₀ : Digest) (x : S.Stmt) : ByteArray := toQ (a₀.toList ++ S.enc x)

/-- The header checks before any query: the statement check and the seed's size. -/
def preOk (c : Digest) (x : S.Stmt) : Bool := S.ok c x && decide (32 + (S.enc x).length ≤ queryCap)

/-- **The compiled verifier** (`compile P`). -/
def V (c : Digest) (π : Proof) : OProg Bool :=
  match S.hdr π with
  | none => .ret false
  | some (x, body) =>
    if S.preOk c x then
      .query (toQ S.q0) fun a₀ => .query (S.seedQ a₀ x) fun st => S.run (S.P x) st [] [] body
    else .ret false

/-! ## The first-preimage reading of a committed word -/

/-- The first entry of the log whose answer is `v`. -/
def findA (L : Log) (v : Digest) : Option (ByteArray × Digest) := L.find? fun e => e.2 = v

/-- Walk down `n` levels from the node `v` towards position `q` (bit `n - 1` of `q` first): the
first entry answering the node must be a 64-byte query; its left half on bit `0`, else its right. -/
def descend (L : Log) : ℕ → Digest → ℕ → Option Digest
  | 0, v, _ => some v
  | n + 1, v, q => (findA L v).bind fun e =>
    if e.1.size = 64 then
      descend L n (if q / 2 ^ n % 2 = 0 then win e.1 0 else win e.1 32) q
    else none

/-- The leaf bytes the log holds under a commitment at a position (`none`: an erasure). -/
def leafBytes (L : Log) (ci : CapI) (p : ℕ) : Option Bytes :=
  (ci.cap[p % 2 ^ ci.ht / 2 ^ (ci.ht - ci.lv)]?).bind fun v =>
    (descend L (ci.ht - ci.lv) v (p % 2 ^ ci.ht)).bind fun d => (findA L d).map fun e => qb e.1

/-- **The word a log holds under a commitment**: the first-preimage reading of the leaf, read by
`padRow`; an erasure reads as the row of the empty byte string. Every row has `wd` words. -/
def wordOf (L : Log) (ci : CapI) : Word := fun p => S.padRow ci ((leafBytes L ci p).getD [])

theorem wellShaped_wordOf (L : Log) (ci : CapI) : WellShaped ci.wd (S.wordOf L ci) :=
  fun _ => S.length_padRow _ _

/-! ## The run on a log, as an interactive history -/

/-- **The compiled run on the log `L`, with the history it follows** (words by `wordOf L`):
`some (b, h)` when every query is answered by `L`; `b` is the verdict of `run`. -/
def trun (L : Log) : VerifierProgram Bool → Digest → Bytes → List CapI → Bytes → List Ev →
    Option (Bool × List Ev)
  | .ret b, _, _, _, body, h => some (b && body.isEmpty, h)
  | .fail, _, _, _, _, h => some (false, h)
  | .grind _ _, _, _, _, _, h => some (false, h)
  | .read k, st, buf, caps, body, h =>
    if body.length < 24 then some (false, h) else
    trun L (k (S.decE (body.take 24))) st (buf ++ body.take 24) caps (body.drop 24)
      (h ++ [.read (S.decE (body.take 24))])
  | .sample k, st, buf, caps, body, h =>
    if 32 + buf.length ≤ queryCap then
      (L.find? fun e => e.1 = toQ (st.toList ++ buf)).bind fun e =>
        trun L (k (S.chal e.2)) e.2 [] caps body (h ++ [.sample (S.chal e.2)])
    else some (false, h)
  | .commit ht w k, st, buf, caps, body, h =>
    if body.length < S.capBytes ht w then some (false, h) else
    trun L k st (buf ++ body.take (S.capBytes ht w)) (caps ++ [S.capI ht w body])
      (body.drop (S.capBytes ht w)) (h ++ [.commit ht w (S.wordOf L (S.capI ht w body))])
  | .query i ps k, st, buf, caps, body, h =>
    match caps[i]? with
    | none => some (false, h)
    | some ci => ((S.openAll ci ps body).runLog L).bind fun
      | some (rows, rest) => trun L (k rows) st buf caps rest (h ++ [.query rows])
      | none => some (false, h)

/-- **The specification extractor**: replay the compiled verifier on the final log and apply the
extraction map `ext` to the history of an accepting replay. -/
def Ex {Wit' : Type} (ext : Digest → S.Stmt → List Ev → Wit') (c : Digest) (π : Proof) (L : Log) :
    Option Wit' :=
  match S.hdr π with
  | none => none
  | some (x, body) =>
    if S.preOk c x then
      (L.find? fun e => e.1 = toQ S.q0).bind fun e₀ =>
      (L.find? fun e => e.1 = S.seedQ e₀.2 x).bind fun e₁ =>
      (S.trun L (S.P x) e₁.2 [] [] body []).bind fun r => if r.1 then some (ext c x r.2) else none
    else none

/-! ## The length rule (BLUEPRINT §2.2; for the extractor program, not used by the theorem) -/

/-- **The length rule** on a set `fs` of Fiat–Shamir query lengths, given the leaf lengths `leaf`:
no Fiat–Shamir query has a node's or a leaf's length, and no leaf has a node's length. -/
def LengthRule (fs leaf : List ℕ) : Prop := (∀ n ∈ fs, n ≠ 64 ∧ n ∉ leaf) ∧ 64 ∉ leaf

end Scheme

/-! ## The oracle-program facts the compiler uses -/

namespace OProgFacts

variable {α β : Type}

/-- `runLog` of a bind. -/
theorem runLog_bind (L : Log) (p : OProg α) (f : α → OProg β) :
    (p.bind f).runLog L = (p.runLog L).bind fun a => (f a).runLog L := by
  induction p with
  | ret a => simp [OProg.bind, OProg.runLog]
  | query q k ih =>
    simp only [OProg.bind, OProg.runLog]
    cases L.find? (fun e => decide (e.1 = q)) with
    | none => rfl
    | some e => simpa using ih e.2

end OProgFacts

namespace Scheme

variable (S : Scheme)

/-- **The compiled run is the replay's verdict.** -/
theorem runLog_run (L : Log) : ∀ (p : VerifierProgram Bool) (st : Digest) (buf : Bytes)
    (caps : List CapI) (body : Bytes) (h : List Ev),
    (S.run p st buf caps body).runLog L = (S.trun L p st buf caps body h).map Prod.fst := by
  intro p
  induction p with
  | ret b => intros; simp [run, trun, OProg.runLog]
  | fail => intros; simp [run, trun, OProg.runLog]
  | grind _ _ _ => intros; simp [run, trun, OProg.runLog]
  | read k ih =>
    intro st buf caps body h
    simp only [run, trun]
    split_ifs
    · simp [OProg.runLog]
    · exact ih _ _ _ _ _ _
  | sample k ih =>
    intro st buf caps body h
    simp only [run, trun]
    split_ifs
    · simp only [OProg.runLog]
      cases L.find? (fun e => decide (e.1 = toQ (st.toList ++ buf))) with
      | none => rfl
      | some e => exact ih _ _ _ _ _ _
    · simp [OProg.runLog]
  | commit ht w k ih =>
    intro st buf caps body h
    simp only [run, trun]
    split_ifs
    · simp [OProg.runLog]
    · exact ih _ _ _ _ _
  | query i ps k ih =>
    intro st buf caps body h
    simp only [run, trun]
    cases caps[i]? with
    | none => simp [OProg.runLog]
    | some ci =>
      simp only
      rw [OProgFacts.runLog_bind]
      cases (S.openAll ci ps body).runLog L with
      | none => rfl
      | some r =>
        rcases r with _ | ⟨rows, rest⟩
        · simp [OProg.runLog]
        · exact ih rows _ _ _ _ _

/-- The compiled verifier on a log, by the replay. -/
theorem runLog_V (L : Log) (c : Digest) (π : Proof) :
    (S.V c π).runLog L = match S.hdr π with
      | none => some false
      | some (x, body) =>
        if S.preOk c x then
          (L.find? fun e => e.1 = toQ S.q0).bind fun e₀ =>
          (L.find? fun e => e.1 = S.seedQ e₀.2 x).bind fun e₁ =>
          (S.trun L (S.P x) e₁.2 [] [] body []).map Prod.fst
        else some false := by
  unfold V
  rcases S.hdr π with _ | ⟨x, body⟩
  · rfl
  · simp only
    split_ifs
    · simp only [OProg.runLog]
      cases L.find? (fun e => decide (e.1 = toQ S.q0)) with
      | none => rfl
      | some e₀ =>
        simp only [Option.bind_some]
        cases L.find? (fun e => decide (e.1 = S.seedQ e₀.2 x)) with
        | none => rfl
        | some e₁ => exact S.runLog_run L _ _ _ _ _ _
    · rfl

end Scheme

end Lvm.FS
