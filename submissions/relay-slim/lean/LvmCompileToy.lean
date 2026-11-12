-- WP-5 (FS). The acceptance test of WP-5 (A0 §3): a toy knowledge certificate compiled and taken
-- through `KState.ks` to the contract's `KS`.
import LvmCompileKS
import LvmCompileCodec
import LvmCompileQB

/-!
# A toy instance of the compiler theorem

**The toy interactive proof.** Statement `x` (a digest; `σ = eOfBytes x`, its first 24 bytes as
an `E` scalar). The prover commits a word of two rows of one `K` word each, `w₀, w₁` (one
commitment, height 1, cap level 0: a Merkle root over two leaves), and claims
`w₀ + w₁ = σ` (in `E`). One **sumcheck round** for the sum of the line
`f(X) = w₀ + (w₀ + w₁)·X` over `{0, 1}` (characteristic 2: `f(0) + f(1) = w₀ + w₁`): the prover
sends `g = a + b·X`, the verifier checks `g(0) + g(1) = b = σ`, draws `r` (group 1); the prover
sends `v`, claimed `f(r)`; one **position group**: the verifier draws `s`, opens the positions
`pos s` (both rows, at positions that depend on `s`), and accepts iff `v = g(r)` and `v = f(r)`
for the opened rows.

**Its knowledge certificate** (`toyK`): doom after the commitment is `w₀ + w₁ ≠ σ`; after `g`,
`g ≠ f` or `b ≠ σ`; after `r`, `g(r) ≠ f(r)`; after `v`, `v ≠ g(r)` or `v ≠ f(r)`. Group 1
escapes with probability at most `1/|E|` (a nonzero line has at most one root); group 2 never
(the opened rows are the word's). No luck (`B = False`). Extraction: the committed word's rows.

**`toy_accepts`**: the compiled toy verifier accepts an honest all-zero proof on a log of its own
queries (non-vacuity). **`toy_ks`**: the contract's `KS` for the compiled toy verifier, the specification extractor, at
`ε = 2^-192 + badCount/2^256 ≤ 2^-138`, with `qV = 8` (`q₀`, seed, two challenges, two openings of
a leaf and a node).
-/

namespace Lvm.FS.Toy

open LeanVM.Parameters RecursionFast Lvm.FS
open LeanVM.Protocol.Compile hiding Proof  -- INT-1: WP-2's DSL also has a `Proof`; here it is `RecursionFast.Proof`
open scoped NNReal

/-- `K` in `E`. -/
abbrev ofB (u : K) : E := CompPoly.Extension.Ext.ofBase u

/-- The first word of row `0` and row `1`. -/
def w0 (w : Word) : K := (w 0).headD 0
def w1 (w : Word) : K := (w 1).headD 0

/-- The line through `(0, u₀)` and `(1, u₁)` at `r`. -/
def fw (u0 u1 : K) (r : E) : E := ofB u0 + (ofB u0 + ofB u1) * r

/-- The opened positions of the challenge `s`. -/
def pos (s : E) : List ℕ := if s = 0 then [0, 1] else [2, 3]

/-- The first word of the first and second opened rows. -/
def row0 (rows : List (List K)) : K := (rows.getD 0 []).headD 0
def row1 (rows : List (List K)) : K := (rows.getD 1 []).headD 0

/-- **The toy interactive program** for the claimed sum `σ`. -/
def prog (σ : E) : VerifierProgram Bool :=
  .commit 1 1 <| .read fun a => .read fun b =>
    if b = σ then
      .sample fun r => .read fun v => .sample fun s => .query 0 (pos s) fun rows =>
        .ret (decide (v = a + b * r) && decide (v = fw (row0 rows) (row1 rows) r))
    else .fail

/-- The witness of a pair of words (their bit patterns in the leaf's length field). -/
def toyWit (u0 u1 : K) : Wit := .leaf (dg []) (u0.toBitVec.toNat + 2 ^ 64 * u1.toBitVec.toNat)

/-- **The toy relation**: the witness is a pair of words whose sum is the statement's `σ`. -/
def toyR (c : Digest) (w : Wit) : Prop :=
  ∃ u0 u1 : K, ofB u0 + ofB u1 = eOfBytes c.toList ∧ w = toyWit u0 u1

/-- The first eight bytes of the proof are not the header: `π = x ‖ body`, `x` the statement. -/
def hdr (π : Proof) : Option (Digest × Bytes) :=
  if 32 ≤ π.size then some (dg (qb π), (qb π).drop 32) else none

/-- **The toy scheme.** -/
def toyS : Scheme where
  Stmt := Digest
  P x := prog (eOfBytes x.toList)
  enc x := x.toList
  enc_inj := fun a b h => Vector.toList_inj.mp h
  hdr := hdr
  ok c x := decide (c = x)
  capOf _ _ := 0
  q0 := [0x6c, 0x76, 0x6d, 0x2f, 0x74, 0x6f, 0x79]
  q0_short := by decide
  decE := eOfBytes
  decK := kOfBytes
  chal := chalOf
  chal_sum := chalOf_sum

/-! ## The toy program, step by step -/

section After

variable {α : Type}

theorem after_nil (p : VerifierProgram α) : p.after [] = some p := by
  simp [VerifierProgram.after]

theorem after_read_cons {k : E → VerifierProgram α} {e : Ev} {es : List Ev}
    {p : VerifierProgram α} :
    (VerifierProgram.read k).after (e :: es) = some p ↔
      ∃ x, e = .read x ∧ (k x).after es = some p := by
  cases e <;> simp [VerifierProgram.after]

theorem after_sample_cons {k : E → VerifierProgram α} {e : Ev} {es : List Ev}
    {p : VerifierProgram α} :
    (VerifierProgram.sample k).after (e :: es) = some p ↔
      ∃ c, e = .sample c ∧ (k c).after es = some p := by
  cases e <;> simp [VerifierProgram.after]

theorem after_commit_cons {ht w : ℕ} {k : VerifierProgram α} {e : Ev} {es : List Ev}
    {p : VerifierProgram α} :
    (VerifierProgram.commit ht w k).after (e :: es) = some p ↔
      ∃ word, e = .commit ht w word ∧ k.after es = some p := by
  cases e with
  | commit ht' w' word =>
    simp only [VerifierProgram.after, Ev.commit.injEq]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp only [false_iff, not_exists, not_and]
      intro _ h1 _; exact h ⟨h1.1.symm, h1.2.1.symm⟩
  | _ => simp [VerifierProgram.after]

theorem after_query_cons {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} {e : Ev}
    {es : List Ev} {p : VerifierProgram α} :
    (VerifierProgram.query i ps k).after (e :: es) = some p ↔
      ∃ rows, e = .query rows ∧ (k rows).after es = some p := by
  cases e <;> simp [VerifierProgram.after]

theorem after_ret_cons {b : α} {e : Ev} {es : List Ev} :
    (VerifierProgram.ret b).after (e :: es) = none := by
  cases e <;> rfl

theorem after_fail_cons {e : Ev} {es : List Ev} :
    (VerifierProgram.fail : VerifierProgram α).after (e :: es) = none := by
  cases e <;> rfl

end After

/-- The toy program after `v`, `s` and the opened rows. -/
def kRet (a b r v : E) (rows : List (List K)) : VerifierProgram Bool :=
  .ret (decide (v = a + b * r) && decide (v = fw (row0 rows) (row1 rows) r))

/-- The toy program after `v`. -/
def kS (a b r v : E) : VerifierProgram Bool := .sample fun s => .query 0 (pos s) (kRet a b r v)

/-- The toy program after `r`. -/
def kV (a b r : E) : VerifierProgram Bool := .read (kS a b r)

/-- The toy program after `b = σ`. -/
def kR (a b : E) : VerifierProgram Bool := .sample (kV a b)

/-- The toy program after `a`. -/
def kB (σ a : E) : VerifierProgram Bool := .read fun b => if b = σ then kR a b else .fail

/-- The toy program after the commitment. -/
def kA (σ : E) : VerifierProgram Bool := .read (kB σ)

theorem prog_eq (σ : E) : prog σ = .commit 1 1 (kA σ) := rfl

/-- **The histories of the toy program**, by shape. -/
theorem after_prog {σ : E} {h : List Ev} {p : VerifierProgram Bool}
    (hp : (prog σ).after h = some p) :
    (h = [] ∧ p = prog σ) ∨
    (∃ w, h = [.commit 1 1 w] ∧ p = kA σ) ∨
    (∃ w a, h = [.commit 1 1 w, .read a] ∧ p = kB σ a) ∨
    (∃ w a b, h = [.commit 1 1 w, .read a, .read b] ∧ p = if b = σ then kR a b else .fail) ∨
    (∃ w a r, h = [.commit 1 1 w, .read a, .read σ, .sample r] ∧ p = kV a σ r) ∨
    (∃ w a r v, h = [.commit 1 1 w, .read a, .read σ, .sample r, .read v] ∧ p = kS a σ r v) ∨
    (∃ w a r v s, h = [.commit 1 1 w, .read a, .read σ, .sample r, .read v, .sample s] ∧
      p = .query 0 (pos s) (kRet a σ r v)) ∨
    (∃ w a r v s rows, h = [.commit 1 1 w, .read a, .read σ, .sample r, .read v, .sample s,
      .query rows] ∧ p = kRet a σ r v rows) := by
  rcases h with _ | ⟨e, h⟩
  · rw [after_nil, Option.some.injEq] at hp
    exact .inl ⟨rfl, hp.symm⟩
  rw [prog_eq, after_commit_cons] at hp
  obtain ⟨w, rfl, hp⟩ := hp
  rcases h with _ | ⟨e, h⟩
  · rw [after_nil, Option.some.injEq] at hp
    exact .inr <| .inl ⟨w, rfl, hp.symm⟩
  rw [kA, after_read_cons] at hp
  obtain ⟨a, rfl, hp⟩ := hp
  rcases h with _ | ⟨e, h⟩
  · rw [after_nil, Option.some.injEq] at hp
    exact .inr <| .inr <| .inl ⟨w, a, rfl, hp.symm⟩
  rw [kB, after_read_cons] at hp
  obtain ⟨b, rfl, hp⟩ := hp
  rcases h with _ | ⟨e, h⟩
  · rw [after_nil, Option.some.injEq] at hp
    exact .inr <| .inr <| .inr <| .inl ⟨w, a, b, rfl, hp.symm⟩
  by_cases hb : b = σ
  swap
  · simp only [hb, ↓reduceIte, after_fail_cons, reduceCtorEq] at hp
  subst hb
  simp only [↓reduceIte] at hp
  rw [kR, after_sample_cons] at hp
  obtain ⟨r, rfl, hp⟩ := hp
  rcases h with _ | ⟨e, h⟩
  · rw [after_nil, Option.some.injEq] at hp
    exact .inr <| .inr <| .inr <| .inr <| .inl ⟨w, a, r, rfl, hp.symm⟩
  rw [kV, after_read_cons] at hp
  obtain ⟨v, rfl, hp⟩ := hp
  rcases h with _ | ⟨e, h⟩
  · rw [after_nil, Option.some.injEq] at hp
    exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨w, a, r, v, rfl, hp.symm⟩
  rw [kS, after_sample_cons] at hp
  obtain ⟨s, rfl, hp⟩ := hp
  rcases h with _ | ⟨e, h⟩
  · rw [after_nil, Option.some.injEq] at hp
    exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨w, a, r, v, s, rfl, hp.symm⟩
  rw [after_query_cons] at hp
  obtain ⟨rows, rfl, hp⟩ := hp
  rcases h with _ | ⟨e, h⟩
  · rw [after_nil, Option.some.injEq] at hp
    exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr ⟨w, a, r, v, s, rows, rfl, hp.symm⟩
  rw [kRet, after_ret_cons] at hp
  exact absurd hp (by simp)

/-! ## The certificate -/

/-- **The toy doom predicate** for the claimed sum `σ`. -/
def toyD (σ : E) : List Ev → Prop
  | [.commit _ _ w] => ofB (w0 w) + ofB (w1 w) ≠ σ
  | [.commit _ _ w, .read _] => ofB (w0 w) + ofB (w1 w) ≠ σ
  | [.commit _ _ w, .read a, .read b] => b ≠ σ ∨ a ≠ ofB (w0 w) ∨ b ≠ ofB (w0 w) + ofB (w1 w)
  | [.commit _ _ w, .read a, .read b, .sample r] => a + b * r ≠ fw (w0 w) (w1 w) r
  | [.commit _ _ w, .read a, .read b, .sample r, .read v] =>
    v ≠ a + b * r ∨ v ≠ fw (w0 w) (w1 w) r
  | [.commit _ _ w, .read a, .read b, .sample r, .read v, .sample _] =>
    v ≠ a + b * r ∨ v ≠ fw (w0 w) (w1 w) r
  | _ => False

/-- The groups' escape bound, `1/|E| = 2^-192`. -/
noncomputable def toyε : ℝ≥0 := (Fintype.card E : ℝ≥0)⁻¹


/-- Under a doom-free predicate the escape probability is `0`. -/
theorem escR_of_forall {D : List Ev → Prop} (hD : ∀ h, D h) :
    ∀ (p : VerifierProgram Bool) (h : List Ev), escR D h p = 0 := by
  intro p
  induction p with
  | ret b => intro h; cases b <;> simp [escR, hD]
  | fail => intro h; simp [escR]
  | read k ih => intro h; simp [escR, hD]
  | sample k ih => intro h; simp [escR, ih]
  | grind b k ih => intro h; simp [escR, hD]
  | commit ht w k ih => intro h; simp [escR, hD]
  | query i ps k ih => intro h; simp only [escR]; cases answer h i ps <;> simp [ih]

/-- The openings of the toy commitment: both rows, whatever `s`. -/
theorem answer_toy (w : Word) (a b r v s : E) :
    answer [.commit 1 1 w, .read a, .read b, .sample r, .read v, .sample s] 0 (pos s) =
      some [w 0, w 1] := by
  unfold pos; split_ifs <;> simp [answer, commits]

/-- A line through two different points' worth of coefficients meets the line `fw` at most once. -/
theorem card_root_le (w : Word) (a σ : E)
    (hD : a ≠ ofB (w0 w) ∨ σ ≠ ofB (w0 w) + ofB (w1 w)) :
    (Finset.univ.filter fun r : E => a + σ * r = fw (w0 w) (w1 w) r).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro r₁ h₁ r₂ h₂
  replace h₁ := (Finset.mem_filter.mp h₁).2
  replace h₂ := (Finset.mem_filter.mp h₂).2
  simp only [fw] at h₁ h₂
  by_contra hne
  have hmul : (σ - (ofB (w0 w) + ofB (w1 w))) * (r₁ - r₂) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp hmul with h | h
  · have hσ : σ = ofB (w0 w) + ofB (w1 w) := sub_eq_zero.mp h
    have ha : a = ofB (w0 w) := by rw [hσ] at h₁; linear_combination h₁
    rcases hD with hD | hD
    · exact hD ha
    · exact hD hσ
  · exact hne (sub_eq_zero.mp h)

/-- **The toy doom certificate.** -/
noncomputable def toyCert (σ : E) : Cert (prog σ) where
  D := toyD σ
  ε _ := (toyε : ENNReal)
  read := by
    intro h k x _ ha hD
    rcases after_prog ha with ⟨rfl, hp⟩ | ⟨w, rfl, hp⟩ | ⟨w, a, rfl, hp⟩ | ⟨w, a, b, rfl, hp⟩ |
      ⟨w, a, r, rfl, hp⟩ | ⟨w, a, r, v, rfl, hp⟩ | ⟨w, a, r, v, s, rfl, hp⟩ |
      ⟨w, a, r, v, s, rows, rfl, hp⟩
    · simp [prog] at hp
    · simp only [List.cons_append, List.nil_append, toyD] at hD ⊢
      exact hD
    · simp only [List.cons_append, List.nil_append, toyD] at hD ⊢
      by_cases hx : x = σ
      · exact .inr <| .inr fun h => hD (h.symm.trans hx)
      · exact .inl hx
    · split_ifs at hp
      simp [kR] at hp
    · simp only [List.cons_append, List.nil_append, toyD] at hD ⊢
      by_cases hx : x = a + σ * r
      · exact .inr fun h => hD (hx.symm.trans h)
      · exact .inl hx
    · simp [kS] at hp
    · simp at hp
    · simp [kRet] at hp
  grind := by
    intro h b k _ ha hD
    rcases after_prog ha with ⟨rfl, hp⟩ | ⟨w, rfl, hp⟩ | ⟨w, a, rfl, hp⟩ | ⟨w, a, b, rfl, hp⟩ |
      ⟨w, a, r, rfl, hp⟩ | ⟨w, a, r, v, rfl, hp⟩ | ⟨w, a, r, v, s, rfl, hp⟩ |
      ⟨w, a, r, v, s, rows, rfl, hp⟩
    · simp [prog] at hp
    all_goals first
      | (split_ifs at hp <;> simp [kR] at hp)
      | simp [kA, kB, kV, kS, kRet] at hp
  commit := by
    intro h ht w k word _ ha _ hD
    rcases after_prog ha with ⟨rfl, hp⟩ | ⟨w, rfl, hp⟩ | ⟨w, a, rfl, hp⟩ | ⟨w, a, b, rfl, hp⟩ |
      ⟨w, a, r, rfl, hp⟩ | ⟨w, a, r, v, rfl, hp⟩ | ⟨w, a, r, v, s, rfl, hp⟩ |
      ⟨w, a, r, v, s, rows, rfl, hp⟩
    · simp [toyD] at hD
    all_goals first
      | (split_ifs at hp <;> simp [kR] at hp)
      | simp [kA, kB, kV, kS, kRet] at hp
  group := by
    intro h p _ hb ha hsq hD
    rw [← coe_escR]
    refine ENNReal.coe_le_coe.mpr ?_
    rcases after_prog ha with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩ | ⟨w, a, rfl, rfl⟩ | ⟨w, a, b, rfl, rfl⟩ |
      ⟨w, a, r, rfl, rfl⟩ | ⟨w, a, r, v, rfl, rfl⟩ | ⟨w, a, r, v, s, rfl, rfl⟩ |
      ⟨w, a, r, v, s, rows, rfl, rfl⟩
    · simp [prog] at hsq
    · simp [kA] at hsq
    · simp [kB] at hsq
    · split_ifs with hbσ
      · -- group 1: the sumcheck challenge
        subst hbσ
        simp only [toyD, ne_eq, not_true_eq_false, false_or] at hD
        rw [kR, escR_sample]
        simp only [kV, escR]
        classical
        have hc : ∀ c : E, (if toyD b ([Ev.commit 1 1 w, Ev.read a, Ev.read b] ++ [Ev.sample c])
            then (0 : ℝ≥0) else 1) = if a + b * c = fw (w0 w) (w1 w) c then 1 else 0 := by
          intro c
          simp only [List.cons_append, List.nil_append]
          split_ifs with h1 h2 h2
          · exact absurd h2 h1
          · rfl
          · rfl
          · simp only [toyD, ne_eq, not_not] at h1
            exact absurd h1 h2
        rw [Finset.sum_congr rfl fun c _ => hc c, Finset.sum_boole]
        calc (Fintype.card E : ℝ≥0)⁻¹ * ((Finset.univ.filter fun c : E =>
                a + b * c = fw (w0 w) (w1 w) c).card : ℝ≥0)
            ≤ (Fintype.card E : ℝ≥0)⁻¹ * 1 := by
              gcongr; exact_mod_cast card_root_le w a b hD
          _ = toyε := mul_one _
      · simp [hbσ] at hsq
    · simp [kV] at hsq
    · -- group 2: the positions
      rw [kS, escR_sample]
      have hz : ∀ c, escR (toyD σ) ([Ev.commit 1 1 w, Ev.read a, Ev.read σ, Ev.sample r,
          Ev.read v] ++ [Ev.sample c]) (VerifierProgram.query 0 (pos c) (kRet a σ r v)) = 0 := by
        intro c
        simp only [List.cons_append, List.nil_append, escR, answer_toy]
        have h0 : row0 [w 0, w 1] = w0 w := rfl
        have h1 : row1 [w 0, w 1] = w1 w := rfl
        have hf : (decide (v = a + σ * r) && decide (v = fw (w0 w) (w1 w) r)) = false := by
          simp only [toyD] at hD
          rcases hD with hD | hD <;> simp [hD]
        rw [kRet, h0, h1, hf]
        simp [escR]
      rw [Finset.sum_congr rfl fun c _ => hz c]
      simp
    · exact False.elim hb
    · simp [kRet] at hsq
  final := by
    intro h _ ha
    rcases after_prog ha with ⟨rfl, hp⟩ | ⟨w, rfl, hp⟩ | ⟨w, a, rfl, hp⟩ | ⟨w, a, b, rfl, hp⟩ |
      ⟨w, a, r, rfl, hp⟩ | ⟨w, a, r, v, rfl, hp⟩ | ⟨w, a, r, v, s, rfl, hp⟩ |
      ⟨w, a, r, v, s, rows, rfl, hp⟩
    · simp [toyD]
    rotate_right
    · exact fun h => h
    all_goals first
      | (split_ifs at hp <;> simp [kR] at hp)
      | simp [kA, kB, kV, kS] at hp

/-- The extraction map: the rows of the first commitment. -/
def toyExt : List Ev → Wit
  | Ev.commit _ _ w :: _ => toyWit (w0 w) (w1 w)
  | _ => toyWit 0 0

/-- The toy program's static query bound: one commitment of one node level, two challenges, one
opening of two positions. -/
theorem toy_qb (σ : E) : toyS.QB 1 (prog σ) 6 := by
  refine .commit 1 1 _ 6 (Nat.sub_le _ _) (.read _ 6 fun a => .read _ 6 fun b => ?_)
  split_ifs
  · refine .sample _ 5 fun r => .read _ 5 fun v => .sample _ 4 fun s => ?_
    have h4 : (pos s).length * (1 + 1) + 0 = 4 := by unfold pos; split_ifs <;> rfl
    exact Scheme.QB.mono toyS (.query 0 (pos s) _ 0 fun rows => .ret _ 0) h4.le
  · exact .fail 6

/-- **The toy knowledge certificate.** -/
noncomputable def toyK : KCert toyS toyR where
  cert x := toyCert (eOfBytes x.toList)
  ε := toyε
  cert_ε _ _ _ _ _ := le_rfl
  ε_lt_one := by
    unfold toyε
    rw [BF64.card_ext3]
    exact inv_lt_one_of_one_lt₀ (by norm_num)
  B _ _ := False
  εB := 0
  εB_lt_one := zero_lt_one
  B_nil _ := not_false
  B_read _ _ _ _ := not_false
  B_commit _ _ _ _ _ := not_false
  B_group := by
    intro x h p _ _ _ _ _
    rw [← coe_escR, escR_of_forall (fun _ => not_false)]
  ext _ _ := toyExt
  extract := by
    intro c x h hok _ ha _ _ hpre
    have hc : c = x := by simpa [toyS] using hok
    subst hc
    rcases after_prog ha with ⟨rfl, hp⟩ | ⟨w, rfl, hp⟩ | ⟨w, a, rfl, hp⟩ | ⟨w, a, b, rfl, hp⟩ |
      ⟨w, a, r, rfl, hp⟩ | ⟨w, a, r, v, rfl, hp⟩ | ⟨w, a, r, v, s, rfl, hp⟩ |
      ⟨w, a, r, v, s, rows, rfl, hp⟩
    rotate_right
    · have hw := hpre [.commit 1 1 w] ⟨_, rfl⟩ trivial
      simp only [toyCert, toyD, ne_eq, not_not] at hw
      exact ⟨w0 w, w1 w, hw, rfl⟩
    · simp [prog] at hp
    all_goals first
      | (split_ifs at hp <;> simp [kR] at hp)
      | simp [kA, kB, kV, kS] at hp

/-- The toy certificate's error. -/
theorem toyK_ε : Scheme.εFS toyK ≤ (2 : ℝ≥0)⁻¹ ^ 138 := by
  have he : toyK.ε = (2 : ℝ≥0)⁻¹ ^ 192 := by
    show (Fintype.card E : ℝ≥0)⁻¹ = _
    rw [BF64.card_ext3, inv_pow]
    norm_num
  have h0 : toyK.εB = 0 := rfl
  unfold Scheme.εFS
  rw [he, h0, add_zero]
  calc (2 : ℝ≥0)⁻¹ ^ 192 + (badCount : ℝ≥0) / 2 ^ 256 ≤ 2⁻¹ ^ 139 + 2⁻¹ ^ 139 :=
        add_le_add (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num))
          badCount_div_le
    _ = 2⁻¹ ^ 138 := by ring

/-- The toy verifier asks at most `8` queries. -/
theorem toy_queries (H : ByteArray → Digest) (c : Digest) (π : Proof) :
    ((toyS.V c π).queries H).length ≤ 8 :=
  toyS.queries_V_le (fun x => toy_qb (eOfBytes x.toList)) H c π

/-- **The acceptance test**: the compiled toy verifier is knowledge sound at `2^-138` per query,
with the specification extractor. -/
theorem toy_ks : KS toyR toyS.V (toyS.Ex toyK.ext) ((2 : ℝ≥0)⁻¹ ^ 138) 8 :=
  ((Scheme.kstate_of_kcert toyK).mono toyK_ε).ks toy_queries

/-! ## The toy verifier accepts (non-vacuity) -/

/-- `n` zero bytes. -/
def zeros (n : ℕ) : Bytes := List.replicate n 0

/-- The zero digest. -/
def zd : Digest := Vector.replicate 32 0

/-- A proof of the statement `0` (`σ = 0`): header `0`, the cap, `a = b = 0`, `v = 0`, and the
two openings (row `0`, sibling = the zero leaf digest): 216 zero bytes. -/
def toyπ : Proof := toQ (zeros 216)

/-- A log answering every query of that run with the zero digest: `q₀`, the seed (64 bytes), the
two Fiat–Shamir queries (112 and 56 bytes), the leaf (8 bytes) and the node (64 bytes, the same
query as the seed's). -/
def toyL : Log :=
  [(toQ toyS.q0, zd), (toQ (zeros 64), zd), (toQ (zeros 112), zd), (toQ (zeros 56), zd),
    (toQ (zeros 8), zd)]

/-- **The compiled toy verifier accepts** an honest proof on a log of its queries (so `toy_ks`
is not vacuous). -/
theorem toy_accepts : (toyS.V zd toyπ).runLog toyL = some true := by
  decide +kernel

end Lvm.FS.Toy
