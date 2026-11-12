-- WP-5 (FS). New for lvm: a static bound on the compiled verifier's queries (the `qV` of `KS`).
import LvmCompile

/-!
# The query bound of the compiled verifier

`QB S lv p n`: on every path, the compiled run of `p` asks at most `n` queries, when every
commitment of `p` has at most `lv` node levels below its cap (`ht - capOf ht w ≤ lv`): a challenge
costs one query, an opening of `m` positions `m·(lv + 1)` (a leaf and `lv` nodes each), a read or
a commitment none. **`queries_V_le`**: then the compiled verifier asks at most `2 + n`
(`q₀` and the seed first) under every oracle.
-/

namespace Lvm.FS

open LeanVM.Parameters RecursionFast
open LeanVM.Protocol.Compile hiding Proof  -- INT-1: WP-2's DSL also has a `Proof`; here it is `RecursionFast.Proof`

namespace Scheme

variable (S : Scheme)

/-- **A static query bound** of a program. -/
inductive QB (lv : ℕ) : VerifierProgram Bool → ℕ → Prop
  | ret (b : Bool) (n : ℕ) : QB lv (.ret b) n
  | fail (n : ℕ) : QB lv .fail n
  | grind (bits : ℕ) (k : VerifierProgram Bool) (n : ℕ) : QB lv (.grind bits k) n
  | read (k : E → VerifierProgram Bool) (n : ℕ) : (∀ x, QB lv (k x) n) → QB lv (.read k) n
  | sample (k : E → VerifierProgram Bool) (n : ℕ) : (∀ c, QB lv (k c) n) → QB lv (.sample k) (n + 1)
  | commit (ht w : ℕ) (k : VerifierProgram Bool) (n : ℕ) : ht - S.capOf ht w ≤ lv → QB lv k n →
      QB lv (.commit ht w k) n
  | query (i : ℕ) (ps : List ℕ) (k : List (List K) → VerifierProgram Bool) (n : ℕ) :
      (∀ rows, QB lv (k rows) n) → QB lv (.query i ps k) (ps.length * (lv + 1) + n)

/-- A larger bound holds. -/
theorem QB.mono {lv : ℕ} {p : VerifierProgram Bool} {n m : ℕ} (h : S.QB lv p n) (hnm : n ≤ m) :
    S.QB lv p m := by
  induction h generalizing m with
  | ret b n => exact .ret b m
  | fail n => exact .fail m
  | grind bits k n => exact .grind bits k m
  | read k n _ ih => exact .read k m fun x => ih x hnm
  | sample k n _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .sample k m' fun c => ih c (by omega)
  | commit ht w k n hlv _ ih => exact .commit ht w k m hlv (ih hnm)
  | query i ps k n _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = ps.length * (lv + 1) + m' :=
      ⟨m - ps.length * (lv + 1), by omega⟩
    exact .query i ps k m' fun rows => ih rows (by omega)

/-- A bind asks the first program's queries and at most `m` more. -/
theorem length_queries_bind_le {α β : Type} (H : ByteArray → Digest) (p : OProg α)
    (f : α → OProg β) (m : ℕ) (hf : ∀ a, ((f a).queries H).length ≤ m) :
    ((p.bind f).queries H).length ≤ (p.queries H).length + m := by
  induction p with
  | ret a => simpa [OProg.bind, OProg.queries] using hf a
  | query q k ih =>
    simp only [OProg.bind, OProg.queries, List.length_cons]
    have := ih (H q)
    omega

/-- A climb asks at most one query per level. -/
theorem queries_climb (H : ByteArray → Digest) :
    ∀ (n : ℕ) (d : Digest) (q : ℕ) (body : Bytes), ((climb n d q body).queries H).length ≤ n
  | 0, _, _, _ => by simp [climb, OProg.queries]
  | n + 1, d, q, body => by
    unfold climb
    split_ifs
    · simp [OProg.queries]
    all_goals
      simp only [OProg.queries, List.length_cons]
      exact Nat.succ_le_succ (queries_climb H n _ _ _)

/-- An opening of one position asks at most a leaf and `ht - lv` nodes. -/
theorem queries_openOne (H : ByteArray → Digest) (ci : CapI) (p : ℕ) (body : Bytes) :
    ((S.openOne ci p body).queries H).length ≤ 1 + (ci.ht - ci.lv) := by
  unfold openOne
  split_ifs
  · simp [OProg.queries]
  · simp only [OProg.queries, List.length_cons]
    refine (Nat.succ_le_succ (length_queries_bind_le H _ _ 0 fun r => ?_)).trans ?_
    · rcases r with _ | ⟨top, rest⟩ <;> simp [OProg.queries]
    · have := queries_climb H (ci.ht - ci.lv) (H (toQ (body.take (8 * ci.wd))))
        (p % 2 ^ ci.ht) (body.drop (8 * ci.wd))
      omega

/-- An opening of `ps` asks at most `ps.length · (lv + 1)` queries. -/
theorem queries_openAll (H : ByteArray → Digest) {lv : ℕ} (ci : CapI) (hci : ci.ht - ci.lv ≤ lv) :
    ∀ (ps : List ℕ) (body : Bytes), ((S.openAll ci ps body).queries H).length ≤ ps.length * (lv + 1)
  | [], body => by simp [openAll, OProg.queries]
  | p :: ps, body => by
    unfold openAll
    have h1 := S.queries_openOne H ci p body
    refine (length_queries_bind_le H _ _ (ps.length * (lv + 1)) fun r => ?_).trans ?_
    · rcases r with _ | ⟨r, rest⟩
      · simp [OProg.queries]
      · refine (length_queries_bind_le H _ _ 0 fun r' => ?_).trans ?_
        · rcases r' with _ | ⟨rs, rest'⟩ <;> simp [OProg.queries]
        · simpa using queries_openAll H ci hci ps rest
    · simp only [List.length_cons]
      nlinarith

/-- The compiled run's query bound. -/
theorem queries_run_le (H : ByteArray → Digest) {lv : ℕ} {p : VerifierProgram Bool} {n : ℕ}
    (hp : S.QB lv p n) : ∀ (st : Digest) (buf : Bytes) (caps : List CapI) (body : Bytes),
    (∀ ci ∈ caps, ci.ht - ci.lv ≤ lv) → ((S.run p st buf caps body).queries H).length ≤ n := by
  induction hp with
  | ret b n => intros; simp [run, OProg.queries]
  | fail n => intros; simp [run, OProg.queries]
  | grind bits k n => intros; simp [run, OProg.queries]
  | read k n _ ih =>
    intro st buf caps body hcaps
    simp only [run]
    split_ifs
    · simp [OProg.queries]
    · exact ih _ _ _ _ _ hcaps
  | sample k n _ ih =>
    intro st buf caps body hcaps
    simp only [run]
    split_ifs
    · simp only [OProg.queries, List.length_cons]
      have := ih (S.chal (H (toQ (st.toList ++ buf)))) (H (toQ (st.toList ++ buf))) [] caps body
        hcaps
      omega
    · simp [OProg.queries]
  | commit ht w k n hlv _ ih =>
    intro st buf caps body hcaps
    simp only [run]
    split_ifs
    · simp [OProg.queries]
    · refine ih _ _ _ _ fun ci hci => ?_
      rcases List.mem_append.mp hci with hci | hci
      · exact hcaps ci hci
      · rw [List.mem_singleton.mp hci]; exact hlv
  | query i ps k n _ ih =>
    intro st buf caps body hcaps
    simp only [run]
    split
    · simp [OProg.queries]
    · rename_i ci hi
      have h1 := S.queries_openAll H ci (hcaps ci (List.mem_of_getElem? hi)) ps body
      refine (length_queries_bind_le H _ _ n fun r => ?_).trans (by omega)
      rcases r with _ | ⟨rows, rest⟩
      · simp [OProg.queries]
      · exact ih rows st buf caps rest hcaps

/-- **The compiled verifier's query bound.** -/
theorem queries_V_le {lv n : ℕ} (hP : ∀ x, S.QB lv (S.P x) n) (H : ByteArray → Digest) (c : Digest)
    (π : Proof) : ((S.V c π).queries H).length ≤ 2 + n := by
  unfold V
  split
  · simp [OProg.queries]
  · rename_i x body _
    split_ifs
    · simp only [OProg.queries, List.length_cons]
      have := S.queries_run_le H (hP x) (H (S.seedQ (H (toQ S.q0)) x)) [] [] body (by simp)
      omega
    · simp [OProg.queries]

end Scheme

end Lvm.FS
