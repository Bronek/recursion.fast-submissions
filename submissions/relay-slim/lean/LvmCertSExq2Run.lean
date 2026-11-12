-- lvm2 X-REC2 (helper XA). The O5c bridge's replay (`LvmCertSExqRun`, WP-14d) extended through a
-- commitment and an opening, for `C_rec`'s second WHIR level (lvm2 S4): v1's `simK`/`trun_simK`/
-- `simK_chain` covered reads and samples only; here also a `commit` (level 1's cap) and, as a
-- separate step, a `query` (level 0's opening), so that the chain's targets through `α₁` are
-- `trun`'s Fiat–Shamir queries.
import LvmCertSExqRun

/-!
# The replay through a commitment and an opening

* `K2`: the kinds `read`, `sample` and `commit ht w nb` (a cap of `nb` bytes); `KM e k`: the event
  `e` has the kind `k`;
* `simK2 S L B ks off pend st`: the history and the final state the replay produces on the kinds
  `ks` (a commit: the commitment's word read by `wordOf` under the cap at `B[off, …)`, the body
  advances by `nb` bytes, which stay pending, as in `LvmDriver.driveItems`);
* **`trun_simK2`**: `trun` along a history of these kinds is `simK2`'s history, the program after it
  is `p.after pre`, and `trun` continues from the slices `offK2`, `pendK2` with the caps `capsK2`;
* **`trun_query`**: one opening of `ps` positions of the commitment `ci`: the body advances by
  `|ps| · (8·wd + 32·(ht − lv))` bytes, which no query absorbs (the pending bytes are kept, so an
  opening right after a sample leaves nothing pending: `driveItems`'s `pend := off`);
* **`simK2_chain`**: `simK2`'s samples are the first-match chain's answers when the chain's targets
  absorb `fsPreK2`'s slices (WP-13a's `fsPre`);
* **`openRec_P20`**: at P20 (S2J, `g = 14`), `fsPreK2` over the kinds of the middle phases and
  `C_rec`'s opening (level 0's head; level 1's cap, level 0's proof of work, positions and `λ`; then,
  after the opening, level 1's intro and fold rounds) is the chain's messages `fsMsgs` of positions
  2–1302, 1303–1327 and 1328–1331, and the offsets are `LvmXLayout`'s.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-- The kinds of the replayed events: a read, a sample, a commitment of shape `(ht, w)` whose cap
is `nb` bytes. -/
inductive K2 where
  | read
  | sample
  | commit (ht w nb : ℕ)
  deriving DecidableEq, Repr

/-- The event `e` has the kind `k`. -/
def KM : Ev → K2 → Prop
  | .read _, .read => True
  | .sample _, .sample => True
  | .commit ht w _, .commit ht' w' _ => ht = ht' ∧ w = w'
  | _, _ => False

section Sim

variable (S : Scheme) (L : Log) (B : List UInt8)

/-- **The replay on kinds** (reads, samples, commitments): the history and the final state. -/
def simK2 : List K2 → ℕ → ℕ → Digest → Option (List Ev × Digest)
  | [], _, _, st => some ([], st)
  | .read :: ks, off, pend, st =>
    (simK2 ks (off + 24) pend st).map fun r => (.read (S.decE (sl B off 24)) :: r.1, r.2)
  | .sample :: ks, off, pend, st =>
    (L.find? fun e => e.1 = toQ (st.toList ++ sl B pend (off - pend))).bind fun e =>
      (simK2 ks off off e.2).map fun r => (.sample (S.chal e.2) :: r.1, r.2)
  | .commit ht w nb :: ks, off, pend, st =>
    (simK2 ks (off + nb) pend st).map fun r =>
      (.commit ht w (S.wordOf L (S.capI ht w (B.drop off))) :: r.1, r.2)

/-- The commitments' records the replay appends. -/
def capsK2 : List K2 → ℕ → List CapI → List CapI
  | [], _, caps => caps
  | .read :: ks, off, caps => capsK2 ks (off + 24) caps
  | .sample :: ks, off, caps => capsK2 ks off caps
  | .commit ht w nb :: ks, off, caps => capsK2 ks (off + nb) (caps ++ [S.capI ht w (B.drop off)])

end Sim

/-- The body offset after the kinds. -/
def offK2 : List K2 → ℕ → ℕ
  | [], off => off
  | .read :: ks, off => offK2 ks (off + 24)
  | .sample :: ks, off => offK2 ks off
  | .commit _ _ nb :: ks, off => offK2 ks (off + nb)

/-- The first pending byte after the kinds. -/
def pendK2 : List K2 → ℕ → ℕ → ℕ
  | [], _, pend => pend
  | .read :: ks, off, pend => pendK2 ks (off + 24) pend
  | .sample :: ks, off, _ => pendK2 ks off off
  | .commit _ _ nb :: ks, off, pend => pendK2 ks (off + nb) pend

/-- The slices the samples absorb (WP-13a's `fsPre`; a cap stays pending). -/
def fsPreK2 : List K2 → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | .read :: ks, off, pend => fsPreK2 ks (off + 24) pend
  | .sample :: ks, off, pend => (pend, off - pend) :: fsPreK2 ks off off
  | .commit _ _ nb :: ks, off, pend => fsPreK2 ks (off + nb) pend

/-! ## The replay is `simK2`, and the program follows the history -/

theorem after_nil {α : Type} (p : VerifierProgram α) : p.after [] = some p := by cases p <;> rfl

theorem forall₂_cons_inv {e : Ev} {pre : List Ev} {k : K2} {ks : List K2}
    (h : List.Forall₂ KM (e :: pre) (k :: ks)) : KM e k ∧ List.Forall₂ KM pre ks := by
  cases h with
  | cons a b => exact ⟨a, b⟩

/-- **The replay along reads, samples and commitments** (`trun` from a state whose pending bytes and
body are slices of `B`): its history is `simK2`'s, the program after it is `p.after pre`. -/
theorem trun_simK2 (S : Scheme) (L : Log) (B : List UInt8) : ∀ (ks : List K2)
    (p : VerifierProgram Bool) (off pend : ℕ) (st : Digest) (caps : List CapI)
    (h pre post : List Ev) (b : Bool),
    (∀ ht w nb, K2.commit ht w nb ∈ ks → S.capBytes ht w = nb) → pend ≤ off →
    List.Forall₂ KM pre ks →
    S.trun L p st (sl B pend (off - pend)) caps (B.drop off) h = some (b, h ++ pre ++ post) →
    ∃ st' p', simK2 S L B ks off pend st = some (pre, st') ∧ p.after pre = some p' ∧
      pendK2 ks off pend ≤ offK2 ks off ∧
      S.trun L p' st' (sl B (pendK2 ks off pend) (offK2 ks off - pendK2 ks off pend))
        (capsK2 S B ks off caps) (B.drop (offK2 ks off)) (h ++ pre) = some (b, h ++ pre ++ post) := by
  intro ks
  induction ks with
  | nil =>
    intro p off pend st caps h pre post b _ hle hk e
    have : pre = [] := by cases hk; rfl
    subst this
    exact ⟨st, p, rfl, after_nil p, hle, by simpa [pendK2, offK2, capsK2] using e⟩
  | cons k ks ih =>
    intro p off pend st caps h pre post b hcb hle hk e
    obtain ⟨e₀, pre', rfl⟩ : ∃ e₀ pre', pre = e₀ :: pre' := by
      cases hk with
      | cons a b => exact ⟨_, _, rfl⟩
    obtain ⟨hk0, hks⟩ := forall₂_cons_inv hk
    have hcb' : ∀ ht w nb, K2.commit ht w nb ∈ ks → S.capBytes ht w = nb :=
      fun ht w nb hm => hcb ht w nb (List.mem_cons_of_mem _ hm)
    have hcon : ∀ b', some (b', h) ≠ some (b, h ++ (e₀ :: pre') ++ post) := fun b' he => by
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      have := congrArg List.length he.2
      simp at this
    cases p with
    | ret a => exact absurd e (hcon _)
    | fail => exact absurd e (hcon _)
    | grind _ _ => exact absurd e (hcon _)
    | read k' =>
      simp only [Scheme.trun] at e
      split_ifs at e with hlen
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      cases k with
      | sample => exact absurd hk0 (by simp [KM])
      | commit _ _ _ => exact absurd hk0 (by simp [KM])
      | read =>
        rw [sl_append B hle, drop_drop'] at e
        obtain ⟨st', p', hs, ha, hle', ht⟩ := ih _ (off + 24) pend st caps
          (h ++ [Ev.read (S.decE ((B.drop off).take 24))]) pre' post b hcb' (by omega) hks
          (by rw [e]; simp)
        refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2, offK2, capsK2] using ht⟩
        · simp only [simK2, hs, Option.map_some]
          rfl
        · simp only [VerifierProgram.after]
          exact ha
    | sample k' =>
      simp only [Scheme.trun] at e
      split_ifs at e with hq
      · cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
        | none => rw [hfd] at e; simp at e
        | some e' =>
          rw [hfd, Option.bind_some] at e
          have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
          have he0 := head_of_prefix hpre
          subst he0
          cases k with
          | read => exact absurd hk0 (by simp [KM])
          | commit _ _ _ => exact absurd hk0 (by simp [KM])
          | sample =>
            have e2 : S.trun L (k' (S.chal e'.2)) e'.2 (sl B off (off - off)) caps (B.drop off)
                (h ++ [Ev.sample (S.chal e'.2)]) =
                some (b, h ++ [Ev.sample (S.chal e'.2)] ++ pre' ++ post) := by
              simpa [sl] using e
            obtain ⟨st', p', hs, ha, hle', ht⟩ := ih _ off off e'.2 caps _ pre' post b hcb'
              le_rfl hks e2
            refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2, offK2, capsK2] using ht⟩
            · simp only [simK2, hfd, Option.bind_some, hs, Option.map_some]
            · simp only [VerifierProgram.after]
              exact ha
      · exact absurd e (hcon _)
    | commit ht w k' =>
      simp only [Scheme.trun] at e
      split_ifs at e
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      cases k with
      | read => exact absurd hk0 (by simp [KM])
      | sample => exact absurd hk0 (by simp [KM])
      | commit ht' w' nb =>
        obtain ⟨rfl, rfl⟩ := hk0
        have hnb : S.capBytes ht w = nb := hcb ht w nb List.mem_cons_self
        rw [hnb, sl_append B hle, drop_drop'] at e
        obtain ⟨st', p', hs, ha, hle', ht'⟩ := ih k' (off + nb) pend st
          (caps ++ [S.capI ht w (B.drop off)])
          (h ++ [Ev.commit ht w (S.wordOf L (S.capI ht w (B.drop off)))]) pre' post b hcb'
          (by omega) hks (by rw [e]; simp)
        refine ⟨st', p', ?_, ?_, hle', by simpa [pendK2, offK2, capsK2] using ht'⟩
        · simp only [simK2, hs, Option.map_some]
        · simp only [VerifierProgram.after, and_self, ite_true]
          exact ha
    | query i ps k' =>
      simp only [Scheme.trun] at e
      cases hc : caps[i]? with
      | none => rw [hc] at e; exact absurd e (hcon _)
      | some ci =>
        rw [hc] at e
        simp only at e
        cases ho : (S.openAll ci ps (B.drop off)).runLog L with
        | none => rw [ho] at e; simp at e
        | some o =>
          rw [ho, Option.bind_some] at e
          rcases o with _ | ⟨rows, rest⟩
          · exact absurd e (hcon _)
          · have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
            have he0 := head_of_prefix hpre
            subst he0
            cases k <;> simp [KM] at hk0

/-! ## One opening -/

/-- The bytes one position of the commitment `ci` takes from the body: the row and the siblings. -/
def posBytes (ci : CapI) : ℕ := 8 * ci.wd + 32 * (ci.ht - ci.lv)

theorem climb_rest (S : Scheme) (L : Log) : ∀ (n : ℕ) (d : Digest) (q : ℕ) (body rest : Bytes)
    (top : Digest), (Scheme.climb n d q body).runLog L = some (some (top, rest)) →
    32 * n ≤ body.length ∧ rest = body.drop (32 * n)
  | 0, d, q, body, rest, top, h => by
    simp only [Scheme.climb, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by omega, by rw [← h.2]; rfl⟩
  | n + 1, d, q, body, rest, top, h => by
    unfold Scheme.climb at h
    by_cases hb : body.length < 32
    · rw [if_pos hb] at h; simp [OProg.runLog] at h
    · rw [if_neg hb] at h
      simp only [OProg.runLog] at h
      cases hf : L.find? _ with
      | none => rw [hf] at h; simp at h
      | some e =>
        rw [hf, Option.bind_some] at h
        obtain ⟨h1, h2⟩ := climb_rest S L n _ _ _ _ _ h
        simp only [List.length_drop] at h1
        refine ⟨by omega, by rw [h2, List.drop_drop]; congr 1; ring⟩

theorem openOne_rest (S : Scheme) (L : Log) (ci : CapI) (q : ℕ) (body rest : Bytes) (row : List K)
    (h : (S.openOne ci q body).runLog L = some (some (row, rest))) :
    posBytes ci ≤ body.length ∧ rest = body.drop (posBytes ci) := by
  unfold Scheme.openOne at h
  split_ifs at h with hb
  · simp [OProg.runLog] at h
  · simp only [OProg.runLog] at h
    cases hf : L.find? _ with
    | none => rw [hf] at h; simp at h
    | some e =>
      rw [hf, Option.bind_some, OProgFacts.runLog_bind] at h
      cases hc : (Scheme.climb (ci.ht - ci.lv) e.2 (q % 2 ^ ci.ht) (body.drop (8 * ci.wd))).runLog L with
      | none => rw [hc] at h; simp at h
      | some o =>
        rw [hc, Option.bind_some] at h
        rcases o with _ | ⟨top, rest'⟩
        · simp [OProg.runLog] at h
        · simp only [OProg.runLog] at h
          split_ifs at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := climb_rest S L _ _ _ _ _ _ hc
            simp only [List.length_drop] at h1
            refine ⟨by unfold posBytes; omega, ?_⟩
            rw [← h.2, h2, List.drop_drop]
            unfold posBytes
            congr 1
          · simp at h

theorem openAll_rest (S : Scheme) (L : Log) (ci : CapI) : ∀ (ps : List ℕ) (body rest : Bytes)
    (rows : List (List K)), (S.openAll ci ps body).runLog L = some (some (rows, rest)) →
    ps.length * posBytes ci ≤ body.length ∧ rest = body.drop (ps.length * posBytes ci)
  | [], body, rest, rows, h => by
    simp only [Scheme.openAll, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by simp, by rw [← h.2]; simp⟩
  | p :: ps, body, rest, rows, h => by
    simp only [Scheme.openAll, OProgFacts.runLog_bind] at h
    cases h1 : (S.openOne ci p body).runLog L with
    | none => rw [h1] at h; simp at h
    | some o =>
      rw [h1, Option.bind_some] at h
      rcases o with _ | ⟨r, rest₁⟩
      · simp [OProg.runLog] at h
      · simp only [OProgFacts.runLog_bind] at h
        cases h2 : (S.openAll ci ps rest₁).runLog L with
        | none => rw [h2] at h; simp at h
        | some o' =>
          rw [h2, Option.bind_some] at h
          rcases o' with _ | ⟨rs, rest₂⟩
          · simp [OProg.runLog] at h
          · simp only [OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨a1, a2⟩ := openOne_rest S L ci p body rest₁ r h1
            obtain ⟨b1, b2⟩ := openAll_rest S L ci ps rest₁ rest₂ rs h2
            rw [a2, List.length_drop] at b1
            rw [a2, List.drop_drop] at b2
            simp only [List.length_cons]
            refine ⟨by rw [Nat.succ_mul]; omega, by rw [← h.2, b2]; congr 1; ring⟩

/-- **One opening** of `ps` positions of the commitment `caps[i]`: the event is `query rows`, the
body advances by `|ps| · posBytes ci`, the state and the pending bytes are kept. -/
theorem trun_query (S : Scheme) (L : Log) {i : ℕ} {ps : List ℕ}
    {k : List (List K) → VerifierProgram Bool} {st : Digest} {buf : Bytes} {caps : List CapI}
    {body : Bytes} {h : List Ev} {b : Bool} {e : Ev} {post : List Ev} {ci : CapI}
    (hc : caps[i]? = some ci)
    (ht : S.trun L (.query i ps k) st buf caps body h = some (b, h ++ e :: post)) :
    ∃ rows, e = .query rows ∧ (VerifierProgram.query i ps k).after [e] = some (k rows) ∧
      ps.length * posBytes ci ≤ body.length ∧
      S.trun L (k rows) st buf caps (body.drop (ps.length * posBytes ci)) (h ++ [e]) =
        some (b, h ++ e :: post) := by
  have hcon : ∀ b', some (b', h) ≠ some (b, h ++ e :: post) := fun b' he => by
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    have := congrArg List.length he.2
    simp at this
  simp only [Scheme.trun, hc] at ht
  cases ho : (S.openAll ci ps body).runLog L with
  | none => rw [ho] at ht; simp at ht
  | some o =>
    rw [ho, Option.bind_some] at ht
    rcases o with _ | ⟨rows, rest⟩
    · exact absurd ht (hcon _)
    · have hpre := trun_prefix S L _ _ _ _ _ _ _ _ ht
      have he0 : Ev.query rows = e := by
        have := head_of_prefix (h := h) (l := post) (post := []) (by simpa using hpre)
        exact this
      subst he0
      obtain ⟨h1, h2⟩ := openAll_rest S L ci ps body rest rows ho
      exact ⟨rows, rfl, by simp only [VerifierProgram.after], h1,
        by rw [← h2]; exact ht⟩

/-! ## `simK2`'s samples are the first-match chain -/

/-- **The chain** (v1's `simK_chain` through commitments): `simK2`'s samples are the challenges of
`fmAns T` from position `j + 1` on, when the chain's targets absorb the slices `fsPreK2`. -/
theorem simK2_chain (S : Scheme) (L : Log) (B : List UInt8) (T : ℕ → Digest → ByteArray)
    (st₀ : Digest) : ∀ (ks : List K2) (off pend : ℕ) (st : Digest) (j : ℕ) (pre : List Ev)
    (st' : Digest), simK2 S L B ks off pend st = some (pre, st') →
    Lvm.X.fmAns T st₀ L j = some st →
    (∀ i (hi : i < (fsPreK2 ks off pend).length) (s : Digest),
      T (j + 1 + i) s = toQ (s.toList ++ sl B ((fsPreK2 ks off pend)[i]).1 ((fsPreK2 ks off pend)[i]).2)) →
    (∀ i (hi : i < (pre.filterMap smpOf).length), ∃ a,
      Lvm.X.fmAns T st₀ L (j + 1 + i) = some a ∧ (pre.filterMap smpOf)[i] = S.chal a) ∧
    Lvm.X.fmAns T st₀ L (j + (pre.filterMap smpOf).length) = some st' := by
  intro ks
  induction ks with
  | nil =>
    intro off pend st j pre st' hs hj _
    simp only [simK2, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨fun i hi => by simp at hi, by simpa using hj⟩
  | cons k ks ih =>
    intro off pend st j pre st' hs hj hT
    cases k with
    | read =>
      simp only [simK2] at hs
      cases hr : simK2 S L B ks (off + 24) pend st with
      | none => rw [hr] at hs; simp at hs
      | some r =>
        obtain ⟨pre₁, st₁⟩ := r
        rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ih (off + 24) pend st j pre₁ st₁ hr hj (fun i hi s => hT i hi s)
    | commit ht w nb =>
      simp only [simK2] at hs
      cases hr : simK2 S L B ks (off + nb) pend st with
      | none => rw [hr] at hs; simp at hs
      | some r =>
        obtain ⟨pre₁, st₁⟩ := r
        rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ih (off + nb) pend st j pre₁ st₁ hr hj (fun i hi s => hT i hi s)
    | sample =>
      simp only [simK2] at hs
      cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
      | none => rw [hfd] at hs; simp at hs
      | some e =>
        rw [hfd, Option.bind_some] at hs
        cases hr : simK2 S L B ks off off e.2 with
        | none => rw [hr] at hs; simp at hs
        | some r =>
          obtain ⟨pre₁, st₁⟩ := r
          rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          have hT0 := hT 0 (by simp [fsPreK2]) st
          simp only [fsPreK2, List.getElem_cons_zero, add_zero] at hT0
          have hj1 : Lvm.X.fmAns T st₀ L (j + 1) = some e.2 := by
            simp only [Lvm.X.fmAns, hj, Option.bind_some, hT0, hfd, Option.map_some]
          obtain ⟨h1, h2⟩ := ih off off e.2 (j + 1) pre₁ st₁ hr hj1 (fun i hi s => by
            have := hT (i + 1) (by simp [fsPreK2]; omega) s
            simp only [fsPreK2, List.getElem_cons_succ] at this
            rw [show j + 1 + 1 + i = j + 1 + (i + 1) by omega]
            exact this)
          refine ⟨fun i hi => ?_, ?_⟩
          · rcases i with _ | i
            · exact ⟨e.2, by simpa using hj1, by simp [smpOf]⟩
            · simp only [List.filterMap_cons, smpOf, List.length_cons] at hi
              obtain ⟨a, ha, he⟩ := h1 i (by omega)
              refine ⟨a, by rw [show j + 1 + (i + 1) = j + 1 + 1 + i by omega]; exact ha, ?_⟩
              simpa [smpOf] using he
          · simp only [List.filterMap_cons, smpOf, List.length_cons]
            rw [show j + (List.length (List.filterMap smpOf pre₁) + 1) =
              j + 1 + (List.filterMap smpOf pre₁).length by omega]
            exact h2

/-! ## The schedule's view of `C_rec`'s opening (P20, by evaluation) -/

/-- The kinds of items without openings (`driveItems`: a cap of `2^c` nodes is a commitment of
`32 · 2^c` bytes, a positions item `nPosQ` samples). -/
def itemK2 (p : Params) (sh : Ref → ℕ × ℕ) : List Item → List K2
  | [] => []
  | .read m :: its => List.replicate m .read ++ itemK2 p sh its
  | .sample :: its => .sample :: itemK2 p sh its
  | .cap c r :: its => .commit (sh r).1 (sh r).2 (nodeBytes * 2 ^ c) :: itemK2 p sh its
  | .positions r :: its => List.replicate (p.level r).nPosQ .sample ++ itemK2 p sh its
  | .opening _ :: its => itemK2 p sh its

/-- `C_rec`'s commitment shapes `(ht, w)` (level 1: `2^12` rows of `3 · 2^4` words). -/
def shRec : Ref → ℕ × ℕ
  | ⟨.crec, 1⟩ => (12, 48)
  | ⟨.crec, _⟩ => (15, 64)
  | ⟨.main, _⟩ => (21, 64)

/-- `C_rec`'s opening up to level 0's residual's place: `ρ`, the intro round, six fold rounds. -/
def recHead1 : List Item := ((phases P20).getD 7 default).2.take 14

/-- Then level 1's cap, level 0's proof of work (separator, nonce, PoW challenge; S2J), positions
and `λ`. -/
def recHead2 : List Item := (((phases P20).getD 7 default).2.drop 14).take 6

/-- After level 0's opening: the intro round and level 1's four fold rounds. -/
def recHeadB : List Item := (((phases P20).getD 7 default).2.drop 21).take 9

/-- **The chain's targets through `α₁` are the replay's FS queries** (P20 on S2J, `g = 14`; one kernel
evaluation, re-decided at every freeze). From the roots' end (body at `17912`, pending from `5624`):
the middle phases and `C_rec`'s head (segment A1) absorb the chain's messages of positions 2–1302 and
end at level 1's cap (`capRec1Off = 205280`); the cap, level 0's proof of work, positions and `λ` (A2)
those of positions 1303–1327; after level 0's opening of `170 × (512 + 32 · 8)` bytes (body at
`339960`, nothing pending), level 1's intro and fold rounds (B) those of positions 1328–1331, ending
at `f2Off`. The segments' kinds. -/
theorem openRec_P20 :
    fsPreK2 (itemK2 P20 shRec (midItems ++ recHead1)) 17912 5624 =
        ((Lvm.X.fsMsgs P20).drop 1).take 1301 ∧
    offK2 (itemK2 P20 shRec (midItems ++ recHead1)) 17912 = 205280 ∧
    pendK2 (itemK2 P20 shRec (midItems ++ recHead1)) 17912 5624 = 205232 ∧
    fsPreK2 (itemK2 P20 shRec recHead2) 205280 205232 = ((Lvm.X.fsMsgs P20).drop 1302).take 25 ∧
    offK2 (itemK2 P20 shRec recHead2) 205280 = 209400 ∧
    pendK2 (itemK2 P20 shRec recHead2) 205280 205232 = 209400 ∧
    209400 + 170 * (8 * 64 + 32 * (15 - 7)) = 339960 ∧
    fsPreK2 (itemK2 P20 shRec recHeadB) 339960 339960 = ((Lvm.X.fsMsgs P20).drop 1327).take 4 ∧
    offK2 (itemK2 P20 shRec recHeadB) 339960 = Lvm.X.f2Off P20 ∧
    pendK2 (itemK2 P20 shRec recHeadB) 339960 339960 = 340152 ∧
    Lvm.X.capRec1Off P20 = 205280 ∧ Lvm.X.f2Off P20 = 340200 ∧
    ((phases P20).getD 7 default).2.getD 20 default = .opening ⟨.crec, 0⟩ ∧
    (itemKinds midItems).count .sample = 1294 ∧ RSItems midItems = true ∧
    itemK2 P20 shRec recHead1 =
      [.sample, .read, .read, .sample, .read, .read, .sample, .read, .read, .sample, .read, .read,
        .sample, .read, .read, .sample, .read, .read, .sample, .read, .read] ∧
    itemK2 P20 shRec recHead2 = .commit 12 48 4096 :: .sample :: .read :: List.replicate 24 .sample ∧
    itemK2 P20 shRec recHeadB =
      [.read, .read, .sample, .read, .read, .sample, .read, .read, .sample, .read, .read, .sample,
        .read, .read] ∧
    (Lvm.X.fsMsgs P20).getD 0 (0, 0) = (8, 5616) := by
  decide +kernel

/-! ## Kinds -/

/-- v1's kinds (reads and samples) as `K2`. -/
def toK2 : EvK → K2
  | .read => .read
  | .sample => .sample
  | .other => .read

theorem itemK2_append (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (a b : List Item),
    itemK2 p sh (a ++ b) = itemK2 p sh a ++ itemK2 p sh b
  | [], _ => rfl
  | .read m :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b, List.append_assoc]
  | .sample :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b]
  | .cap _ _ :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b]
  | .positions _ :: a, b => by
    simp only [List.cons_append, itemK2, itemK2_append p sh a b, List.append_assoc]
  | .opening _ :: a, b => by simp only [List.cons_append, itemK2, itemK2_append p sh a b]

/-- On items of reads and samples, `itemK2` is v1's `itemKinds`. -/
theorem itemK2_rs (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item), RSItems its = true →
    itemK2 p sh its = (itemKinds its).map toK2
  | [], _ => rfl
  | .read m :: its, h => by
    rw [itemK2, itemKinds, itemK2_rs p sh its h, List.map_append, List.map_replicate]; rfl
  | .sample :: its, h => by rw [itemK2, itemKinds, itemK2_rs p sh its h]; rfl
  | .cap _ _ :: _, h => by simp [RSItems] at h
  | .positions _ :: _, h => by simp [RSItems] at h
  | .opening _ :: _, h => by simp [RSItems] at h

theorem forall₂_append {a b : List Ev} {c d : List K2} (h1 : List.Forall₂ KM a c)
    (h2 : List.Forall₂ KM b d) : List.Forall₂ KM (a ++ b) (c ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

/-- A history of v1's kinds (no `other`) has the kinds `toK2`. -/
theorem forall₂_of_kinds : ∀ (l : List Ev) (ks : List EvK), l.map kindOf = ks →
    EvK.other ∉ ks → List.Forall₂ KM l (ks.map toK2)
  | [], _, h, _ => by subst h; exact .nil
  | e :: l, ks, h, ho => by
    subst h
    simp only [List.map_cons, List.mem_cons, not_or] at ho ⊢
    refine .cons ?_ (forall₂_of_kinds l _ rfl ho.2)
    cases e <;> simp [kindOf, toK2, KM] at ho ⊢

/-- `simK2` appends to the caps. -/
theorem capsK2_prefix (S : Scheme) (B : List UInt8) : ∀ (ks : List K2) (off : ℕ) (caps : List CapI),
    ∃ l, capsK2 S B ks off caps = caps ++ l
  | [], _, caps => ⟨[], by simp [capsK2]⟩
  | .read :: ks, off, caps => capsK2_prefix S B ks _ caps
  | .sample :: ks, off, caps => capsK2_prefix S B ks _ caps
  | .commit ht w nb :: ks, off, caps => by
    obtain ⟨l, hl⟩ := capsK2_prefix S B ks (off + nb) (caps ++ [S.capI ht w (B.drop off)])
    exact ⟨_ :: l, by rw [capsK2, hl, List.append_assoc]; rfl⟩

theorem sl_zero (B : List UInt8) (a : ℕ) : sl B a 0 = [] := by simp [sl]

end Lvm.ASM
