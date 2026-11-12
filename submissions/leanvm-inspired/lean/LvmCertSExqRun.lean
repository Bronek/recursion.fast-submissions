-- WP-14d (EXQ). New for lvm (O5c bridge (a)): WP-5's replay `trun` along a run whose events have
-- known kinds (reads and samples), on a body that is a suffix of a byte string `B`: the history is
-- `simK` (each read the scalar of the next 24 bytes, each sample the challenge of the first log
-- entry for `state ‖ pending bytes`), and its samples are the first-match chain of WP-13a
-- (`fmAns`) whose targets absorb the slices `fsPreK` (WP-13a's `fsPre` on kinds).
import LvmCompile
import LvmCertSExqKinds
import LvmXChainL

/-!
# The replay along known kinds

* `simK S L B ks off pend st`: the history and final state the replay produces on kinds `ks` with
  the body at byte `off` of `B` and the pending bytes `B[pend, off)`;
* **`trun_simK`**: if `trun` (from that state) returns a history `h ++ pre ++ post` with
  `pre.map kindOf = ks` (no `other`), then `pre` is `simK`'s and `trun` continues from `simK`'s state;
* **`simK_chain`**: `simK`'s samples are the challenges of the first-match chain `fmAns T` from
  position `j + 1` on, when the chain's targets `T (j + 1 + i)` absorb the slices
  `fsPreK ks off pend` (WP-13a's `fsPre`, `fsPre_eq_fsPreK`);
* `simK_reads`: a run of reads is the scalars of consecutive 24-byte slices.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-- The challenge of a sample event (`LvmCertSLuck.sampleOf`, restated here so that the replay
does not import the certificate's modules). -/
def smpOf : Ev → Option E
  | .sample c => some c
  | _ => none

/-- The slice `B[a, a + n)`. -/
def sl (B : List UInt8) (a n : ℕ) : List UInt8 := (B.drop a).take n

section Sim

variable (S : Scheme) (L : Log) (B : List UInt8)

/-- **The replay on kinds**: the history and the final state. -/
def simK : List EvK → ℕ → ℕ → Digest → Option (List Ev × Digest)
  | [], _, _, st => some ([], st)
  | .read :: ks, off, pend, st =>
    (simK ks (off + 24) pend st).map fun r => (.read (S.decE (sl B off 24)) :: r.1, r.2)
  | .sample :: ks, off, pend, st =>
    (L.find? fun e => e.1 = toQ (st.toList ++ sl B pend (off - pend))).bind fun e =>
      (simK ks off off e.2).map fun r => (.sample (S.chal e.2) :: r.1, r.2)
  | .other :: _, _, _, _ => none

/-- The body offset after the kinds. -/
def offK : List EvK → ℕ → ℕ
  | [], off => off
  | .read :: ks, off => offK ks (off + 24)
  | _ :: ks, off => offK ks off

/-- The first pending byte after the kinds. -/
def pendK : List EvK → ℕ → ℕ → ℕ
  | [], _, pend => pend
  | .read :: ks, off, pend => pendK ks (off + 24) pend
  | .sample :: ks, off, _ => pendK ks off off
  | .other :: ks, off, pend => pendK ks off pend

/-- The slices the samples absorb (WP-13a's `fsPre` on kinds). -/
def fsPreK : List EvK → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | .read :: ks, off, pend => fsPreK ks (off + 24) pend
  | .sample :: ks, off, pend => (pend, off - pend) :: fsPreK ks off off
  | .other :: ks, off, pend => fsPreK ks off pend

end Sim

/-! ## `trun` keeps its history's prefix -/

theorem trun_prefix (S : Scheme) (L : Log) : ∀ (p : VerifierProgram Bool) (st : Digest) (buf : Bytes)
    (caps : List CapI) (body : Bytes) (h : List Ev) (b : Bool) (hf : List Ev),
    S.trun L p st buf caps body h = some (b, hf) → h <+: hf := by
  intro p
  induction p with
  | ret a => intro st buf caps body h b hf e; simp only [Scheme.trun, Option.some.injEq,
      Prod.mk.injEq] at e; rw [← e.2]
  | fail => intro st buf caps body h b hf e; simp only [Scheme.trun, Option.some.injEq,
      Prod.mk.injEq] at e; rw [← e.2]
  | grind _ _ _ => intro st buf caps body h b hf e; simp only [Scheme.trun, Option.some.injEq,
      Prod.mk.injEq] at e; rw [← e.2]
  | read k ih =>
    intro st buf caps body h b hf e
    simp only [Scheme.trun] at e
    split_ifs at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
    · exact (List.prefix_append _ _).trans (ih _ _ _ _ _ _ _ _ e)
  | sample k ih =>
    intro st buf caps body h b hf e
    simp only [Scheme.trun] at e
    split_ifs at e
    · cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ buf))) with
      | none => rw [hfd] at e; simp at e
      | some e' =>
        rw [hfd, Option.bind_some] at e
        exact (List.prefix_append _ _).trans (ih _ _ _ _ _ _ _ _ e)
    · simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
  | commit ht w k ih =>
    intro st buf caps body h b hf e
    simp only [Scheme.trun] at e
    split_ifs at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
    · exact (List.prefix_append _ _).trans (ih _ _ _ _ _ _ _ e)
  | query i ps k ih =>
    intro st buf caps body h b hf e
    simp only [Scheme.trun] at e
    cases hc : caps[i]? with
    | none => rw [hc] at e; simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
    | some ci =>
      rw [hc] at e
      simp only at e
      cases ho : (S.openAll ci ps body).runLog L with
      | none => rw [ho] at e; simp at e
      | some o =>
        rw [ho, Option.bind_some] at e
        rcases o with _ | ⟨rows, rest⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]
        · exact (List.prefix_append _ _).trans (ih _ _ _ _ _ _ _ _ e)

theorem not_self_append {h l : List Ev} (e : Ev) (hh : h = h ++ e :: l) : False := by
  have := congrArg List.length hh
  simp at this

theorem head_of_prefix {h l post : List Ev} {e e₀ : Ev} (hp : h ++ [e] <+: h ++ e₀ :: l ++ post) :
    e = e₀ := by
  simpa using hp

/-! ## The replay is `simK` -/

theorem sl_append (B : List UInt8) {pend off : ℕ} (h1 : pend ≤ off) (n : ℕ) :
    sl B pend (off - pend) ++ (B.drop off).take n = sl B pend (off + n - pend) := by
  unfold sl
  rw [show off + n - pend = (off - pend) + n by omega, List.take_add, List.drop_drop,
    show pend + (off - pend) = off by omega]

theorem drop_drop' (B : List UInt8) (a n : ℕ) : (B.drop a).drop n = B.drop (a + n) := by
  rw [List.drop_drop]

/-- **The replay along known kinds** (`trun` from a state whose pending bytes and body are slices
of `B`). -/
theorem trun_simK (S : Scheme) (L : Log) (B : List UInt8) : ∀ (ks : List EvK)
    (p : VerifierProgram Bool) (off pend : ℕ) (st : Digest) (caps : List CapI)
    (h pre post : List Ev) (b : Bool),
    EvK.other ∉ ks → pend ≤ off → pre.map kindOf = ks →
    S.trun L p st (sl B pend (off - pend)) caps (B.drop off) h = some (b, h ++ pre ++ post) →
    ∃ st' p' caps', simK S L B ks off pend st = some (pre, st') ∧
      pendK ks off pend ≤ offK ks off ∧
      S.trun L p' st' (sl B (pendK ks off pend) (offK ks off - pendK ks off pend)) caps'
        (B.drop (offK ks off)) (h ++ pre) = some (b, h ++ pre ++ post) := by
  intro ks
  induction ks with
  | nil =>
    intro p off pend st caps h pre post b _ hle hk e
    have : pre = [] := List.map_eq_nil_iff.1 hk
    subst this
    exact ⟨st, p, caps, rfl, hle, by simpa [pendK, offK] using e⟩
  | cons k ks ih =>
    intro p off pend st caps h pre post b hno hle hk e
    obtain ⟨e₀, pre', rfl, hk0, hks⟩ : ∃ e₀ pre', pre = e₀ :: pre' ∧ kindOf e₀ = k ∧
        pre'.map kindOf = ks := by
      rcases pre with _ | ⟨e₀, pre'⟩
      · simp at hk
      · simp only [List.map_cons, List.cons.injEq] at hk
        exact ⟨e₀, pre', rfl, hk.1, hk.2⟩
    have hno' : EvK.other ∉ ks := fun hm => hno (List.mem_cons_of_mem _ hm)
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
      simp only [kindOf] at hk0
      subst hk0
      have hl : off + 24 ≤ B.length := by simp at hlen; omega
      rw [sl_append B hle, drop_drop'] at e
      obtain ⟨st', p', caps', hs, hle', ht⟩ := ih _ (off + 24) pend st caps
        (h ++ [Ev.read (S.decE ((B.drop off).take 24))]) pre' post b hno' (by omega) hks
        (by rw [e]; simp)
      refine ⟨st', p', caps', ?_, hle', by simpa [pendK, offK] using ht⟩
      simp only [simK, hs, Option.map_some]
      rfl
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
          simp only [kindOf] at hk0
          subst hk0
          have e2 : S.trun L (k' (S.chal e'.2)) e'.2 (sl B off (off - off)) caps (B.drop off)
              (h ++ [Ev.sample (S.chal e'.2)]) = some (b, h ++ [Ev.sample (S.chal e'.2)] ++ pre' ++ post) := by
            simpa [sl] using e
          obtain ⟨st', p', caps', hs, hle', ht⟩ := ih _ off off e'.2 caps _ pre' post b hno'
            le_rfl hks e2
          refine ⟨st', p', caps', ?_, hle', by simpa [pendK, offK] using ht⟩
          simp only [simK, hfd, Option.bind_some, hs, Option.map_some]
      · exact absurd e (hcon _)
    | commit ht w k' =>
      simp only [Scheme.trun] at e
      split_ifs at e
      · exact absurd e (hcon _)
      have hpre := trun_prefix S L _ _ _ _ _ _ _ _ e
      have he0 := head_of_prefix hpre
      subst he0
      simp only [kindOf] at hk0
      exact absurd (hk0 ▸ List.mem_cons_self) hno
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
            simp only [kindOf] at hk0
            exact absurd (hk0 ▸ List.mem_cons_self) hno

/-! ## `simK`'s samples are the first-match chain -/

/-- **The chain**: `simK`'s samples are the challenges of `fmAns T` from position `j + 1` on, when
the chain's targets absorb the slices `fsPreK`. -/
theorem simK_chain (S : Scheme) (L : Log) (B : List UInt8) (T : ℕ → Digest → ByteArray)
    (st₀ : Digest) : ∀ (ks : List EvK) (off pend : ℕ) (st : Digest) (j : ℕ) (pre : List Ev)
    (st' : Digest), simK S L B ks off pend st = some (pre, st') →
    Lvm.X.fmAns T st₀ L j = some st →
    (∀ i (hi : i < (fsPreK ks off pend).length) (s : Digest),
      T (j + 1 + i) s = toQ (s.toList ++ sl B ((fsPreK ks off pend)[i]).1 ((fsPreK ks off pend)[i]).2)) →
    (∀ i (hi : i < (pre.filterMap smpOf).length), ∃ a,
      Lvm.X.fmAns T st₀ L (j + 1 + i) = some a ∧ (pre.filterMap smpOf)[i] = S.chal a) ∧
    Lvm.X.fmAns T st₀ L (j + (pre.filterMap smpOf).length) = some st' := by
  intro ks
  induction ks with
  | nil =>
    intro off pend st j pre st' hs hj _
    simp only [simK, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨fun i hi => by simp at hi, by simpa using hj⟩
  | cons k ks ih =>
    intro off pend st j pre st' hs hj hT
    cases k with
    | read =>
      simp only [simK] at hs
      cases hr : simK S L B ks (off + 24) pend st with
      | none => rw [hr] at hs; simp at hs
      | some r =>
        obtain ⟨pre₁, st₁⟩ := r
        rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have := ih (off + 24) pend st j pre₁ st₁ hr hj (fun i hi s => hT i hi s)
        have e : (Ev.read (S.decE (sl B off 24)) :: pre₁).filterMap smpOf = pre₁.filterMap smpOf := rfl
        rw [e]
        exact this
    | sample =>
      simp only [simK] at hs
      cases hfd : L.find? (fun e => decide (e.1 = toQ (st.toList ++ sl B pend (off - pend)))) with
      | none => rw [hfd] at hs; simp at hs
      | some e =>
        rw [hfd, Option.bind_some] at hs
        cases hr : simK S L B ks off off e.2 with
        | none => rw [hr] at hs; simp at hs
        | some r =>
          obtain ⟨pre₁, st₁⟩ := r
          rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          have hT0 := hT 0 (by simp [fsPreK]) st
          simp only [fsPreK, List.getElem_cons_zero, add_zero] at hT0
          have hj1 : Lvm.X.fmAns T st₀ L (j + 1) = some e.2 := by
            simp only [Lvm.X.fmAns, hj, Option.bind_some, hT0, hfd, Option.map_some]
          obtain ⟨h1, h2⟩ := ih off off e.2 (j + 1) pre₁ st₁ hr hj1 (fun i hi s => by
            have := hT (i + 1) (by simp [fsPreK]; omega) s
            simp only [fsPreK, List.getElem_cons_succ] at this
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
    | other => simp [simK] at hs

/-! ## Runs of reads -/

theorem simK_reads (S : Scheme) (L : Log) (B : List UInt8) : ∀ (n off pend : ℕ) (st : Digest),
    simK S L B (List.replicate n .read) off pend st =
      some ((List.range n).map fun i => Ev.read (S.decE (sl B (off + 24 * i) 24)), st)
  | 0, off, pend, st => rfl
  | n + 1, off, pend, st => by
    rw [List.replicate_succ, simK, simK_reads S L B n (off + 24) pend st, Option.map_some,
      List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero]
    refine congrArg (fun l => some (_ :: l, st)) (List.map_congr_left fun i _ => ?_)
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show off + 24 + 24 * i = off + 24 * (i + 1) by ring]

theorem offK_reads : ∀ (n off : ℕ), offK (List.replicate n .read) off = off + 24 * n
  | 0, off => rfl
  | n + 1, off => by rw [List.replicate_succ, offK, offK_reads n]; ring

/-! ## Kinds of items -/

/-- Items of reads and samples only. -/
def RSItems : List Item → Bool
  | [] => true
  | .read _ :: its => RSItems its
  | .sample :: its => RSItems its
  | _ :: _ => false

theorem fsPreK_reads (ks : List EvK) : ∀ (m off pend : ℕ),
    fsPreK (List.replicate m .read ++ ks) off pend = fsPreK ks (off + 24 * m) pend
  | 0, off, pend => rfl
  | m + 1, off, pend => by
    rw [List.replicate_succ, List.cons_append, fsPreK, fsPreK_reads ks m]
    congr 1
    ring

/-- **WP-13a's `fsPre` is `fsPreK` on the kinds** (items of reads and samples). -/
theorem fsPre_eq_fsPreK (p : Params) : ∀ (its : List Item) (off pend : ℕ), RSItems its = true →
    Lvm.X.fsPre p its off pend = fsPreK (itemKinds its) off pend
  | [], _, _, _ => rfl
  | .read m :: its, off, pend, h => by
    rw [Lvm.X.fsPre, itemKinds, fsPreK_reads, fsPre_eq_fsPreK p its _ _ h]
    rfl
  | .sample :: its, off, pend, h => by
    rw [Lvm.X.fsPre, itemKinds, fsPreK, fsPre_eq_fsPreK p its _ _ h]
  | .cap _ _ :: _, _, _, h => by simp [RSItems] at h
  | .positions _ :: _, _, _, h => by simp [RSItems] at h
  | .opening _ :: _, _, _, h => by simp [RSItems] at h

theorem other_not_mem : ∀ (its : List Item), RSItems its = true → EvK.other ∉ itemKinds its
  | [], _ => by simp [itemKinds]
  | .read m :: its, h => by simpa [itemKinds] using other_not_mem its h
  | .sample :: its, h => by simpa [itemKinds] using other_not_mem its h
  | .cap _ _ :: _, h => by simp [RSItems] at h
  | .positions _ :: _, h => by simp [RSItems] at h
  | .opening _ :: _, h => by simp [RSItems] at h

end Lvm.ASM
