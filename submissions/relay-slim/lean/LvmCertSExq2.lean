-- lvm2 X-REC2 / S4-S2 (helper XA). O5c for two `C_rec` levels (lvm2 S4, on S2J: `g = 14` proofs of
-- work, Johnson/OOD on `C_main`), generic in `V_S`: WP-13a's
-- extractor `EX` returns the specification extractor's witness (`S.Ex K.ext`, `kcertS`'s `extS`: DEC's
-- level-1 decoder, then WP-13b's) on accepted `S` proofs over logs of potential below 1, or a witness
-- of the relation. WP-14d's `LvmCertSExq` (v1, one level) adapted: its helpers moved here unchanged
-- (but `roots_trun`, which now names the caps); the replay runs through level 1's commitment and level
-- 0's opening (`LvmCertSExq2Run`). `LvmCertSExq.ext_eq_S` instantiates `V_S := VS20`.
import LvmCertSExt
import LvmCertSGood
import LvmCertSExqCodec
import LvmCertSExq2Run

/-!
# O5c for two levels: `EX = S.Ex K.ext` on good logs

**`ext_eq_gen`**: for `mid` with `MidSpec`, `MidShape`, `MidFollows` and `child` of WP-13a's form
(`ChildX`), on an accepted `'S'` proof over a log with `μ K L < 1`, `EX (accV VS) = S.Ex K.ext` or
`EX` returns a witness (an `S` node outside the extractor's domain: the search).

In the domain, `EX_node`'s inputs are the replayed history's: the chain answers at `alphaPos j`
(`α₀`) and `alpha1Pos j` (`α₁`) are the history's fold samples (`simK2_chain` on three segments:
up to level 1's cap, the cap with level 0's positions and `λ`, and after level 0's opening level 1's
intro and fold rounds; `openRec_P20`: the schedule's slices); `readWd1 L (capRec1 π)` and
`readWd L (capRec π)` are `C_rec`'s committed words; `f2E π` is the replayed residual; the decoders
succeed there (`decode_S`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-! ## The child of WP-13a's node witness -/

/-- The words of a `C_rec` candidate (WP-14c's `wOfCol`). -/
def wOfColX (q : Column 19) (i : ℕ) : RecursionFast.Word := BF64.toBitVec (q.values.getD i 0)

/-- **`child` is WP-13a's left child** of the candidate's words (WP-14c's `childS`). -/
def ChildX (child : Column 19 → Signed) : Prop :=
  ∀ q, child q = ⟨Lvm.Replay.reassemble Lvm.X.pX (Lvm.X.readTraceL (Lvm.X.laneOf (wOfColX q))),
    Lvm.X.readTraceL (Lvm.X.laneOf (wOfColX q)), Lvm.X.sigOfF (Lvm.X.sigCol (wOfColX q))⟩

/-! ## The replay of an accepted proof -/

theorem Ex_inv (S : Scheme) {c : RecursionFast.Digest} {π : RecursionFast.Proof} {L : Log} {x : S.Stmt}
    {h : List Ev}
    (hx : ∀ {W' : Type} (ext : RecursionFast.Digest → S.Stmt → List Ev → W'),
      S.Ex ext c π L = some (ext c x h)) :
    ∃ body e₀ e₁, S.hdr π = some (x, body) ∧
      L.find? (fun e => decide (e.1 = toQ S.q0)) = some e₀ ∧
      L.find? (fun e => decide (e.1 = S.seedQ e₀.2 x)) = some e₁ ∧
      S.trun L (S.P x) e₁.2 [] [] body [] = some (true, h) := by
  have hh := hx (fun _ x h => (x, h))
  unfold Scheme.Ex at hh
  rcases hhdr : S.hdr π with _ | ⟨x', body⟩
  · rw [hhdr] at hh; simp at hh
  · rw [hhdr] at hh
    simp only at hh
    split_ifs at hh
    cases h0 : L.find? (fun e => decide (e.1 = toQ S.q0)) with
    | none => rw [h0] at hh; simp at hh
    | some e₀ =>
      rw [h0, Option.bind_some] at hh
      cases h1 : L.find? (fun e => decide (e.1 = S.seedQ e₀.2 x')) with
      | none => rw [h1] at hh; simp at hh
      | some e₁ =>
        rw [h1, Option.bind_some] at hh
        cases hr : S.trun L (S.P x') e₁.2 [] [] body [] with
        | none => rw [hr] at hh; simp at hh
        | some r =>
          rw [hr, Option.bind_some] at hh
          obtain ⟨b, hf⟩ := r
          split_ifs at hh with hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          refine ⟨body, e₀, e₁, rfl, rfl, h1, ?_⟩
          rw [hr]
          simp only at hb
          rw [hb]

theorem hdrS_inv {π : RecursionFast.Proof} {x body : List UInt8} (h : hdrS π = some (x, body)) :
    π.size = piSz ∧ π.data.toList.take 8 = sPrefix ∧ x = (π.data.toList.drop 8).take hdrLen ∧
      body = π.data.toList.drop Lvm.headerBytes := by
  unfold hdrS at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨hc.1, hc.2, h.1.symm, h.2.symm⟩

theorem byte0_of_prefix {π : RecursionFast.Proof} (h : π.data.toList.take 8 = sPrefix) : π.data[0]? = some 0x53 := by
  have := congrArg (fun l : List UInt8 => l[0]?) h
  simp only [sPrefix] at this
  simpa using this

/-! ## The roots -/

theorem capBytes_main (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeS vk P).capBytes 19 64 = 8192 := by
  simp only [Scheme.capBytes, schemeS, capOfS]; norm_num

theorem capBytes_rec (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeS vk P).capBytes 15 64 = 4096 := by
  simp only [Scheme.capBytes, schemeS, capOfS]; norm_num

/-- **The replay of the roots**: the two commitments' words, then the rest of `P_S` with both caps
pending and the two commitments' records. -/
theorem roots_trun {vk : RecursionFast.Digest} {mid : List UInt8 → VerifierProgram OpenClaims}
    {x : List UInt8} {L : Log} {B : List UInt8} {st : RecursionFast.Digest} {h : List Ev}
    (e : (schemeS vk (PSWith mid)).trun L (PSWith mid x) st [] [] (B.drop 5624) [] = some (true, h)) :
    ∃ k rest, PSWith mid x = .commit 19 64 (.commit 15 64 k) ∧
      h = [Ev.commit 19 64 ((schemeS vk (PSWith mid)).wordOf L
        ((schemeS vk (PSWith mid)).capI 19 64 (B.drop 5624))),
        Ev.commit 15 64 ((schemeS vk (PSWith mid)).wordOf L
          ((schemeS vk (PSWith mid)).capI 15 64 (B.drop 13816)))] ++ rest ∧
      (schemeS vk (PSWith mid)).trun L k st (sl B 5624 (17912 - 5624))
        [(schemeS vk (PSWith mid)).capI 19 64 (B.drop 5624),
          (schemeS vk (PSWith mid)).capI 15 64 (B.drop 13816)] (B.drop 17912)
        [Ev.commit 19 64 ((schemeS vk (PSWith mid)).wordOf L
          ((schemeS vk (PSWith mid)).capI 19 64 (B.drop 5624))),
        Ev.commit 15 64 ((schemeS vk (PSWith mid)).wordOf L
          ((schemeS vk (PSWith mid)).capI 15 64 (B.drop 13816)))] = some (true, h) := by
  obtain ⟨k, hk⟩ := PSWith_roots mid x
  rw [hk] at e
  simp only [Scheme.trun, capBytes_main, capBytes_rec] at e
  split_ifs at e
  · simp at e
  · simp at e
  rw [List.drop_drop] at e
  have hbuf : [] ++ List.take 8192 (List.drop 5624 B) ++ List.take 4096 (List.drop (5624 + 8192) B) =
      sl B 5624 (17912 - 5624) := by
    simp only [List.nil_append, sl]
    rw [show 17912 - 5624 = 8192 + 4096 by norm_num, List.take_add, List.drop_drop]
  rw [hbuf, List.drop_drop] at e
  simp only [List.nil_append, List.cons_append, Nat.reduceAdd] at e
  have hpre := trun_prefix _ _ _ _ _ _ _ _ _ _ e
  obtain ⟨rest, hrest⟩ := hpre
  exact ⟨k, rest, hk, by rw [← hrest], e⟩

/-! ## Event kinds of `C_rec`'s opening head -/

theorem read_after {l : List Ev} {c : E} (h : (readScalar).after l = some (.ret c)) :
    l = [Ev.read c] := by
  rcases l with _ | ⟨e, _ | ⟨e', es⟩⟩
  · simp [readScalar, VerifierProgram.after] at h
  · cases e <;> simp [readScalar, VerifierProgram.after] at h; subst h; rfl
  · cases e <;> cases e' <;> simp [readScalar, VerifierProgram.after] at h

theorem readScalars_after_eq : ∀ (n : ℕ) {l : List Ev} {xs : List E},
    (readScalars n).after l = some (.ret xs) → l = xs.map Ev.read
  | 0, l, xs, h => by
    cases l with
    | nil => simp [readScalars, VerifierProgram.after] at h; subst h; rfl
    | cons e es => cases e <;> simp [readScalars, VerifierProgram.after] at h
  | n + 1, l, xs, h => by
    obtain ⟨y, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := readScalar) h
    obtain ⟨ys, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    rw [read_after h1, readScalars_after_eq n h3]
    cases m₂ with
    | nil => simp [VerifierProgram.after] at h4; subst h4; simp
    | cons e es => cases e <;> simp [VerifierProgram.after] at h4

/-- **A level's proof-of-work prefix** (`grindPre g`, `g > 0`): the separator and the nonce. -/
theorem grindPre_after {g : ℕ} (hg : g ≠ 0) {l : List Ev} (h : (grindPre g).after l = some (.ret ())) :
    ∃ c y, l = [Ev.sample c, Ev.read y] := by
  unfold grindPre at h
  rw [if_neg hg] at h
  obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
  obtain rfl := sample_after h1
  obtain ⟨y, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret (p := readScalar) h2
  obtain rfl := read_after h3
  cases m₂ with
  | nil => exact ⟨c, y, rfl⟩
  | cons e es => cases e <;> simp [VerifierProgram.after] at h4

/-- **A level's PoW check** (`powCheck g`, `g > 0`): one challenge. -/
theorem powCheck_after {g : ℕ} (hg : g ≠ 0) {l : List Ev} (h : (powCheck g).after l = some (.ret ())) :
    ∃ c, l = [Ev.sample c] := by
  unfold powCheck at h
  rw [if_neg hg] at h
  obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
  obtain rfl := sample_after h1
  cases l₂ with
  | nil => exact ⟨c, rfl⟩
  | cons e es =>
    unfold VerifierProgram.require at h2
    split_ifs at h2 <;> cases e <;> simp [VerifierProgram.after] at h2

theorem roundPoly_kinds {t : E} {l : List Ev} {q : List E}
    (h : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 t none).after l = some (.ret q)) :
    l.map kindOf = [.read, .read] := by
  unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly at h
  obtain ⟨c₀, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := readScalar) h
  obtain ⟨tl, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
  have hl := readScalars_after_len _ h3
  rw [read_after h1, readScalars_after_eq _ h3]
  cases m₂ with
  | nil =>
    obtain ⟨c₂, rfl⟩ : ∃ c₂, tl = [c₂] := by
      rcases tl with _ | ⟨a, _ | ⟨b, t'⟩⟩ <;> simp at hl ⊢
    rfl
  | cons e es => cases e <;> simp [VerifierProgram.after] at h4

theorem foldRoundsT_kinds : ∀ (n : ℕ) (s : WhirStateT) (lf : List E) {l : List Ev}
    {r : WhirStateT × List E}, (foldRoundsT n s lf).after l = some (.ret r) →
      l.map kindOf = (List.replicate n [EvK.sample, .read, .read]).flatten
  | 0, s, lf, l, r, h => by
    cases l with
    | nil => rfl
    | cons e es => cases e <;> simp [foldRoundsT, VerifierProgram.after] at h
  | n + 1, s, lf, l, r, h => by
    unfold foldRoundsT at h
    obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
    obtain rfl := sample_after h1
    obtain ⟨quad, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    rw [List.map_append, List.map_append, roundPoly_kinds h3, foldRoundsT_kinds n _ _ h4,
      List.replicate_succ, List.flatten_cons]
    rfl

/-- (−) **`MidFollows` is not vacuous**: middle phases that return at once do not follow the
schedule. -/
theorem not_midFollows_ret : ¬ MidFollows fun _ ↦ (VerifierProgram.ret (([], []) : OpenClaims)) := by
  intro h
  have e := h [] [] ([], []) rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, c, -⟩ := openRec_P20
  rw [← e] at c
  simp at c

theorem itemKinds_append : ∀ (a b : List Item), itemKinds (a ++ b) = itemKinds a ++ itemKinds b
  | [], b => rfl
  | .read m :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.append_assoc]
  | .sample :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.cons_append]
  | .cap _ _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]
  | .positions _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]
  | .opening _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]

/-- The number of samples of a history is the count of its sample kinds. -/
theorem samples_length : ∀ (l : List Ev), (l.filterMap sampleOf).length = (l.map kindOf).count .sample
  | [] => rfl
  | e :: l => by
    rw [List.map_cons, List.count_cons, ← samples_length l]
    cases e <;> simp [sampleOf, kindOf, List.filterMap_cons]

/-! ## The decoder's inputs -/

theorem capI_rec (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (b : List UInt8) :
    (schemeS vk P).capI 15 64 b = ⟨15, 64, 7, digestsOf (b.take 4096) (2 ^ 7)⟩ := by
  unfold Scheme.capI
  rw [capBytes_rec]
  rfl

/-- **O13**: the cap `C_rec`'s commitment reads is π's `capRec`. -/
theorem capRec_eq (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (π : RecursionFast.Proof)
    (hs : 17912 ≤ π.size) :
    (schemeS vk P).capI 15 64 (π.data.toList.drop 13816) = ⟨15, 64, 7, Lvm.X.capRec π⟩ := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  have hc : Lvm.X.capRecOff Lvm.X.pX = 13816 := Lvm.X.layout_P20.2.2.2.2.1
  rw [capI_rec]
  have e : digestsOf ((π.data.toList.drop 13816).take 4096) (2 ^ 7) = Lvm.X.capRec π := by
    unfold digestsOf Lvm.X.capRec
    rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
    refine List.map_congr_left fun e he => ?_
    have he' : e < 128 := List.mem_range.1 he
    rw [Lvm.X.hdD_eq_digestAt, hc]
    apply Vector.ext
    intro i hi
    simp only [dg, digestAt, Vector.getElem_ofFn]
    rw [get!_eq_getD, List.getD_eq_getElem _ _ (by simp only [List.length_drop, List.length_take]; omega),
      List.getD_eq_getElem _ _ (by omega)]
    simp only [List.getElem_drop, List.getElem_take]
    congr 1
    omega
  rw [e]

theorem decodeRec_congr_f (wd : ℕ → ℕ → BF64) (α : ℕ → BF64.Ext3) {f f' : ℕ → BF64.Ext3}
    (h : ∀ v < 2 ^ 13, f v = f' v) : Lvm.X.decodeRec wd α f = Lvm.X.decodeRec wd α f' := by
  have he : ∀ q, Lvm.X.enc0 f q = Lvm.X.enc0 f' q := fun q =>
    Finset.sum_congr rfl fun v hv => by rw [h v (Finset.mem_range.1 hv)]
  have ha : Lvm.X.agreeL wd α f = Lvm.X.agreeL wd α f' := by
    unfold Lvm.X.agreeL
    exact List.filter_congr fun q _ => by rw [he]
  unfold Lvm.X.decodeRec Lvm.X.decWord Lvm.X.selJ
  rw [ha]

theorem values_getD_msgs (q : Column 19) (i : ℕ) :
    q.values.getD i 0 = ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)).getD i 0 := by
  have hlen : ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)).length = 2 ^ 19 := by
    rw [List.length_map, List.length_range]
  rcases Nat.lt_or_ge i (2 ^ 19) with hi | hi
  · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi), List.getElem_map, List.getElem_range]
    rfl
  · rw [List.getD_eq_default _ _ (by rw [hlen]; omega)]
    rcases q with ⟨v⟩
    show Vector.getD v i 0 = 0
    unfold Vector.getD
    rw [Array.getD_eq_getD_getElem?]
    simp only [Vector.getElem?_toArray]
    rw [Vector.getElem?_eq_none (by omega)]
    rfl

theorem wOfColX_apply (q : Column 19) (i : ℕ) : wOfColX q i = BF64.toBitVec (q.values.getD i 0) := rfl

theorem wOut_apply (l : List BF64) (i : ℕ) : Lvm.X.wOut l i = BF64.toBitVec (l.getD i 0) := rfl

/-- The candidate's words are the decoder's output words (kernel-cheap form: `rw`, no `unfold`). -/
theorem wOfColX_eq (q : Column 19) :
    wOfColX q = Lvm.X.wOut ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)) := by
  funext i
  rw [wOfColX_apply, wOut_apply, values_getD_msgs]

/-- The chain's target at `p ≥ 1` absorbs the slice `msgL p`. -/
theorem fsQL_eq (π : RecursionFast.Proof) {p : ℕ} (hp : 0 < p) (s : RecursionFast.Digest) :
    Lvm.X.fsQL π p s = toQ (s.toList ++ sl π.data.toList (Lvm.X.msgL p).1 (Lvm.X.msgL p).2) := by
  have hd := Lvm.X.fsQL_data (π := π) p hp s
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    Nat.add_sub_cancel_left] at hd
  rcases hq : Lvm.X.fsQL π p s with ⟨a⟩
  rw [hq] at hd
  simp only at hd
  unfold toQ sl
  rw [← hd, Array.toArray_toList]

theorem msgL_eq (p : ℕ) : Lvm.X.msgL p = (Lvm.X.fsMsgs Lvm.X.pX).getD (p - 1) (0, 0) := by
  unfold Lvm.X.msgL
  rfl

/-! ## Level 1 (lvm2 S4) -/

theorem smpOf_eq : smpOf = sampleOf := by
  funext e
  cases e <;> rfl

theorem capBytes_rec1 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    (schemeS vk P).capBytes 12 48 = 4096 := by
  simp only [Scheme.capBytes, schemeS, capOfS]; norm_num

theorem capI_rec1 (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) (b : List UInt8) :
    (schemeS vk P).capI 12 48 b = ⟨12, 48, 7, digestsOf (b.take 4096) (2 ^ 7)⟩ := by
  unfold Scheme.capI
  rw [capBytes_rec1]
  rfl

/-- The positions a completed run of `samplePositionsAux` returns. -/
def posLen (per : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, rem => if rem = 0 then 0 else min per rem + posLen per fuel (rem - min per rem)

/-- **A run of the positions** is samples only, and returns `posLen` positions. -/
theorem samplePositionsAux_kinds (per depth : ℕ) : ∀ (fuel rem : ℕ) {l : List Ev} {qs : List ℕ},
    (samplePositionsAux per depth fuel rem).after l = some (.ret qs) →
      (∀ e ∈ l, kindOf e = .sample) ∧ qs.length = posLen per fuel rem
  | 0, rem, l, qs, h => by
    cases l with
    | nil =>
      simp only [samplePositionsAux, VerifierProgram.after, Option.some.injEq] at h
      cases h
      simp [posLen]
    | cons e es => cases e <;> simp [samplePositionsAux, VerifierProgram.after] at h
  | fuel + 1, rem, l, qs, h => by
    unfold samplePositionsAux at h
    by_cases hr : rem = 0
    · rw [if_pos hr] at h
      cases l with
      | nil =>
        simp only [VerifierProgram.after, Option.some.injEq] at h
        cases h
        simp [posLen, hr]
      | cons e es => cases e <;> simp [VerifierProgram.after] at h
    · rw [if_neg hr] at h
      obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
      obtain rfl := sample_after h1
      obtain ⟨rest, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
      obtain ⟨k1, k2⟩ := samplePositionsAux_kinds per depth fuel _ h3
      cases m₂ with
      | nil =>
        simp only [VerifierProgram.after, Option.some.injEq] at h4
        cases h4
        refine ⟨fun e he => ?_, ?_⟩
        · simp only [List.singleton_append, List.append_nil, List.mem_cons] at he
          rcases he with rfl | he
          · rfl
          · exact k1 e he
        · simp [posLen, hr, k2]
      | cons e es => cases e <;> simp [VerifierProgram.after] at h4

theorem enc1_congr {f f' : ℕ → BF64.Ext3} (h : ∀ v < 2 ^ 9, f v = f' v) (q : ℕ) :
    Lvm.X.enc1 f q = Lvm.X.enc1 f' q :=
  Finset.sum_congr rfl fun v hv => by rw [h v (Finset.mem_range.1 hv)]

/-- The level-1 decoder reads `f₂` below `2^9` only. -/
theorem decodeRec1_congr_f (wd : ℕ → ℕ → BF64) (α : ℕ → BF64.Ext3) {f f' : ℕ → BF64.Ext3}
    (h : ∀ v < 2 ^ 9, f v = f' v) : Lvm.X.decodeRec1 wd α f = Lvm.X.decodeRec1 wd α f' := by
  have ha : Lvm.X.agree1L wd α f = Lvm.X.agree1L wd α f' := by
    unfold Lvm.X.agree1L
    exact List.filter_congr fun q _ => by rw [enc1_congr h]
  unfold Lvm.X.decodeRec1 Lvm.X.dec1At Lvm.X.coef1 Lvm.X.sel1J
  rw [ha]

theorem bitsToNat_symmN (n v : ℕ) (hv : v < 2 ^ n) :
    bitsToNat ((bitsEquiv n).symm ⟨v, hv⟩) = v := by
  rw [← bitsEquiv_val, Equiv.apply_symm_apply]

theorem forall₂_reads_samples {l : List Ev} {ks : List EvK} (h : l.map kindOf = ks)
    (ho : EvK.other ∉ ks) : List.Forall₂ KM l (ks.map toK2) := forall₂_of_kinds l ks h ho

/-- **`P_S` after level 0's proof of work, positions and `λ`** is at level 0's opening, of
commitment `1`. -/
theorem PS_after_query {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}
    {hr lm lq lf lc l₁ : List Ev} {cl : OpenClaims} {ρ lam c₁ c₂ y : E} {quad : List E}
    {r : WhirStateT × List E} {qs : List ℕ}
    (h1 : rootsProg.after hr = some (.ret ())) (h3 : (mid x).after lm = some (.ret cl))
    (h8 : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq =
      some (.ret quad))
    (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).after lc = some (.ret ()))
    (hgp : (grindPre 14).after [Ev.sample c₁, Ev.read y] = some (.ret ()))
    (hpw : (powCheck 14).after [Ev.sample c₂] = some (.ret ()))
    (hp1 : (samplePositions 8 (19 - r.1.folds.length + 2) 170).after l₁ = some (.ret qs)) :
    ∃ K, (PSWith mid x).after (hr ++ (lm ++ (([Ev.sample ρ] ++ (lq ++ (lf ++ lc))) ++
      ([Ev.sample c₁, Ev.read y] ++ ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])))))) =
        some (.query 1 qs K) := by
  obtain ⟨g', e3⟩ := after_stacked_two_commit cfgRec20G recLevel0 recLevel1 rec20_levels cl.1 h8 h10 hcm
  have e5 : (queryFrag 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).after (l₁ ++ [Ev.sample lam]) =
      some ((queryOpenings 1 qs).bind fun words ↦ VerifierProgram.ret (qs, lam, words)) := by
    unfold queryFrag
    refine (after_bind_append _ hp1 _).trans ?_
    rw [← List.append_nil [Ev.sample lam]]
    refine (after_bind_append _ (rfl : sampleChallenge.after [Ev.sample lam] = some (.ret lam)) _).trans ?_
    exact after_nil _
  have e5' : (queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).after
      ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])) =
      some ((queryOpenings 1 qs).bind fun words ↦ VerifierProgram.ret (qs, lam, words)) := by
    unfold queryFragG
    exact (after_bind_append _ hpw _).trans e5
  have e5'' := (after_bind_append (fun _ : Unit ↦
    (queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).bind g') hgp _).trans
      (after_bind_of_after g' _ _ e5')
  have e4 := after_bind_of_after (fun _ : Unit ↦ verifyStackedJ (cfgMain24J 3) cl.2 >>= fun _ ↦
    VerifierProgram.ret true) _ _ e3
  have e6 := after_bind_of_after (fun _ : Unit ↦ verifyStackedJ (cfgMain24J 3) cl.2 >>= fun _ ↦
    VerifierProgram.ret true) _ _ e5''
  have e7 : ((verifyStackedUd cfgRec20G cl.1).bind fun _ : Unit ↦ verifyStackedJ (cfgMain24J 3) cl.2 >>=
      fun _ ↦ VerifierProgram.ret true).after (([Ev.sample ρ] ++ (lq ++ (lf ++ lc))) ++
        ([Ev.sample c₁, Ev.read y] ++ ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])))) =
        some ((((queryOpenings 1 qs).bind fun words ↦
          VerifierProgram.ret (qs, lam, words)).bind g').bind fun _ : Unit ↦
            verifyStackedJ (cfgMain24J 3) cl.2 >>= fun _ ↦ VerifierProgram.ret true) := by
    rw [VerifierProgram.after_append, e4, Option.bind_some]
    exact e6
  have e8 := (after_bind_append (fun _ : Unit ↦ (mid x).bind openProg) h1 _).trans
    ((after_bind_append openProg h3 _).trans e7)
  rw [PSWith_eq]
  exact ⟨_, e8⟩

theorem not_commit_toK2 {ht w nb : ℕ} : ∀ (ks : List EvK), K2.commit ht w nb ∉ ks.map toK2
  | [] => by simp
  | k :: ks => by
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨by cases k <;> simp [toK2], not_commit_toK2 ks⟩

/-- The chain's targets of positions `D + 1 + i` absorb the slices `fsMsgs[D + i]`. -/
theorem chainT (π : RecursionFast.Proof) {ks : List K2} {off pend D N : ℕ}
    (hPre : fsPreK2 ks off pend = ((Lvm.X.fsMsgs P20).drop D).take N) (hD : 0 < D + 1) :
    ∀ i (hi : i < (fsPreK2 ks off pend).length) (s : RecursionFast.Digest),
      Lvm.X.fsQL π (D + 1 + i) s =
        toQ (s.toList ++ sl π.data.toList ((fsPreK2 ks off pend)[i]).1 ((fsPreK2 ks off pend)[i]).2) := by
  intro i hi s
  rw [fsQL_eq π (by omega), msgL_eq, ← List.getD_eq_getElem _ (0, 0) hi, hPre]
  have hi' : i < N := by
    have := hi
    rw [hPre] at this
    exact lt_of_lt_of_le this (List.length_take_le _ _)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi',
    List.getElem?_drop, show D + 1 + i - 1 = D + i by omega]

theorem kA1 : itemK2 P20 shRec recHead1 =
    ([EvK.sample, EvK.read, EvK.read] ++ (List.replicate 6 [EvK.sample, EvK.read, EvK.read]).flatten).map
      toK2 := by
  rw [openRec_P20.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl

theorem kB : itemK2 P20 shRec recHeadB =
    ([EvK.read, EvK.read] ++ (List.replicate 4 [EvK.sample, EvK.read, EvK.read]).flatten).map toK2 := by
  rw [openRec_P20.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl

theorem kA2 : itemK2 P20 shRec recHead2 =
    .commit 12 48 4096 :: .sample :: .read :: (List.replicate 24 EvK.sample).map toK2 := by
  rw [openRec_P20.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl

open Classical in
/-- **O5c for two `C_rec` levels**, generic in `V_S`: on an accepted `'S'` proof over a log of
potential below `1`, WP-13a's `EX` is the specification extractor of `kcertS` (DEC's level-1 decoder,
then WP-13b's, on the replayed history), or returns a witness of the relation. `hA`: `acc` implies
the search's bounds (the contract's, `sFits_of_acc`). -/
theorem ext_eq_gen {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}
    (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid) {VS : SProg}
    {child : Column 19 → Signed} (hnode : ∀ vk, NodeSound VS vk Good child)
    (hch : ChildX child) (hfol : MidFollows mid)
    (hA : ∀ vk c p, accV VS vk c p = true → Lvm.X.SFits p) (vk : RecursionFast.Digest) (L : Log)
    (c : RecursionFast.Digest) (π : RecursionFast.Proof)
    (hμ : Scheme.μ (kcertS hmid hLm hsh (hnode vk)) L < 1)
    (hacc : ((schemeS vk (PSWith mid)).V c π).runLog L = some true) :
    (∃ w, Lvm.X.EX (accV VS) c π L = some w ∧ Rel (accV VS vk) c w) ∨
      Lvm.X.EX (accV VS) c π L =
        (schemeS vk (PSWith mid)).Ex (kcertS hmid hLm hsh (hnode vk)).ext c π L := by
  obtain ⟨x, h, hok, hreach, hafter, hB, hBp, hD, hEx⟩ :=
    Scheme.final_good (kcertS hmid hLm hsh (hnode vk)) L c π hμ hacc
  obtain ⟨body, e₀, e₁, hhdr, h0, h1, htr⟩ := Ex_inv _ hEx
  obtain ⟨hsz, hpre8, rfl, rfl⟩ := hdrS_inv hhdr
  set S := schemeS vk (PSWith mid) with hSdef
  set B := π.data.toList with hBdef
  have hsize : π.size = Lvm.piSize Lvm.X.pX := hsz
  have hpi : π.size = 783192 := by rw [hsize]; exact Lvm.X.piSize_eq
  have hBlen : B.length = π.size := Array.length_toList
  have hb0 : π.data[0]? = some 0x53 := byte0_of_prefix hpre8
  have hhd : hdrOf ((B.drop 8).take hdrLen) = Header.ofProof π :=
    hdrOf_eq π (by rw [hpi]; decide)
  have hExK := hEx (kcertS hmid hLm hsh (hnode vk)).ext
  rw [hExK]
  have hext : (kcertS hmid hLm hsh (hnode vk)).ext = extS mid child := rfl
  rw [hext]
  -- the header fields
  have hfb : (Header.ofProof π).b = (Lvm.X.pw π 1).toNat := (pw_toNat π 1 (by omega)).symm
  have hfn : (Header.ofProof π).n = (Lvm.X.pw π 14).toNat := (pw_toNat π 14 (by omega)).symm
  have hfs : (Header.ofProof π).s = Lvm.X.hdD π 10 := (Lvm.X.hdD_eq_digestAt π 10).symm
  have hfvk : (Header.ofProof π).vk = Lvm.X.hdD π 2 := (Lvm.X.hdD_eq_digestAt π 2).symm
  have hfcL : (Header.ofProof π).cL = Lvm.X.hdD π 6 := (Lvm.X.hdD_eq_digestAt π 6).symm
  have hfh : (Header.ofProof π).h = Lvm.X.hdD π 15 := (Lvm.X.hdD_eq_digestAt π 15).symm
  have hfsig : (Header.ofProof π).sig = Lvm.X.sigOfF fun j => Lvm.X.pw π (19 + j) :=
    sig_eq π (by rw [hpi]; decide)
  by_cases hb : Lvm.X.pw π 1 = 0
  · -- a leaf
    right
    rw [Lvm.X.EX_leaf _ c π L hsize hb0 hb]
    unfold extS witOf
    rw [hhd, if_pos (by rw [hfb, hb]; rfl), hfs, hfn]
    rfl
  have hbne : (Header.ofProof π).b ≠ 0 := by
    rw [hfb]; intro h0'; exact hb (BitVec.eq_of_toNat_eq (by rw [h0']; rfl))
  by_cases hdom : Lvm.X.InDomE c π L
  swap
  · -- a node outside the domain: the search
    left
    rw [Lvm.X.EX_node_out _ c π L hdom hsize hb0 hb]
    have hvk : Lvm.X.hdD π 2 = vk := by
      have := hok
      simp only [hSdef, schemeS, okS, Bool.and_eq_true, beq_iff_eq] at this
      rw [← hfvk, ← hhd]
      exact this.1.1.1.2
    rw [hvk]
    exact Lvm.X.search_spec_acc (fun c' p hp => hA vk c' p hp)
      ⟨_, (kcertS hmid hLm hsh (hnode vk)).extract hok hreach hafter hB hBp hD⟩
  -- a node in the domain
  right
  have hS' : ¬ Lvm.X.StateHit L := Lvm.X.notStateHit_of_notBad (Scheme.mu_lt_one hμ).1
  obtain ⟨hr, lm, cl, ρ, lq, quad, lf, r, lc, lg, g, lhq, hq, lf1, r₁, lres, res, rest, hsplit, h1r,
    h3, h8, h10, hcm, hg, hh, hf1, hres⟩ := accept_split hafter
  have hrd2 := recData2_split (rest := rest) h1r h3 h8 h10 hcm hg hh hf1 hres
  obtain ⟨W₁, W₂, rfl⟩ := roots_after h1r
  have htr' : S.trun L (PSWith mid ((B.drop 8).take hdrLen)) e₁.2 [] [] (B.drop 5624) [] =
      some (true, h) := htr
  obtain ⟨k, rest₀, hk, hh0, htrk⟩ := roots_trun htr'
  rw [hsplit] at hh0
  simp only [List.cons_append, List.nil_append, List.cons.injEq, Ev.commit.injEq, true_and] at hh0
  obtain ⟨rfl, rfl, -⟩ := hh0
  -- the fold states, the residual's length, the level-1 commitment
  obtain ⟨e1r, e2r, e3r, -, -⟩ := foldRoundsT_after 6 _ [] h10
  rw [List.nil_append] at e1r e3r
  have hlen6 : r.2.length = 6 := by rw [e1r]; exact e2r
  have hfl : r.1.folds.length = 6 := by rw [e3r]; exact e2r
  obtain ⟨f1r, f2r, f3r, -, -⟩ := foldRoundsT_after 4 _ [] hf1
  rw [List.nil_append] at f1r
  have hlen4 : r₁.2.length = 4 := by rw [f1r]; exact f2r
  have hfl1 : r₁.1.folds.length = 10 := by rw [f3r, glueLv_folds, List.length_append, hfl, f2r]
  have hres' := readScalars_after_eq _ hres
  have hreslen : res.length = 2 ^ 9 := by rw [readScalars_after_len _ hres, hfl1]
  obtain ⟨Wc, hlc⟩ := readCommitment_after hcm
  have hht : 19 - r.1.folds.length - 4 + 3 = 12 := by rw [hfl]
  -- the query group: proof of work, positions, `λ`, the opening
  obtain ⟨_, lgp, lgq, hlg0, hgp, hgq⟩ := after_bind_ret hg
  obtain ⟨c₁, y, rfl⟩ := grindPre_after (by norm_num) hgp
  have hgq' := hgq
  unfold queryFragG at hgq'
  obtain ⟨_, lpw, lqf, rfl, hpw, hqf⟩ := after_bind_ret hgq'
  obtain ⟨c₂, rfl⟩ := powCheck_after (by norm_num) hpw
  unfold queryFrag at hqf
  obtain ⟨qs, l₁, l₂, rfl, hp1, hp2⟩ := after_bind_ret hqf
  obtain ⟨lam, m₁, m₂, rfl, hp3, hp4⟩ := after_bind_ret hp2
  obtain rfl := sample_after hp3
  obtain ⟨w, n₁, n₂, rfl, hp5, hp6⟩ := after_bind_ret hp4
  obtain rfl := queryOpenings_after hp5
  have hn₂ : n₂ = [] := by
    cases n₂ with
    | nil => rfl
    | cons e es => cases e <;> simp [VerifierProgram.after] at hp6
  subst hn₂
  obtain ⟨hl₁k, hqsl⟩ := samplePositionsAux_kinds 8 _ 170 170 hp1
  have hqs : qs.length = 170 := by rw [hqsl]; decide
  have hl₁n : (l₁.filterMap sampleOf).length = 22 := by
    have := samplePositionsAux_after 8 _ 170 170 hp1
    rw [this]; decide
  have hl₁map : l₁.map kindOf = List.replicate 22 .sample := by
    have hall : l₁.map kindOf = List.replicate l₁.length .sample :=
      List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb; exact hl₁k e he⟩
    have hlen : l₁.length = 22 := by
      rw [← hl₁n, samples_length, hall, List.count_replicate_self]
    rw [hall, hlen]
  -- the kinds of the three segments
  have hRSm := openRec_P20.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fm : lm.map kindOf = itemKinds midItems := hfol _ lm cl h3
  have fq : lq.map kindOf = [.read, .read] := roundPoly_kinds h8
  have ff := foldRoundsT_kinds 6 _ _ h10
  have fh : lhq.map kindOf = [.read, .read] := roundPoly_kinds hh
  have ff1 := foldRoundsT_kinds 4 _ _ hf1
  have hkA1 : List.Forall₂ KM (lm ++ ([Ev.sample ρ] ++ (lq ++ lf)))
      (itemK2 P20 shRec (midItems ++ recHead1)) := by
    rw [itemK2_append, itemK2_rs _ _ _ hRSm, kA1]
    refine forall₂_append (forall₂_of_kinds lm _ fm (other_not_mem _ hRSm))
      (forall₂_of_kinds _ _ ?_ (by decide))
    rw [List.map_append, List.map_append, fq, ff]
    rfl
  have hlg' : lg = [Ev.sample c₁, Ev.read y] ++ ([Ev.sample c₂] ++ (l₁ ++ ([Ev.sample lam] ++
      [Ev.query w]))) := by rw [hlg0]; simp only [List.append_nil]
  clear hlg0
  subst hlg'
  subst hlc
  have hkA2 : List.Forall₂ KM ([Ev.commit (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4) Wc] ++
      ([Ev.sample c₁, Ev.read y] ++ ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])))) (itemK2 P20 shRec recHead2) := by
    rw [kA2]
    refine .cons ⟨hht, rfl⟩ (.cons trivial (.cons trivial
      (forall₂_of_kinds ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])) _ ?_ (by simp))))
    rw [List.map_append, List.map_append, hl₁map]
    rfl
  have hkB : List.Forall₂ KM (lhq ++ lf1) (itemK2 P20 shRec recHeadB) := by
    rw [kB]
    refine forall₂_of_kinds _ _ ?_ (by decide)
    rw [List.map_append, fh, ff1]
  -- segment A1: the middle phases and `C_rec`'s head
  obtain ⟨oA1, oA1o, oA1p, oA2, oA2o, oA2p, oQ, oB, oBo, oBp, -, oF2, -, oCnt, -, -, -, -, o0⟩ :=
    openRec_P20
  obtain ⟨stA1, p1, hsA1, haA1, -, htA1⟩ := trun_simK2 S L B (itemK2 P20 shRec (midItems ++ recHead1))
    k 17912 5624 e₁.2 _ _ (lm ++ ([Ev.sample ρ] ++ (lq ++ lf)))
    ([Ev.commit (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4) Wc] ++ (([Ev.sample c₁, Ev.read y] ++
      ([Ev.sample c₂] ++ (l₁ ++ ([Ev.sample lam] ++ [Ev.query w])))) ++ (lhq ++ (lf1 ++ (lres ++ rest)))))
    true
    (fun ht w nb hm => by
      rw [itemK2_append, itemK2_rs _ _ _ hRSm, kA1, ← List.map_append] at hm
      exact absurd hm (not_commit_toK2 _))
    (by norm_num) hkA1 (by rw [htrk, hsplit]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [oA1o, oA1p] at htA1
  -- segment A2: level 1's cap, level 0's positions, `λ`
  obtain ⟨stA2, p2, hsA2, haA2, -, htA2⟩ := trun_simK2 S L B (itemK2 P20 shRec recHead2) p1 205280
    205232 stA1 _ _ ([Ev.commit (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4) Wc] ++
      ([Ev.sample c₁, Ev.read y] ++ ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])))) ([Ev.query w] ++ (lhq ++ (lf1 ++ (lres ++ rest)))) true
    (fun ht w nb hm => by
      rw [kA2, List.mem_cons, List.mem_cons, List.mem_cons] at hm
      rcases hm with hm | hm | hm | hm
      · cases hm; exact capBytes_rec1 vk (PSWith mid)
      · cases hm
      · cases hm
      · exact absurd hm (not_commit_toK2 _))
    (by norm_num) hkA2 (by rw [htA1]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [oA2o, oA2p] at htA2
  -- level 1's word
  have hWc : Wc = S.wordOf L ⟨12, 48, 7, Lvm.X.capRec1 π⟩ := by
    rw [kA2, simK2] at hsA2
    cases hs' : simK2 S L B (.sample :: .read :: (List.replicate 24 EvK.sample).map toK2) (205280 + 4096)
      205232 stA1 with
    | none => rw [hs'] at hsA2; simp at hsA2
    | some r' =>
      rw [hs', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsA2
      have e := hsA2.1
      simp only [List.singleton_append, List.cons.injEq, Ev.commit.injEq] at e
      rw [← e.1.2.2, capI_rec1, ← Lvm.X.layout_P20.2.2.2.1]
      have := capRec1_eq π (by rw [Lvm.X.layout_P20.2.2.2.1, hpi]; norm_num)
      rw [this]
  -- the program at level 0's opening, and the opening
  obtain ⟨K, hK⟩ := PS_after_query (lam := lam) h1r h3 h8 h10 hcm hgp hpw hp1
  have hPq : p2 = .query 1 qs K := by
    rw [hk] at hK
    simp only [List.cons_append, List.nil_append, VerifierProgram.after, and_self, ite_true] at hK
    have e : k.after ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf))) ++
        ([Ev.commit (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4) Wc] ++ ([Ev.sample c₁, Ev.read y] ++ ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam]))))) =
        some p2 := by
      rw [VerifierProgram.after_append, haA1, Option.bind_some, haA2]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hK e
    rw [hK] at e
    exact (Option.some.inj e).symm
  obtain ⟨cx, hcx⟩ := capsK2_prefix S B (itemK2 P20 shRec (midItems ++ recHead1)) 17912
    [S.capI 19 64 (B.drop 5624), S.capI 15 64 (B.drop 13816)]
  obtain ⟨cy, hcy⟩ := capsK2_prefix S B (itemK2 P20 shRec recHead2) 205280
    (capsK2 S B (itemK2 P20 shRec (midItems ++ recHead1)) 17912
      [S.capI 19 64 (B.drop 5624), S.capI 15 64 (B.drop 13816)])
  have hc1 : (capsK2 S B (itemK2 P20 shRec recHead2) 205280 (capsK2 S B (itemK2 P20 shRec
      (midItems ++ recHead1)) 17912 [S.capI 19 64 (B.drop 5624), S.capI 15 64 (B.drop 13816)]))[1]? =
      some (S.capI 15 64 (B.drop 13816)) := by
    rw [hcy, hcx]
    simp
  rw [hPq] at htA2
  obtain ⟨rows, hrows, -, -, htQ⟩ := trun_query S L hc1
    (show S.trun L (.query 1 qs K) stA2 (sl B 209400 (209400 - 209400)) _ (B.drop 209400) _ =
      some (true, _ ++ Ev.query w :: (lhq ++ (lf1 ++ (lres ++ rest)))) by
      rw [htA2]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  have hpb : qs.length * posBytes (S.capI 15 64 (B.drop 13816)) = 130560 := by
    rw [hqs, capI_rec]; simp only [posBytes]
  rw [hpb, List.drop_drop, show 209400 + 130560 = 339960 from rfl, sl_zero,
    ← sl_zero B 339960, ← Nat.sub_self 339960] at htQ
  -- segment B: level 1's intro and fold rounds
  obtain ⟨stB, p3, hsB, -, -, htB⟩ := trun_simK2 S L B (itemK2 P20 shRec recHeadB) (K rows) 339960
    339960 stA2 _ _ (lhq ++ lf1) (lres ++ rest) true
    (fun ht w nb hm => by rw [kB] at hm; exact absurd hm (not_commit_toK2 _))
    le_rfl hkB (by rw [htQ]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [oBo, oBp] at htB
  -- the residual
  have hk2 : lres.map kindOf = List.replicate (2 ^ 9) .read := by
    rw [hres', List.map_map, ← hreslen]
    show List.map (fun _ => EvK.read) res = _
    exact List.map_const'
  rw [oF2] at htB
  obtain ⟨stR, -, -, hsimR, -, -⟩ := trun_simK S L B _ p3 340200 340152 stB _ _ lres rest true
    (fun hm => by cases (List.mem_replicate.1 hm).2) (by norm_num)
    hk2 (by rw [htB]; simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])
  rw [simK_reads] at hsimR
  have hresv : res = (List.range (2 ^ 9)).map fun i => eOfBytes (sl B (340200 + 24 * i) 24) := by
    have e := (Prod.mk.inj (Option.some.inj hsimR)).1
    rw [hres'] at e
    apply List.map_injective_iff.2 (fun a b hab => Ev.read.inj hab)
    rw [← e, List.map_map]
    rfl
  -- the chain
  have hfm1 : Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L 1 = some e₁.2 := by
    have hq0 : Lvm.X.fsQL π 0 Lvm.X.zeroDL = toQ S.q0 := rfl
    have hseed : Lvm.X.fsQL π 1 e₀.2 = S.seedQ e₀.2 ((B.drop 8).take hdrLen) := by
      rw [fsQL_eq π (by norm_num), msgL_eq, show 1 - 1 = 0 from rfl, o0]
      rfl
    simp only [Lvm.X.fmAns, hq0, h0, Option.map_some, Option.bind_some, zero_add, hseed]
    exact congrArg (Option.map Prod.snd) h1
  have cA1 := simK2_chain S L B (Lvm.X.fsQL π) Lvm.X.zeroDL _ 17912 5624 e₁.2 1 _ stA1 hsA1 hfm1
    (chainT π (D := 1) (N := 1301) oA1 (by norm_num))
  simp only [smpOf_eq] at cA1
  obtain ⟨cA1, fA1⟩ := cA1
  have hlq : lq.filterMap sampleOf = [] := by
    have := samples_length lq
    rw [fq] at this
    exact List.length_eq_zero_iff.1 (by simpa using this)
  have hlm : (lm.filterMap sampleOf).length = 1294 := by rw [samples_length, fm]; exact oCnt
  have hpreS : (lm ++ ([Ev.sample ρ] ++ (lq ++ lf))).filterMap sampleOf =
      lm.filterMap sampleOf ++ (ρ :: r.2) := by
    simp only [List.filterMap_append, hlq, e1r, List.nil_append]
    rfl
  have hA1n : ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf))).filterMap sampleOf).length = 1301 := by
    rw [hpreS, List.length_append, hlm, List.length_cons, hlen6]
  rw [hA1n] at fA1
  have cA2 := simK2_chain S L B (Lvm.X.fsQL π) Lvm.X.zeroDL _ 205280 205232 stA1 1302 _ stA2 hsA2 fA1
    (chainT π (D := 1302) (N := 25) oA2 (by norm_num))
  simp only [smpOf_eq] at cA2
  obtain ⟨-, fA2⟩ := cA2
  have hA2n : (([Ev.commit (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4) Wc] ++
      ([Ev.sample c₁, Ev.read y] ++ ([Ev.sample c₂] ++ (l₁ ++ [Ev.sample lam])))).filterMap sampleOf).length = 25 := by
    simp only [List.filterMap_append, List.length_append, hl₁n]
    rfl
  rw [hA2n] at fA2
  have cB := simK2_chain S L B (Lvm.X.fsQL π) Lvm.X.zeroDL _ 339960 339960 stA2 1327 _ stB hsB fA2
    (chainT π (D := 1327) (N := 4) oB (by norm_num))
  simp only [smpOf_eq] at cB
  obtain ⟨cB, -⟩ := cB
  have hlhq : lhq.filterMap sampleOf = [] := by
    have := samples_length lhq
    rw [fh] at this
    exact List.length_eq_zero_iff.1 (by simpa using this)
  have hpreB : (lhq ++ lf1).filterMap sampleOf = r₁.2 := by
    rw [List.filterMap_append, hlhq, List.nil_append, f1r]
  have hfold : ∀ j < 6, ∃ a, Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alphaPos Lvm.X.pX j) =
      some a ∧ r.2.getD j 0 = chalOf a := by
    intro j hj
    have hlen : 1295 + j < ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf))).filterMap sampleOf).length := by
      rw [hA1n]; omega
    obtain ⟨a, ha, hea⟩ := cA1 (1295 + j) hlen
    refine ⟨a, by rw [Lvm.X.alphaPos_eq, show 1297 + j = 1 + 1 + (1295 + j) by omega]; exact ha, ?_⟩
    rw [show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreS,
      List.getD_append_right _ _ _ _ (by omega), hlm, show 1295 + j - 1294 = j + 1 by omega]
    rfl
  have hfold1 : ∀ j < 4, ∃ a, Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alpha1Pos Lvm.X.pX j) =
      some a ∧ r₁.2.getD j 0 = chalOf a := by
    intro j hj
    have hlen : j < ((lhq ++ lf1).filterMap sampleOf).length := by rw [hpreB, hlen4]; exact hj
    obtain ⟨a, ha, hea⟩ := cB j hlen
    refine ⟨a, by rw [Lvm.X.alpha1Pos_eq, show 1328 + j = 1327 + 1 + j by omega]; exact ha, ?_⟩
    rw [show chalOf a = S.chal a from rfl, ← hea, ← List.getD_eq_getElem _ 0 hlen, hpreB]
  let αd : ℕ → RecursionFast.Digest := fun j => if j < 6 then
    (Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alphaPos Lvm.X.pX j)).getD Lvm.X.zeroDL
    else Lvm.X.zeroDL
  have hα : ∀ j < 6, Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alphaPos Lvm.X.pX j) =
      some (αd j) := by
    intro j hj
    obtain ⟨a, ha, -⟩ := hfold j hj
    simp only [αd, if_pos hj, ha, Option.getD_some]
  let α1d : ℕ → RecursionFast.Digest := fun j => if j < 4 then
    (Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alpha1Pos Lvm.X.pX j)).getD Lvm.X.zeroDL
    else Lvm.X.zeroDL
  have hα1 : ∀ j < 4, Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alpha1Pos Lvm.X.pX j) =
      some (α1d j) := by
    intro j hj
    obtain ⟨a, ha, -⟩ := hfold1 j hj
    simp only [α1d, if_pos hj, ha, Option.getD_some]
  -- the decoders
  obtain ⟨qm, q, -, r', r₁', res', hrd, m, hdec1, hdec⟩ := decode_S hmid hLm hsh hreach hafter hB hD
  rw [← hsplit] at hrd2
  obtain ⟨rfl, rfl, rfl⟩ : r = r' ∧ r₁ = r₁' ∧ res = res' := by
    have := hrd2.symm.trans hrd
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this
  have hWr : WrOf h = S.wordOf L ⟨15, 64, 7, Lvm.X.capRec π⟩ := by
    rw [hsplit]
    unfold WrOf
    rw [rootsOf_split h1r, ← capRec_eq vk (PSWith mid) π (by omega)]
    rfl
  have hcm' : commits lm = [] := NoCommit.after_commits (hsh.noCommit _) h3
  have hcq := NoCommit.after_commits (nc_roundPoly _ _ _) h8
  have hcf := NoCommit.after_commits (nc_foldRoundsT _ _ _) h10
  have hWr1 : Wr1Of h = Wc := by
    rw [hsplit]
    unfold Wr1Of
    simp only [List.append_assoc, commits_append, hcm', hcq, hcf, List.nil_append]
    rfl
  have hdec1EX : Lvm.X.decodeRec1 (Lvm.X.readWd1 L (Lvm.X.capRec1 π)) (fun i => Lvm.X.alphaE (α1d i))
      (Lvm.X.f2E π) = some m := by
    have ew : Lvm.X.readWd1 L (Lvm.X.capRec1 π) = Lvm.X.wdOf (Wr1Of h) := by
      rw [hWr1, hWc]
      exact readWd1_eq_wdOf S rfl L _
    have ea : (fun i => Lvm.X.alphaE (α1d i)) = Lvm.X.alphaN1 fun i ↦ r₁.2.getD i 0 := by
      funext i
      unfold Lvm.X.alphaN1
      split_ifs with hi
      · obtain ⟨a, ha, hra⟩ := hfold1 i hi
        simp only [α1d, if_pos hi, ha, Option.getD_some]
        rw [hra, chalOf_eq_alphaE]
      · simp only [α1d, if_neg hi]
        exact alphaE_zero
    rw [ew, ea, decodeRec1_congr_f _ _ (f' := Lvm.X.fN2 (resMsg res)) ?_]
    · exact hdec1
    · intro v hv
      have hf2 : Lvm.X.f2Off Lvm.X.pX = 340200 := Lvm.X.layout_P20.2.2.2.2.2.2.2.2.1
      rw [f2E_eq π v (by rw [hf2, hpi]; omega), hf2]
      unfold Lvm.X.fN2
      rw [dif_pos hv]
      unfold resMsg
      erw [bitsToNat_symmN 9 v hv]
      rw [hresv, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
        List.getElem_map, List.getElem_range]
      rfl
  have hdecEX : Lvm.X.decodeRec (Lvm.X.readWd L (Lvm.X.capRec π)) (fun i => Lvm.X.alphaE (αd i)) m =
      some ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)) := by
    have ew : Lvm.X.readWd L (Lvm.X.capRec π) = Lvm.X.wdOf (WrOf h) := by
      funext p' t
      rw [hWr]
      unfold Lvm.X.readWd Lvm.X.wdOf
      rw [readRow_eq_wordOf S rfl]
    have ea : (fun i => Lvm.X.alphaE (αd i)) = Lvm.X.alphaN fun i ↦ r.2.getD i 0 := by
      funext i
      unfold Lvm.X.alphaN
      split_ifs with hi
      · obtain ⟨a, ha, hra⟩ := hfold i hi
        simp only [αd, if_pos hi, ha, Option.getD_some]
        rw [hra, chalOf_eq_alphaE]
      · simp only [αd, if_neg hi]
        exact alphaE_zero
    rw [ew, ea]
    exact hdec
  -- the witness
  rw [Lvm.X.EX_node _ c π L hdom hsize hb0 hb hS' αd hα α1d hα1 m hdec1EX _ hdecEX]
  unfold extS
  rw [hrd]
  simp only [Option.bind_some]
  rw [hdec1, Option.bind_some, hdec, colOf_msgOf, Lvm.X.Xwit_eq_replay, ← wOfColX_eq, ← hch q]
  unfold witOf
  rw [hhd, if_neg hbne, hfcL, hfh, hfn, hfs, hfsig]

end Lvm.ASM
