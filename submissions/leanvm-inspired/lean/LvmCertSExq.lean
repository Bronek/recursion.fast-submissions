-- WP-14d (EXQ). New for lvm (O5c): WP-13a's extractor `EX` returns the specification extractor's
-- witness (`S.Ex K.ext`, `kcertS`'s extraction `extS`) on accepted `S` proofs over logs of potential
-- below 1, or else a witness of the relation (FR's search outside the domain). The replay's history
-- (`final_good`) is cut by `accept_split`; the roots and the middle phases' kinds (`MidFollows`) put
-- every sample and the residual at the schedule's offsets (`trun_simK`, `simK_chain`), so the
-- decoder's inputs are equal (bridges (a)–(d)); WP-13b's decoder succeeds there (`decode_S`).
import LvmSubmissionS
import LvmCertSExqCodec
import LvmCertSExqRun

/-!
# O5c: `EX = S.Ex K.ext` on good logs

**`ext_eq_S`**: for `mid` with `MidSpec`, `MidShape`, `MidFollows` (WP-14a, the middle phases'
event kinds are the schedule's) and `child` of WP-13a's form (`ChildX`, WP-14c's `childS`):
on an accepted `'S'` proof over a log with `μ K L < 1`, `EXt tabs = S.Ex K.ext` or `EXt tabs` returns a
witness (an `S` node outside the extractor's domain: the search).

Cases (`b` = π word 1): `b = 0`: `EX_leaf` and the header bridge; `b ≠ 0` outside the domain:
`EX_node_out` and `search_spec_acc` from `K.extract`; `b ≠ 0` in the domain: `EX_node` with
* the chain answers `fmAns (fsQL π)` at positions `1308 … 1313` = the replay's fold samples
  (`simK_chain` on the kinds after the roots; `fsPre_P20`: the schedule's slices);
* `readWd L (capRec π)` = `C_rec`'s committed word (`readRow_eq_wordOf`, `capRec_eq`);
* `f1E π` = the replay's residual (`simK_reads`, `f1E_eq`, `f1_off`);
* `decodeRec` on these succeeds (`decode_S`), and `Xwit` is `witOf x (child q)` (header bridge).
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
pending. -/
theorem roots_trun {vk : RecursionFast.Digest} {mid : List UInt8 → VerifierProgram OpenClaims}
    {x : List UInt8} {L : Log} {B : List UInt8} {st : RecursionFast.Digest} {h : List Ev}
    (e : (schemeS vk (PSWith mid)).trun L (PSWith mid x) st [] [] (B.drop 5624) [] = some (true, h)) :
    ∃ k caps rest, h = [Ev.commit 19 64 ((schemeS vk (PSWith mid)).wordOf L
        ((schemeS vk (PSWith mid)).capI 19 64 (B.drop 5624))),
        Ev.commit 15 64 ((schemeS vk (PSWith mid)).wordOf L
          ((schemeS vk (PSWith mid)).capI 15 64 (B.drop 13816)))] ++ rest ∧
      (schemeS vk (PSWith mid)).trun L k st (sl B 5624 (17912 - 5624)) caps (B.drop 17912)
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
  exact ⟨k, _, rest, by rw [← hrest], e⟩

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

/-! ## The schedule's slices (P20, by evaluation) -/

/-- The items of `C_rec`'s opening up to the residual: `ρ`, the intro round, six fold rounds. -/
def recHead : List Item :=
  [.sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2]

/-- Byte offset after items of reads and samples. -/
def offI : List Item → ℕ → ℕ
  | [], off => off
  | .read m :: its, off => offI its (off + 24 * m)
  | _ :: its, off => offI its off

theorem offK_reads_append (ks : List EvK) : ∀ (m off : ℕ),
    offK (List.replicate m .read ++ ks) off = offK ks (off + 24 * m)
  | 0, off => rfl
  | m + 1, off => by
    rw [List.replicate_succ, List.cons_append, offK, offK_reads_append ks m]
    congr 1
    ring

theorem offK_eq_offI : ∀ (its : List Item) (off : ℕ), RSItems its = true →
    offK (itemKinds its) off = offI its off
  | [], _, _ => rfl
  | .read m :: its, off, h => by
    rw [itemKinds, offK_reads_append, offK_eq_offI its _ h]
    rfl
  | .sample :: its, off, h => by
    rw [itemKinds]
    exact offK_eq_offI its off h
  | .cap _ _ :: _, _, h => by simp [RSItems] at h
  | .positions _ :: _, _, h => by simp [RSItems] at h
  | .opening _ :: _, _, h => by simp [RSItems] at h

/-- **The schedule at P20** (one kernel evaluation): the middle phases and `C_rec`'s head are reads
and samples; their slices from the roots' end are the chain's messages of positions `2 … 1313`;
the residual starts at `f1Off`; the middle phases draw `1305` samples. -/
theorem sched_P20 : RSItems (midItems ++ recHead) = true ∧
    Lvm.X.fsPre P20 (midItems ++ recHead) 17912 5624 = ((Lvm.X.fsMsgs P20).drop 1).take 1312 ∧
    offI (midItems ++ recHead) 17912 = Lvm.X.f1Off P20 ∧
    (itemKinds midItems).count .sample = 1305 ∧ Lvm.X.f1Off P20 = 229352 ∧
    (Lvm.X.fsMsgs P20).getD 0 (0, 0) = (8, 5616) := by
  decide +kernel

/-- (−) **`MidFollows` is not vacuous**: middle phases that return at once do not follow the
schedule. -/
theorem not_midFollows_ret : ¬ MidFollows fun _ ↦ (VerifierProgram.ret (([], []) : OpenClaims)) := by
  intro h
  have e := h [] [] ([], []) rfl
  have c := sched_P20.2.2.2.1
  rw [← e] at c
  simp at c

theorem itemKinds_append : ∀ (a b : List Item), itemKinds (a ++ b) = itemKinds a ++ itemKinds b
  | [], b => rfl
  | .read m :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.append_assoc]
  | .sample :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b, List.cons_append]
  | .cap _ _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]
  | .positions _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]
  | .opening _ :: a, b => by simp only [List.cons_append, itemKinds, itemKinds_append a b]

theorem itemKinds_recHead :
    itemKinds recHead = [.sample, .read, .read] ++ (List.replicate 6 [EvK.sample, .read, .read]).flatten :=
  rfl

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

/-! ## O5c -/

theorem bitsToNat_symm (v : ℕ) (hv : v < 2 ^ 13) :
    bitsToNat ((bitsEquiv 13).symm ⟨v, hv⟩) = v := by
  rw [← bitsEquiv_val, Equiv.apply_symm_apply]

open Classical in
/-- **O5c** for `EXt tabs` (lvm2 S2-CERT: generic in the node program's tables; v1's `EX20`): on
an accepted `'S'` proof over a log of potential below `1`, WP-13a's
`EX` is the specification extractor of `kcertS` (WP-13b's decoder on the replayed history), or
returns a witness of the relation. Hypotheses beyond `kcertS`'s: the middle phases' event kinds
(`MidFollows`, WP-14a) and the child's form (`ChildX`, WP-14c's `childS`). -/
theorem ext_eq_S {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}
    (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {tabs : Lvm.Pub → List Lvm.M3.Tab}
    {child : Column 19 → Signed} (hnode : ∀ vk, NodeSound (Lvm.T.VSt tabs) vk Good child)
    (hch : ChildX child) (hfol : MidFollows mid) (vk : RecursionFast.Digest) (L : Log)
    (c : RecursionFast.Digest) (π : RecursionFast.Proof) (_hS : isS π = true)
    (_hl : L.length ≤ logCap)
    (hμ : Scheme.μ (kcertS hmid hLm hsh (hnode vk)) L < 1)
    (hacc : ((schemeS vk (PSWith mid)).V c π).runLog L = some true) :
    (∃ w, Lvm.T.EXt tabs c π L = some w ∧ Rel (accV (Lvm.T.VSt tabs) vk) c w) ∨
      Lvm.T.EXt tabs c π L = (schemeS vk (PSWith mid)).Ex (kcertS hmid hLm hsh (hnode vk)).ext c π L := by
  obtain ⟨x, h, hok, hreach, hafter, hB, hBp, hD, hEx⟩ :=
    Scheme.final_good (kcertS hmid hLm hsh (hnode vk)) L c π hμ hacc
  obtain ⟨body, e₀, e₁, hhdr, h0, h1, htr⟩ := Ex_inv _ hEx
  obtain ⟨hsz, hpre8, rfl, rfl⟩ := hdrS_inv hhdr
  have hsize : π.size = Lvm.piSize Lvm.X.pX := hsz
  have hpi : π.size = 1094248 := by rw [hsize]; exact Lvm.X.piSize_eq
  have hBlen : π.data.toList.length = π.size := Array.length_toList
  have hb0 : π.data[0]? = some 0x53 := byte0_of_prefix hpre8
  have hhd : hdrOf ((π.data.toList.drop 8).take hdrLen) = Header.ofProof π :=
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
    rw [Lvm.T.EXt, Lvm.X.EX_leaf _ c π L hsize hb0 hb]
    unfold extS witOf
    rw [hhd, if_pos (by rw [hfb, hb]; rfl), hfs, hfn]
    rfl
  have hbne : (Header.ofProof π).b ≠ 0 := by
    rw [hfb]; intro h0'; exact hb (BitVec.eq_of_toNat_eq (by rw [h0']; rfl))
  by_cases hdom : Lvm.X.InDomE c π L
  swap
  · -- a node outside the domain: the search
    left
    rw [Lvm.T.EXt, Lvm.X.EX_node_out _ c π L hdom hsize hb0 hb]
    have hvk : Lvm.X.hdD π 2 = vk := by
      have := hok
      simp only [schemeS, okS, Bool.and_eq_true, beq_iff_eq] at this
      rw [← hfvk, ← hhd]
      exact this.1.1.1.2
    rw [hvk]
    refine Lvm.X.search_spec_acc (fun c' p hp => Lvm.X.sFits_of_acc (S := Lvm.T.submissionT tabs)
      (by show Lvm.T.qVlvm ≤ Lvm.X.qMax; decide)
      (by rw [show (Lvm.T.submissionT tabs).acc = accV (Lvm.T.VSt tabs) from
        subWith_acc (Lvm.T.VSt tabs) (Lvm.T.EXt tabs) Lvm.X.extX]; exact hp))
      ⟨_, (kcertS hmid hLm hsh (hnode vk)).extract hok hreach hafter hB hBp hD⟩
  -- a node in the domain
  right
  have hS' : ¬ Lvm.X.StateHit L := Lvm.X.notStateHit_of_notBad (Scheme.mu_lt_one hμ).1
  obtain ⟨hr, lm, cl, ρ, lq, quad, lf, r, lres, res, rest, hsplit, h1r, h3, h8, h10, h12⟩ :=
    accept_split hafter
  obtain ⟨W₁, W₂, rfl⟩ := roots_after h1r
  have htr' : (schemeS vk (PSWith mid)).trun L (PSWith mid ((π.data.toList.drop 8).take hdrLen)) e₁.2
      [] [] (π.data.toList.drop 5624) [] = some (true, h) := htr
  obtain ⟨k, caps, rest₀, hh, htrk⟩ := roots_trun htr'
  rw [hsplit] at hh
  simp only [List.cons_append, List.nil_append, List.cons.injEq, Ev.commit.injEq, true_and] at hh
  obtain ⟨rfl, rfl, -⟩ := hh
  -- the kinds of the history up to the residual
  have hRS := sched_P20.1
  have fm : lm.map kindOf = itemKinds midItems := hfol _ lm cl h3
  have fq : lq.map kindOf = [.read, .read] := roundPoly_kinds h8
  have ff := foldRoundsT_kinds 6 _ _ h10
  obtain ⟨e1r, e2r, e3r, -, -⟩ := foldRoundsT_after 6 _ [] h10
  rw [List.nil_append] at e1r e3r
  have hlen6 : r.2.length = 6 := by rw [e1r]; exact e2r
  have hfl : r.1.folds.length = 6 := by rw [e3r]; exact e2r
  have hres := readScalars_after_eq _ h12
  have hreslen : res.length = 2 ^ 13 := by rw [readScalars_after_len _ h12, hfl]
  have hk1 : (lm ++ ([Ev.sample ρ] ++ (lq ++ lf))).map kindOf = itemKinds (midItems ++ recHead) := by
    rw [itemKinds_append, itemKinds_recHead, List.map_append, List.map_append, List.map_append, fm, fq,
      ff]
    rfl
  -- the replay up to the residual, then the residual
  obtain ⟨st₁, p₁, caps₁, hsim1, hle1, htr1⟩ := trun_simK _ L π.data.toList _ k 17912 5624 e₁.2 caps _
    (lm ++ ([Ev.sample ρ] ++ (lq ++ lf))) (lres ++ rest) true (other_not_mem _ hRS) (by norm_num) hk1
    (by rw [htrk, hsplit]; simp only [List.append_assoc, List.cons_append, List.nil_append])
  have hoff1 : offK (itemKinds (midItems ++ recHead)) 17912 = 229352 := by
    rw [offK_eq_offI _ _ hRS, sched_P20.2.2.1, sched_P20.2.2.2.2.1]
  have hk2 : lres.map kindOf = List.replicate (2 ^ 13) .read := by
    rw [hres, List.map_map, ← hreslen]
    show List.map (fun _ => EvK.read) res = _
    exact List.map_const'
  obtain ⟨st₂, -, -, hsim2, -, -⟩ := trun_simK _ L π.data.toList _ p₁ _ _ st₁ caps₁ _ lres rest true
    (fun hm => by cases (List.mem_replicate.1 hm).2) hle1 hk2 (by rw [htr1]; simp only [List.append_assoc])
  rw [simK_reads, hoff1] at hsim2
  have hresv : res = (List.range (2 ^ 13)).map fun i => eOfBytes (sl π.data.toList (229352 + 24 * i) 24) := by
    have e := (Prod.mk.inj (Option.some.inj hsim2)).1
    rw [hres] at e
    apply List.map_injective_iff.2 (fun a b hab => Ev.read.inj hab)
    rw [← e, List.map_map]
    rfl
  -- the chain
  have hfm1 : Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L 1 = some e₁.2 := by
    have hq0 : Lvm.X.fsQL π 0 Lvm.X.zeroDL = toQ (schemeS vk (PSWith mid)).q0 := rfl
    have hseed : Lvm.X.fsQL π 1 e₀.2 =
        (schemeS vk (PSWith mid)).seedQ e₀.2 ((π.data.toList.drop 8).take hdrLen) := by
      rw [fsQL_eq π (by norm_num), msgL_eq, show 1 - 1 = 0 from rfl, sched_P20.2.2.2.2.2]
      rfl
    simp only [Lvm.X.fmAns, hq0, h0, Option.map_some, Option.bind_some, hseed, h1]
  have hPre : fsPreK (itemKinds (midItems ++ recHead)) 17912 5624 =
      ((Lvm.X.fsMsgs P20).drop 1).take 1312 := by
    rw [← fsPre_eq_fsPreK _ _ _ _ hRS]
    exact sched_P20.2.1
  obtain ⟨hch1, -⟩ := simK_chain _ L π.data.toList (Lvm.X.fsQL π) Lvm.X.zeroDL _ 17912 5624 e₁.2 1 _ st₁
    hsim1 hfm1 (fun i hi s => by
      rw [fsQL_eq π (by omega), msgL_eq, ← List.getD_eq_getElem _ (0, 0) hi, hPre]
      have hi' : i < 1312 := by
        have := hi
        rw [hPre] at this
        exact lt_of_lt_of_le this (List.length_take_le _ _)
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi',
        List.getElem?_drop, show 1 + 1 + i - 1 = 1 + i by omega])
  have hlm : (lm.filterMap sampleOf).length = 1305 := by
    rw [samples_length, fm]; exact sched_P20.2.2.2.1
  have hlq : lq.filterMap sampleOf = [] := by
    have := samples_length lq
    rw [fq] at this
    exact List.length_eq_zero_iff.1 (by simpa using this)
  have hpreS : (lm ++ ([Ev.sample ρ] ++ (lq ++ lf))).filterMap sampleOf =
      lm.filterMap sampleOf ++ (ρ :: r.2) := by
    simp only [List.filterMap_append, hlq, e1r, List.nil_append]
    rfl
  have hfold : ∀ j < 6, ∃ a, Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alphaPos Lvm.X.pX j) =
      some a ∧ r.2.getD j 0 = chalOf a := by
    intro j hj
    have hlen : 1306 + j < ((lm ++ ([Ev.sample ρ] ++ (lq ++ lf))).filterMap sampleOf).length := by
      rw [hpreS, List.length_append, hlm, List.length_cons, hlen6]; omega
    obtain ⟨a, ha, hea⟩ := hch1 (1306 + j) hlen
    refine ⟨a, by rw [Lvm.X.alphaPos_eq, show 1308 + j = 1 + 1 + (1306 + j) by omega]; exact ha, ?_⟩
    rw [show chalOf a = (schemeS vk (PSWith mid)).chal a from rfl, ← hea,
      ← List.getD_eq_getElem _ 0 hlen, hpreS, List.getD_append_right _ _ _ _ (by omega), hlm,
      show 1306 + j - 1305 = j + 1 by omega]
    rfl
  -- the decoder
  let αd : ℕ → RecursionFast.Digest := fun j => if j < 6 then
    (Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alphaPos Lvm.X.pX j)).getD Lvm.X.zeroDL
    else Lvm.X.zeroDL
  have hα : ∀ j < 6, Lvm.X.fmAns (Lvm.X.fsQL π) Lvm.X.zeroDL L (Lvm.X.alphaPos Lvm.X.pX j) =
      some (αd j) := by
    intro j hj
    obtain ⟨a, ha, -⟩ := hfold j hj
    simp only [αd, if_pos hj, ha, Option.getD_some]
  obtain ⟨qm, q, -, r', res', hrd, hdec⟩ := decode_S hmid hLm hsh hreach hafter hB hD
  have hrd' := recData_split (rest := rest) h1r h3 h8 h10 h12
  rw [← hsplit, hrd] at hrd'
  obtain ⟨rfl, rfl⟩ : r = r' ∧ res = res' := by simpa [eq_comm] using hrd'
  have hWr : WrOf h = (schemeS vk (PSWith mid)).wordOf L ⟨15, 64, 7, Lvm.X.capRec π⟩ := by
    rw [hsplit]
    unfold WrOf
    rw [rootsOf_split h1r, ← capRec_eq vk (PSWith mid) π (by omega)]
    rfl
  have hdecEX : Lvm.X.decodeRec (Lvm.X.readWd L (Lvm.X.capRec π)) (fun i => Lvm.X.alphaE (αd i))
      (Lvm.X.f1E π) = some ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)) := by
    have ew : Lvm.X.readWd L (Lvm.X.capRec π) = Lvm.X.wdOf (WrOf h) := by
      funext p' t
      rw [hWr]
      unfold Lvm.X.readWd Lvm.X.wdOf
      rw [readRow_eq_wordOf (schemeS vk (PSWith mid)) rfl]
    have ea : (fun i => Lvm.X.alphaE (αd i)) = Lvm.X.alphaN fun i ↦ r.2.getD i 0 := by
      funext i
      unfold Lvm.X.alphaN
      split_ifs with hi
      · obtain ⟨a, ha, hra⟩ := hfold i hi
        simp only [αd, if_pos hi, ha, Option.getD_some]
        rw [hra, chalOf_eq_alphaE]
      · simp only [αd, if_neg hi]
        exact alphaE_zero
    rw [ew, ea, decodeRec_congr_f _ _ (f' := Lvm.X.fNr (resMsg res)) ?_]
    · exact hdec
    · intro v hv
      have hf1 : Lvm.X.f1Off Lvm.X.pX = 229352 := sched_P20.2.2.2.2.1
      rw [f1E_eq π v (by rw [hf1, hpi]; omega), hf1]
      unfold Lvm.X.fNr
      rw [dif_pos hv]
      unfold resMsg
      erw [bitsToNat_symm v hv]
      rw [hresv, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
        List.getElem_map, List.getElem_range]
      rfl
  -- the witness
  rw [Lvm.T.EXt, Lvm.X.EX_node _ c π L hdom hsize hb0 hb hS' αd hα _ hdecEX]
  unfold extS
  rw [hrd]
  simp only [Option.bind_some]
  rw [hdec, colOf_msgOf, Lvm.X.Xwit_eq_replay, ← wOfColX_eq, ← hch q]
  unfold witOf
  rw [hhd, if_neg hbne, hfcL, hfh, hfn, hfs, hfsig]

end Lvm.ASM
