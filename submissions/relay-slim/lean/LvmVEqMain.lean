-- New for lvm (WP-14a): V_S's acceptance implies the compiled S.V's (obligation O5b, WP-14's
-- `OpenS.refines`), from the value refinement (`ref_decide`), the query correspondence (`sim`), the
-- schedule's shape (`Fol`) and its static facts (`stA_P20`).
import LvmVEqTop
import LvmVEqSim
import LvmVEqStatic
import LvmVEqParse

/-!
# V_S ⇒ S.V

**`refines_seqOf`**: for every key, statement, proof and trace, if `V_S = VSL P20 tabs` accepts the
proof on the trace, so does WP-5's compiled verifier of WP-14's `P_S = PSWith (midS tabs)`.
**`refines_logOf`/`refines_logF`** are the same on every log (the form of `OpenS.refines`): the trace
`V_S` asks on the log is answered by the log, and the compiled verifier asks the same queries.
The headline without the shape hypothesis is `LvmVEqRefines.refines_VSL`.

The proof: `V_S`'s header check gives the compiled verifier's header (`hdrS`, `okS`), its driver's
acceptance gives the stream `Σ = traceBytesB tr` on which `F` holds; `ref_decide` turns `F` into the
program `P_S x` read off `Σ` returning `true`; `sim` (with `Fol` of `P_S x` against the schedule's
atoms and `stA_P20`) runs the compiled verifier on the same trace to the same verdict.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

theorem capOfS_eq : Lvm.ASM.capOfS = capS := rfl

theorem size_q0Query : q0Query.size = 7 := rfl

theorem entOff_one (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) :
    entOff ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) 1 = 48 := by
  simp [entOff, traceBytes_cons, traceBytes_nil, length_enc64, length_blb, size_q0Query]

theorem size_seedQuery (π : ByteArray) (a₀ : Digest) (hH : headerBytes ≤ π.size) :
    (seedQuery π a₀).size = 32 + (headerBytes - 8) := by
  rw [seedQuery, ByteArray.size_append, size_digestBytes, ← length_blb, blb_extract]
  simp [length_blb]; omega

theorem entOff_two (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) (hH : headerBytes ≤ π.size) :
    entOff ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) 2 = RS.start.ent := by
  have hd1 : ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest).drop 1 = (seedQuery π a₀, st₀) :: rest := rfl
  rw [(stream_entry hd1).2.2, entOff_one, size_seedQuery π a₀ hH]
  rfl

/-- The header bytes in the stream: the seed entry holds `π`'s bytes 8…4927. -/
theorem seed_bytes (π : ByteArray) (a₀ st₀ : Digest) (rest : Trace) (hH : headerBytes ≤ π.size) :
    ∀ t < headerBytes - 8, (traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest)).get!
      (headerAt 8 + t) = π.get! (8 + t) := by
  intro t ht
  have hd1 : ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest).drop 1 = (seedQuery π a₀, st₀) :: rest := rfl
  have he := (stream_entry hd1).1 (32 + t) 1 (by rw [size_seedQuery π a₀ hH]; omega)
  rw [entOff_one, show 48 + 8 + (32 + t) = headerAt 8 + t by simp [headerAt]; omega] at he
  have hg := getD_sb (traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest)) (headerAt 8 + t) 1 0
    (by omega)
  rw [Nat.add_zero] at hg
  rw [← hg, show sb = sbs from rfl, he, get!_blb]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_zero,
    seedQuery, blb_append, blb_digestBytes, List.getElem?_append_right (by simp),
    show 32 + t - (Vector.toList a₀).length = t by simp, blb_extract, List.getElem?_take_of_lt (by omega),
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem decideF_ok {p : Params} {m : M3} {vk c : Digest} {sig : ByteArray}
    (h : decideF p m vk c sig = true) : (runD (decideProg p m vk c) sig RS.start).2.ok = true := by
  rw [decideF_eq, Bool.and_eq_true] at h
  have h1 := h.1
  unfold decideCore DM.runOn at h1
  have e : (decideProg p m vk c sig).run RS.start = runD (decideProg p m vk c) sig RS.start := rfl
  rw [e] at h1
  rcases hr : runD (decideProg p m vk c) sig RS.start with ⟨u, s⟩
  rw [hr] at h1
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1

/-- A23: `decideF` also checks the folded claim of the run (`AccOk`). -/
theorem decideF_acc {p : Params} {m : M3} {vk c : Digest} {sig : ByteArray}
    (h : decideF p m vk c sig = true) :
    AccOk p m (pubOf vk c sig) (runD (decideProg p m vk c) sig RS.start).1 = true := by
  rw [decideF_eq, Bool.and_eq_true] at h
  have h2 := h.2
  unfold accOutOf DM.runOn at h2
  have e : (decideProg p m vk c sig).run RS.start = runD (decideProg p m vk c) sig RS.start := rfl
  rw [e] at h2
  exact h2

/-! ## From traces to logs -/

/-- The trace a program asks on a log (answers by the log's first matching entry). -/
def traceOf {α : Type} (L : Log) : OProg α → Trace
  | .ret _ => []
  | .query q k => match L.find? (fun e ↦ e.1 = q) with
    | some e => (q, e.2) :: traceOf L (k e.2)
    | none => []

theorem runSeq_traceOf {α : Type} (L : Log) : ∀ (p : OProg α) {b : α}, p.runLog L = some b →
    p.runSeq (traceOf L p) = some b
  | .ret a, b, h => by simpa [OProg.runLog, traceOf, OProg.runSeq] using h
  | .query q k, b, h => by
    simp only [OProg.runLog] at h
    simp only [traceOf]
    cases he : L.find? (fun e ↦ decide (e.1 = q)) with
    | none => rw [he] at h; simp at h
    | some e =>
      rw [he] at h
      simp only [Option.bind_some] at h
      simp only [OProg.runSeq, ↓reduceIte]
      exact runSeq_traceOf L (k e.2) h

/-- Every entry of the trace a program asks on a log is the log's answer. -/
def LogCons (L : Log) (tr : Trace) : Prop :=
  ∀ e ∈ tr, ∃ e', L.find? (fun x ↦ decide (x.1 = e.1)) = some e' ∧ e'.2 = e.2

theorem logCons_traceOf {α : Type} (L : Log) : ∀ p : OProg α, LogCons L (traceOf L p)
  | .ret _ => fun e he ↦ by simp [traceOf] at he
  | .query q k => by
    intro e he
    simp only [traceOf] at he
    cases hf : L.find? (fun x ↦ decide (x.1 = q)) with
    | none => rw [hf] at he; simp at he
    | some e' =>
      rw [hf] at he
      rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨e', hf, rfl⟩
      · exact logCons_traceOf L (k e'.2) e he'

theorem runLog_of_runSeq {α : Type} (L : Log) : ∀ (p : OProg α) (tr : Trace) {b : α}, LogCons L tr →
    p.runSeq tr = some b → p.runLog L = some b
  | .ret a, tr, b, _, h => by
    rcases tr with _ | ⟨e, tr⟩
    · simpa [OProg.runSeq, OProg.runLog] using h
    · simp [OProg.runSeq] at h
  | .query q k, tr, b, hc, h => by
    rcases tr with _ | ⟨⟨q', a⟩, tr⟩
    · simp [OProg.runSeq] at h
    · simp only [OProg.runSeq] at h
      split at h
      · rename_i hq
        subst hq
        obtain ⟨e', he', he2⟩ := hc (q', a) List.mem_cons_self
        simp only [OProg.runLog, he', Option.bind_some]
        rw [he2]
        exact runLog_of_runSeq L (k a) tr (fun e he ↦ hc e (List.mem_cons_of_mem _ he)) h
      · simp at h

/-- **Acceptance on every trace transfers to every log.** -/
theorem runLog_of_seq {p q : OProg Bool} (h : ∀ tr, p.runSeq tr = some true → q.runSeq tr = some true)
    (L : Log) (hp : p.runLog L = some true) : q.runLog L = some true :=
  runLog_of_runSeq L q _ (logCons_traceOf L p) (h _ (runSeq_traceOf L p hp))

section Main

variable (tabs : Pub → List M3.Tab)

/-- **V_S ⇒ S.V on a trace**, given the program's shape and the parse facts. -/
theorem refines_seqOf (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (hw : ∀ x, ∀ t ∈ M3.sumcheckTabs (tabs (pubX x)), 0 < t.w)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith (midS tabs) x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (hhdr : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.hdrS π = some (xOf π, (π.data.toList).drop headerBytes))
    (hok : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.okS vk c (xOf π) = true)
    (hpubeq : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true → ∀ {sig : ByteArray},
      (∀ t < headerBytes - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      pubOf vk c sig = pubX (xOf π))
    (vk c : Digest) (π : ByteArray) (tr : Trace)
    (h : (VSL P20 tabs vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith (midS tabs))).V c π).runSeq tr = some true := by
  -- the header check
  unfold VSL VS at h
  by_cases hp : parseOk P20 vk c π = true
  swap
  · rw [if_neg hp] at h; exact absurd (runSeq_ret_true h).2 (by simp)
  rw [if_pos hp] at h
  have hp' := hp
  simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hp'
  have hsize : π.size = piSize P20 := hp'.1.1.1
  have hHle : headerBytes ≤ π.size := by rw [hsize, sizes_P20.1]; decide
  -- the driver: q₀, the seed, the schedule
  unfold drive at h
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons h
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItems_eq] at h2
  -- the driver's final state: the whole trace logged, the body used up, `F` on the stream
  obtain ⟨sf, n, hf1, hf2, -, -⟩ := drive_run P20 π _ _ _ rest h2
  obtain ⟨hnil, hb⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨-, hF⟩ := hb
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  have hlog : streamOf sf.log =
      traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest with htr
  set x := xOf π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpub := hpubeq hp (sig := traceBytesB tr) (seed_bytes π a₀ st₀ rest hHle)
  have hok0 : (runD (decideProg P20 (M3.real P20 tabs) vk c) (traceBytesB tr) RS.start).2.ok = true :=
    decideF_ok hF
  have hacc : AccOk P20 (M3.real P20 tabs) (pubX x)
      (runD (decideProg P20 (M3.real P20 tabs) vk c) (traceBytesB tr) RS.start).1 = true := by
    rw [← hpub]; exact decideF_acc hF
  obtain ⟨b, hb1, -, -, rfl⟩ :=
    ref_decide (traceBytesB tr) tabs vk c x hfit (hw x) hpub RS.start hok0 hacc
  obtain ⟨⟨b0, rs'⟩, hivp⟩ : ∃ r, ivp capS shpS (Lvm.ASM.PSWith (midS tabs) x) (traceBytesB tr) RS.start = r :=
    ⟨_, rfl⟩
  rw [hivp] at hb1
  simp only at hb1
  subst hb1
  -- the simulation
  have hJ0 : J (Lvm.ASM.schemeS vk (Lvm.ASM.PSWith (midS tabs))) π tr
      ⟨headerBytes, headerBytes, st₀, [(seedQuery π a₀, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop headerBytes) RS.start 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_two π a₀ st₀ rest hHle).symm,
      by show 0 = headerBytes - headerBytes; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    sim (S := Lvm.ASM.schemeS vk (Lvm.ASM.PSWith (midS tabs))) (π := π) (tr := tr) (p := P20)
      rfl rfl rfl capOfS_eq (atomsOf P20 (schedule P20)) (Lvm.ASM.PSWith (midS tabs) x) [] _ _ st₀ [] []
      _ RS.start 2 [] [] _ true rs' (hfol x) (by simpa using stA_P20) hJ0 rfl
      (fun _ h ↦ by simp at h)
      (fun s'' m hm ↦ by
        obtain ⟨-, hb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        rw [hb.1])
      h2 hivp
  obtain ⟨hnil', hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hbody' : body' = [] := by
    rw [hJ'.body, hb'.1, List.drop_eq_nil_iff, length_blb]
  -- the compiled verifier
  have hx5616 : x.length = Lvm.ASM.hdrLen := by
    rw [hx, xOf, List.length_take, List.length_drop, length_blb]
    simp only [Lvm.ASM.hdrLen]; omega
  have hseed : toQ (a₀.toList ++ x) = seedQuery π a₀ := by
    apply toQ_eq
    rw [seedQuery, blb_append, blb_digestBytes, blb_extract, hx, xOf]
    rfl
  have hqc : 32 + x.length ≤ queryCap := by rw [hx5616]; decide
  set S := Lvm.ASM.schemeS vk (Lvm.ASM.PSWith (midS tabs)) with hSdef
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop headerBytes) := hhdr hp
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okS vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [hok hp]; simp [hqc]
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ from hseed, runSeq_query_eq,
    show S.P x = Lvm.ASM.PSWith (midS tabs) x from rfl, run_eq_runK,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

/-- **V_S ⇒ S.V on every log** (WP-14's `OpenS.refines` form), given the program's shape and the
parse facts. -/
theorem refines_logOf (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (hw : ∀ x, ∀ t ∈ M3.sumcheckTabs (tabs (pubX x)), 0 < t.w)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith (midS tabs) x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (hhdr : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.hdrS π = some (xOf π, (π.data.toList).drop headerBytes))
    (hok : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true →
      Lvm.ASM.okS vk c (xOf π) = true)
    (hpubeq : ∀ {vk c : Digest} {π : ByteArray}, parseOk P20 vk c π = true → ∀ {sig : ByteArray},
      (∀ t < headerBytes - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      pubOf vk c sig = pubX (xOf π)) :
    ∀ (vk : Digest) (L : Log) (c : Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VSL P20 tabs vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith (midS tabs))).V c π).runLog L = some true :=
  fun vk L c π _ h ↦ runLog_of_seq
    (fun tr ht ↦ refines_seqOf tabs hfit hw hfol hhdr hok hpubeq vk c π tr ht) L h

/-- **V_S ⇒ S.V on every log** (O5b, WP-14's `OpenS.refines`), given the program's shape against
the schedule. -/
theorem refines_logF (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (hw : ∀ x, ∀ t ∈ M3.sumcheckTabs (tabs (pubX x)), 0 < t.w)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith (midS tabs) x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True) :
    ∀ (vk : Digest) (L : Log) (c : Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VSL P20 tabs vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith (midS tabs))).V c π).runLog L = some true :=
  refines_logOf tabs hfit hw hfol (fun h ↦ hdrS_of_parseOk h) (fun h ↦ okS_of_parseOk h)
    (fun h _ hs ↦ pubOf_eq_pubX h hs)

end Main

end Lvm.VEq
