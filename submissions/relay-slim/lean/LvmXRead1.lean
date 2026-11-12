-- lvm2 X-REC2 (helper DEC): the semantics of the level-1 column reads. Adapted from this entry's
-- `LvmXRead.lean`/`LvmXRead2.lean` (v1's `cr_capLd_sem`, `cr_nodeLoop`, `cr_copy_sem`, `cr_pos_sem`,
-- `cr_posLoop`, `readIR_sem4`, `readIR_sem`, `readIR_readWd`) at tree (12, 48, 7).
import LvmXRead1Defs

/-!
# `read1IR_sem`: the level-1 column reads compute `readRow1`

After the index (`idxIR4`), `read1IR bX pL capW wB` stores `readRow1 L cap p` at `wB + 48p + t`
(`p < 2^12`, `t < 48`); the index and the heap outside `[wB, wB + 48·2^12)` are kept.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## The pure reading at level 1 -/

/-- The reading under a cap node `d0` after `n` steps down: the leaf's bytes. -/
def crRdN (n : ℕ) (L : Log) (d0 : Digest) (p : ℕ) : Option (List UInt8) :=
  (xDescend L n d0 p).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- On a position of the level-1 tree, the leaf bytes are the reading under its cap node. -/
theorem xLeafBytes1_eq {L : Log} {cap : List Digest} {p : ℕ} (hp : p < 2 ^ 12)
    (hpc : p / 32 < cap.length) :
    xLeafBytes1 L cap p = crRdN 5 L (cap[p / 32]'hpc) p := by
  unfold xLeafBytes1 crRdN
  rw [Nat.mod_eq_of_lt hp, show (2 : ℕ) ^ (12 - 7) = 32 from rfl, List.getElem?_eq_getElem hpc]
  all_goals rfl

theorem readRow1_getD (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 48) :
    (readRow1 L cap p).getD t 0 =
      decLE ((((xLeafBytes1 L cap p).getD []).drop (8 * t)).take 8) := by
  rw [List.getD_eq_getElem _ _ (by rw [readRow1_length]; exact ht)]
  simp [readRow1, xRowOf]

/-- **The stored word as a `K` element is the level-1 row's word.** -/
theorem crLeafW_readRow1 (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 48) :
    wK (crLeafW (xLeafBytes1 L cap p) t) = (readRow1 L cap p).getD t 0 := by
  rw [wK_crLeafW, readRow1_getD L cap p ht]

/-! ## The cap node at level 1 -/

/-- **The cap node's words**: after `cr1CapPs ; crLd4`, `rQ0 … rQ3` hold `cap[p / 32]`. -/
theorem cr1_capLd_sem (I : Array Word) (s : St) (hM : Inv s.M) {capW : ℕ} {cap : List Digest}
    (hcw : capW + 4 * cap.length < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      I.getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p : ℕ} (hp : p < 2 ^ 62) (he : p / 32 < cap.length) (hP : rd s.M crP = toWord p) :
    [rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M rQ0,
      rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M rQ1,
      rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M rQ2,
      rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M rQ3] =
      packBytes (cap[p / 32]'he).toList := by
  have hs := hM.1
  simp only [regs] at hs
  have hw : WF (.blk (cr1CapPs capW)) := by simp +decide only [cr1CapPs, WF, Prim.dst, crK, crB,
    crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hA : rd (semXIR I (.blk (cr1CapPs capW)) s).M crTA = toWord (capW + 4 * (p / 32)) := by
    simp only [cr1CapPs, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hP, show (5 : Word) = toWord 5 from rfl, shr_toWord (by omega) (by norm_num),
      show (2 : Word) = toWord 2 from rfl, shl_toWord (by norm_num) (by omega), add_toWord]
    congr 1
    omega
  rw [semXIR_seq, cr_ld4_sem _ _ (inv_sem _ hw hM) (by omega) hA, cr_pk_digest_eq4,
    ← hcap _ he 0 (by decide), ← hcap _ he 1 (by decide), ← hcap _ he 2 (by decide),
    ← hcap _ he 3 (by decide)]
  simp only [Nat.add_zero]

/-! ## The walk of `n` steps -/

/-- **The walk's state at height `h`** for a walk of `n` steps from the cap node `d₀` (v1's
`crWalk` at `n = 8`). -/
def crWalkN (n : ℕ) (L : Log) (d0 : Digest) (p h : ℕ) (M : Mem) : Prop :=
  (rd M crOk = 1 ∧ ∃ d : Digest, [rd M rQ0, rd M rQ1, rd M rQ2, rd M rQ3] = packBytes d.toList ∧
    xDescend L n d0 p = xDescend L h d p) ∨
  (rd M crOk = 0 ∧ xDescend L n d0 p = none)

section Read1

variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One node step keeps the walk's state**, one level down. -/
theorem cr_nodeWalkN (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {n : ℕ} {d0 : Digest}
    {p h : ℕ} (hp : p < 2 ^ 62) (hh : h + 1 < 64) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) (hW : crWalkN n L d0 p (h + 1) s.M) :
    crWalkN n L d0 p h (semXIR (crTape c π L) (crNode bX pL) s).M := by
  rcases hW with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · obtain ⟨n1, n2⟩ := cr_node_sem hbX hbX2 hpL hD hX s hM hXs hp hh hP hH hOk hT
    rw [xDescend_succ L h d p] at hc
    cases hn : xStep L p h d with
    | none =>
      rw [hn] at hc
      exact .inr ⟨n2 hn, hc⟩
    | some d' =>
      rw [hn] at hc
      obtain ⟨o1, o2⟩ := n1 d' hn
      exact .inl ⟨o1, d', o2, hc⟩
  · have e : semXIR (crTape c π L) (crNode bX pL) s = s := by
      rw [crNode, semXIR_ite, hOk, if_pos rfl]; rfl
    rw [e]; exact .inr ⟨hOk, hc⟩

/-- **The height loop**: `m` node steps from height `m` reach height `0`; the heap, `crP` and
`crWA` are kept. -/
theorem cr_nodeLoopN (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {n : ℕ} {d0 : Digest} {p : ℕ} (hp : p < 2 ^ 62) :
    ∀ (m : ℕ) (s : St), m < 64 → Inv s.M → (∀ a < L.length, rd s.M (bX + a) = Xi a) →
      rd s.M crP = toWord p → rd s.M crHc = toWord m → crWalkN n L d0 p m s.M →
      crWalkN n L d0 p 0 (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      Inv (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      (∀ x, regs ≤ x → rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M x = rd s.M x) ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crP = rd s.M crP ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crWA = rd s.M crWA
  | 0, s, _, hM, _, _, _, hW => ⟨hW, hM, fun _ _ => rfl, rfl, rfl⟩
  | m + 1, s, hm, hM, hXs, hP, hH, hW => by
    set I := crTape c π L
    have h1 := cr_nodeWalkN hbX hbX2 hpL hD hX s hM hXs (h := m) hp (by omega) hP hH hW
    have hM1 := inv_sem I (cr_wf_node (bX := bX) (pL := pL)) hM
    have hH1 := hframeK I (crNode bX pL) s cr_loK_node
    have fr : ∀ r, (r = crP ∨ r = crWA ∨ r = crHc) →
        rd (semXIR I (crNode bX pL) s).M r = rd s.M r :=
      fun r hr => frame I _ s (cr_wf_node (bX := bX) (pL := pL)) hM r
        (by rcases hr with rfl | rfl | rfl <;> decide) (cr_node_nw hr)
    have hM' : Inv (decS crHc (semXIR I (crNode bX pL) s)).M := inv_decS hM1 (by decide)
    have hHc : rd (decS crHc (semXIR I (crNode bX pL) s)).M crHc = toWord m :=
      rd_decS_self hM1 (by decide) (by rw [fr _ (.inr (.inr rfl)), hH]) (by omega)
    have dk : ∀ r, r ≠ crHc → rd (decS crHc (semXIR I (crNode bX pL) s)).M r =
        rd (semXIR I (crNode bX pL) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hW' : crWalkN n L d0 p m (decS crHc (semXIR I (crNode bX pL) s)).M := by
      unfold crWalkN at h1 ⊢
      rw [dk crOk (by decide), dk rQ0 (by decide), dk rQ1 (by decide), dk rQ2 (by decide),
        dk rQ3 (by decide)]
      exact h1
    have hHp : ∀ x, regs ≤ x → rd (decS crHc (semXIR I (crNode bX pL) s)).M x = rd s.M x :=
      fun x hx => (dk x (by simp only [crHc, regs] at *; omega)).trans (hH1 x hx)
    obtain ⟨a1, a2, a3, a4, a5⟩ := cr_nodeLoopN hD hX hp m _ (by omega) hM'
      (fun a ha => by rw [hHp _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
      (by rw [dk _ (by decide), fr _ (.inl rfl), hP]) hHc hW'
    simp only [iterL]
    refine ⟨a1, a2, fun x hx => (a3 x hx).trans (hHp x hx), ?_, ?_⟩
    · rw [a4, dk _ (by decide), fr _ (.inl rfl)]
    · rw [a5, dk _ (by decide), fr _ (.inr (.inl rfl))]

/-- **The leaf**: after `crLeaf`, `crX` and `crQe` are such that the copy stores the leaf words of
the reading under the cap node `d₀` after `n` steps (`crRdN`). -/
theorem cr_leaf_semN (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {n : ℕ} {d0 : Digest}
    {p : ℕ} (hW : crWalkN n L d0 p 0 s.M) :
    ∃ ql < 2 ^ 64, rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crQe = toWord ql ∧
      ∀ t, crCpW (crTape c π L) (rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crX) ql t =
        crLeafW (crRdN n L d0 p) t := by
  set I := crTape c π L with hI
  have hs := hM.1
  simp only [regs] at hs
  rw [crLeaf, semXIR_seq]
  have hM0 := inv_sem I (P := .blk [.const crQe 0]) (by simp +decide only [WF, Prim.dst, crQe]) hM
  have hQ0 : rd (semXIR I (.blk [.const crQe 0]) s).M crQe = toWord 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [crQe]; omega)
  have fr0 : ∀ r, r ≠ crQe → rd (semXIR I (.blk [.const crQe 0]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  have hXs0 : ∀ a < L.length, rd (semXIR I (.blk [.const crQe 0]) s).M (bX + a) = Xi a :=
    fun a ha => by rw [fr0 _ (by simp only [crQe, regs] at hbX ⊢; omega), hXs a ha]
  have hW0 : crWalkN n L d0 p 0 (semXIR I (.blk [.const crQe 0]) s).M := by
    unfold crWalkN at hW ⊢
    rw [fr0 crOk (by decide), fr0 rQ0 (by decide), fr0 rQ1 (by decide), fr0 rQ2 (by decide),
      fr0 rQ3 (by decide)]
    exact hW
  generalize semXIR I (.blk [.const crQe 0]) s = s0 at hM0 hQ0 hXs0 hW0
  have hs0 := hM0.1
  simp only [regs] at hs0
  rw [semXIR_ite]
  rcases hW0 with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · rw [hOk, if_neg (by decide), semXIR_seq]
    have hrd : crRdN n L d0 p = (xFindA L d).map fun e => xQb e.1 := by
      rw [crRdN, hc]; rfl
    rw [hrd]
    obtain ⟨lk1, lk2, lk3, lk4, lk5⟩ := cr_look_spec hbX hbX2 hpL hD hX s0 hM0 hXs0 d hT
    have hQ1 := (lk5 crQe (by decide) (by decide)).trans hQ0
    generalize semXIR I (lookIR4 bX pL) s0 = s1 at lk1 lk2 lk3 lk4 hQ1
    have hs1 := lk4.1
    simp only [regs] at hs1
    rw [semXIR_ite]
    cases hk : ansIdx L d with
    | none =>
      rw [lk2 hk, if_pos rfl, xFindA_none hk]
      refine ⟨0, by norm_num, hQ1, fun t => ?_⟩
      simp [crCpW_zero, crLeafW_none]
    | some k =>
      obtain ⟨b, hb, hlo, hfd, hxb⟩ := lk1 k hk
      obtain ⟨hkL, hpre⟩ := xFindA_some hk
      rw [hfd, if_neg (by decide), hpre, Option.map_some]
      have hxl := hD.posE_lt hkL
      have hsm := hD.small
      have hq := hD.hq _ (List.getElem_mem hkL)
      obtain ⟨g1, g2⟩ := cr_get_sem hbX hbX2 hpL I s1 lk4 (b := b) (x := posE4 pL L k) (by omega)
        (by omega) hlo (by rw [lk3 _ (by simp only [regs] at hbX ⊢; omega), hXs0 b hb, hxb])
      have hM2 := inv_sem I (cr_wf_get (bX := bX)) lk4
      rw [semXIR_seq]
      generalize semXIR I (crGet bX) s1 = s2 at g1 g2 hM2
      have hs2 := hM2.1
      simp only [regs] at hs2
      refine ⟨L[k].1.size, hq, ?_, fun t => ?_⟩
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_self (by simp only [crQe]; omega), g2, cr_tp_len hD hkL, or_self_eval]
      · have e : rd (semXIR I (.blk [.op .or crQe crQn crQn]) s2).M crX =
            toWord (posE4 pL L k) := by
          simp only [semXIR, runPrims, List.foldl, Prim.run]
          rw [rd_set_ne (by decide), g1]
        rw [e, cr_cpW_entry hD hkL t]
  · rw [hOk, if_pos rfl]
    have hrd : crRdN n L d0 p = none := by rw [crRdN, hc]; rfl
    rw [hrd]
    refine ⟨0, by norm_num, by
      show rd (runPrims [] s0.M) crQe = _
      rw [runPrims_nil, hQ0], fun t => ?_⟩
    rw [crCpW_zero, crLeafW_none]

end Read1

/-! ## The copy of 48 words -/

theorem cr1_wf_copy : WF cr1Copy := by
  simp +decide only [cr1Copy, crCopyBody, WF, Writes, Prim.dst, crV, crMk, crK, crWA, crTA, cr8,
    crNw, crCw, crX, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

/-- **The copy**: from `crX = x`, `crQe = ql`, `crWA = a`, cells `a … a + 47` get
`crCpW I x ql ·`; every other heap cell is kept; `crWA` ends at `a + 48`. -/
theorem cr1_copy_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a) (ha2 : a + 48 + 2 < 2 ^ 64) (hsz : a + 48 ≤ s.M.size)
    (hX : rd s.M crX = x) (hQ : rd s.M crQe = toWord ql) (hA : rd s.M crWA = toWord a) :
    (∀ i < 48, rd (semXIR I cr1Copy s).M (a + i) = crCpW I x ql i) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 48 ≤ y) → rd (semXIR I cr1Copy s).M y = rd s.M y) ∧
    Inv (semXIR I cr1Copy s).M ∧ rd (semXIR I cr1Copy s).M crWA = toWord (a + 48) ∧
    rd (semXIR I cr1Copy s).M crP = rd s.M crP := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have wf0 : WF (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)]) := by
    simp +decide only [WF, Prim.dst, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I wf0 hM
  have hH0 := hframe I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)]) s
    (by simp +decide only [Lo, Prim.dst, regs, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hsz0 := size_sem I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)]) s
  have r0 : rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crTA = x + toWord (1 + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M cr8 = toWord (8 * 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crNw = toWord 48 ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crQe = toWord ql ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crWA = toWord (a + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crP = rd s.M crP := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crTA, cr8, crNw]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hQ | exact hA | (rw [hX, h1]; all_goals rfl)
  rw [cr1Copy, semXIR_seq]
  generalize semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
    s = s0 at hM0 hH0 hsz0 r0
  obtain ⟨t0, e0, n0, q0, a0, p0⟩ := r0
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp → rd (entryK crCw crNw (toWord 48) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCw crNw (toWord 48) s0.M) crCw = toWord 48 :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCw) (n := crNw) (K := toWord 48) hM0 (by decide)
  have e : semXIR I (.loopK crCw crNw (toWord 48) crCopyBody) s0 =
      iterL (semXIR I crCopyBody) crCw 48 ⟨entryK crCw crNw (toWord 48) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 48 < 2 ^ 64 by norm_num)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ cTmp := fun y hy => by
    simp only [crCw, cTmp, regs] at *; omega
  obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I hql ha ha2 (by norm_num) 48 0
    ⟨entryK crCw crNw (toWord 48) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega) (by rw [hE _ (by decide) (by decide), a0])
    (by rw [hE _ (by decide) (by decide), t0]) (by rw [hE _ (by decide) (by decide), e0])
    (by rw [hE _ (by decide) (by decide), q0])
  refine ⟨fun i hi => d1 i (by omega) (by omega), fun y hy1 hy2 => ?_, d3,
    by rw [d4, Nat.zero_add], ?_⟩
  · rw [d2 y hy1 (by omega)]
    show rd (entryK crCw crNw (toWord 48) s0.M) y = rd s.M y
    rw [hE y (hy y hy1).1 (hy y hy1).2, hH0 y hy1]
  · rw [d5]
    show rd (entryK crCw crNw (toWord 48) s0.M) crP = rd s.M crP
    rw [hE _ (by decide) (by decide), p0]

/-! ## One position, the position loop -/

section Pos1

variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One position**: the leaf words of position `p` at `a … a + 47`; `crP := p + 1`,
`crWA := a + 48`; every other heap cell kept. -/
theorem cr1_pos_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p a : ℕ} (hp : p < 2 ^ 12) (hP : rd s.M crP = toWord p) (hA : rd s.M crWA = toWord a)
    (ha : regs ≤ a) (ha2 : a + 48 + 2 < 2 ^ 64) (hsz : a + 48 ≤ s.M.size) :
    (∀ t < 48, rd (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M (a + t) =
      crLeafW (xLeafBytes1 L cap p) t) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 48 ≤ y) →
      rd (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M ∧
    rd (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M crWA = toWord (a + 48) ∧
    rd (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M crP = toWord (p + 1) := by
  set I := crTape c π L with hI
  have hpc : p / 32 < cap.length := by rw [hcl]; omega
  have hs := hM.1
  simp only [regs] at hs
  -- the cap node
  have wf1 : WF (.seq (.blk (cr1CapPs capW)) crLd4) := ⟨by simp +decide only [cr1CapPs, WF,
    Prim.dst, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true], cr_wf_ld4⟩
  have lo1 : Lo (.seq (.blk (cr1CapPs capW)) crLd4) := ⟨by simp +decide only [cr1CapPs, Lo,
    Prim.dst, regs, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true], cr_lo_ld4⟩
  have q1 := cr1_capLd_sem I s hM (by rw [hcl]; omega) hcap (by omega) hpc hP
  have hH1 := hframe I _ s lo1
  have f1 : ∀ r, r = crP ∨ r = crWA → rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M r =
      rd s.M r := fun r hr => frame I _ s wf1 hM r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;>
      simp +decide only [cr1CapPs, crLd4, Writes, Prim.dst, crK, crB, crTA, rQ0, rQ1, rQ2, rQ3,
        crP, crWA, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.blk (cr1CapPs capW)) crLd4) s
  rw [cr1Pos, semXIR_seq]
  generalize semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s = s1 at q1 hH1 f1 hM1 hsz1
  -- `crOk := 1`, the height count
  have wf2 : WF (.blk [.const crOk 1, .const crNH (toWord 5)]) := by simp +decide only [WF,
    Prim.dst, crOk, crNH, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have r2 : ∀ r, r ≠ crOk → r ≠ crNH →
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1).M r = rd s1.M r :=
    fun r h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o2 : rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1).M crOk = 1 ∧
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1).M crNH = toWord 5 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crOk, crNH]; omega)) only
      [rd_set_self, rd_set_ne]
  have hM2 := inv_sem I wf2 hM1
  have hsz2 := size_sem I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1 = s2 at r2 o2 hM2 hsz2
  have hW2 : crWalkN 5 L (cap[p / 32]'hpc) p 5 s2.M := by
    refine .inl ⟨o2.1, cap[p / 32]'hpc, ?_, rfl⟩
    rw [r2 rQ0 (by decide) (by decide), r2 rQ1 (by decide) (by decide),
      r2 rQ2 (by decide) (by decide), r2 rQ3 (by decide) (by decide)]
    exact q1
  have hH2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => by
    rw [r2 y (by simp only [crOk, regs] at *; omega) (by simp only [crNH, regs] at *; omega),
      hH1 y hy]
  -- the height loop
  have hE : ∀ i, i ≠ crHc → i ≠ cTmp → rd (entryK crHc crNH (toWord 5) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crHc crNH (toWord 5) s2.M) crHc = toWord 5 :=
    entryK_count hM2 (by decide) (by decide) (by decide) o2.2
  have hME := inv_entryK (c := crHc) (n := crNH) (K := toWord 5) hM2 (by decide)
  have e : semXIR I (.loopK crHc crNH (toWord 5) (crNode bX pL)) s2 =
      iterL (semXIR I (crNode bX pL)) crHc 5 ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 5 < 2 ^ 64 by norm_num)]
  have hyE : ∀ y, regs ≤ y → y ≠ crHc ∧ y ≠ cTmp := fun y hy => by
    simp only [crHc, cTmp, regs] at *; omega
  have hWE : crWalkN 5 L (cap[p / 32]'hpc) p 5 (entryK crHc crNH (toWord 5) s2.M) := by
    unfold crWalkN at hW2 ⊢
    rw [hE crOk (by decide) (by decide), hE rQ0 (by decide) (by decide),
      hE rQ1 (by decide) (by decide), hE rQ2 (by decide) (by decide),
      hE rQ3 (by decide) (by decide)]
    exact hW2
  have hxr : ∀ a', regs ≤ bX + a' := fun a' => by simp only [regs] at hbX ⊢; omega
  have hXE : ∀ a' < L.length, rd (entryK crHc crNH (toWord 5) s2.M) (bX + a') = Xi a' :=
    fun a' ha' => by
      rw [hE _ (hyE _ (hxr a')).1 (hyE _ (hxr a')).2, hH2 _ (hxr a'), hXs a' ha']
  have hPE : rd (entryK crHc crNH (toWord 5) s2.M) crP = toWord p := by
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  obtain ⟨n1, n2, n3, n4, n5⟩ := cr_nodeLoopN hbX hbX2 hpL hD hX (by omega) 5
    ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩ (by norm_num) hME hXE hPE hcnt hWE
  have hH3 : ∀ y, regs ≤ y →
      rd (iterL (semXIR I (crNode bX pL)) crHc 5 ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩).M y =
        rd s.M y := fun y hy => by
    rw [n3 y hy]
    show rd (entryK crHc crNH (toWord 5) s2.M) y = _
    rw [hE y (hyE y hy).1 (hyE y hy).2, hH2 y hy]
  have hP3 : rd (iterL (semXIR I (crNode bX pL)) crHc 5
      ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩).M crP = toWord p := by
    rw [n4]
    show rd (entryK crHc crNH (toWord 5) s2.M) crP = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  have hA3 : rd (iterL (semXIR I (crNode bX pL)) crHc 5
      ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩).M crWA = toWord a := by
    rw [n5]
    show rd (entryK crHc crNH (toWord 5) s2.M) crWA = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inr rfl), hA]
  have hsz3 : (iterL (semXIR I (crNode bX pL)) crHc 5
      ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩).M.size = s.M.size := by
    rw [size_iterL (fun s' => size_sem I (crNode bX pL) s')]
    show (entryK crHc crNH (toWord 5) s2.M).size = _
    rw [size_entryK, hsz2, hsz1]
  rw [semXIR_seq, e]
  generalize iterL (semXIR I (crNode bX pL)) crHc 5 ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩ = s3
    at n1 n2 hH3 hP3 hA3 hsz3
  -- the leaf
  obtain ⟨ql, hql, c1, c2⟩ := cr_leaf_semN hbX hbX2 hpL hD hX s3 n2 (fun a' ha' => by
    rw [hH3 _ (by simp only [regs] at hbX ⊢; omega), hXs a' ha']) n1
  have hH4 := hframeK I (crLeaf bX pL) s3 cr_loK_leaf
  have hP4 : rd (semXIR I (crLeaf bX pL) s3).M crP = toWord p := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crP (by decide)
      (cr_leaf_nw (.inl rfl)), hP3]
  have hA4 : rd (semXIR I (crLeaf bX pL) s3).M crWA = toWord a := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crWA (by decide)
      (cr_leaf_nw (.inr rfl)), hA3]
  have hM4 := inv_sem I (cr_wf_leaf (bX := bX) (pL := pL)) n2
  have hsz4 := size_sem I (crLeaf bX pL) s3
  rw [semXIR_seq]
  generalize semXIR I (crLeaf bX pL) s3 = s4 at c1 c2 hH4 hP4 hA4 hM4 hsz4
  -- the copy
  obtain ⟨k1, k2, k3, k4, k5⟩ := cr1_copy_sem I s4 hM4 hql ha ha2 (by omega) rfl c1 hA4
  rw [semXIR_seq]
  generalize semXIR I cr1Copy s4 = s5 at k1 k2 k3 k4 k5
  have hs5 := k3.1
  simp only [regs] at hs5
  have hc5 : rd s5.M cOne = 1 := k3.2 0 (by decide)
  have wf6 : WF (.blk [.op .add crP crP cOne]) := by simp +decide only [WF, Prim.dst, crP]
  have r6 : ∀ r, r ≠ crP → rd (semXIR I (.blk [.op .add crP crP cOne]) s5).M r = rd s5.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  refine ⟨fun t ht => ?_, fun y hy1 hy2 => ?_, inv_sem I wf6 k3, ?_, ?_⟩
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k1 t ht, c2, xLeafBytes1_eq hp hpc]
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k2 y hy1 hy2, hH4 y hy1, hH3 y hy1]
  · rw [r6 _ (by decide), k4]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [crP]; omega), k5, hP4, hc5, add_one_toWord]

/-- **The position loop**: `m` positions from `j` fill their leaf words' cells. -/
theorem cr1_posLoop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 ≤ bX) :
    ∀ (m j : ℕ) (s : St), j + m ≤ 2 ^ 12 → Inv s.M → bX ≤ s.M.size →
      (∀ a < L.length, rd s.M (bX + a) = Xi a) → rd s.M crP = toWord j →
      rd s.M crWA = toWord (wB + 48 * j) →
      (∀ q, j ≤ q → q < j + m → ∀ t < 48,
        rd (iterL (semXIR (crTape c π L) (cr1Pos bX pL capW)) crCp m s).M (wB + 48 * q + t) =
          crLeafW (xLeafBytes1 L cap q) t) ∧
      (∀ y, regs ≤ y → (y < wB + 48 * j ∨ wB + 48 * (j + m) ≤ y) →
        rd (iterL (semXIR (crTape c π L) (cr1Pos bX pL capW)) crCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (crTape c π L) (cr1Pos bX pL capW)) crCp m s).M
  | 0, j, s, _, hM, _, _, _, _ => ⟨fun q h1 h2 => by omega, fun _ _ _ => rfl, hM⟩
  | m + 1, j, s, hjm, hM, hsz, hXs, hP, hA => by
    set I := crTape c π L
    have e1 : 48 * (j + 1) = 48 * j + 48 := Nat.mul_succ 48 j
    obtain ⟨b1, b2, b3, b4, b5⟩ := cr1_pos_sem hbX hbX2 hpL hD hX s hM hXs hcl hcw hcap (p := j)
      (a := wB + 48 * j) (by omega) hP hA (by omega) (by omega) (by omega)
    have hM' : Inv (decS crCp (semXIR I (cr1Pos bX pL capW) s)).M := inv_decS b3 (by decide)
    have dk : ∀ r, r ≠ crCp → rd (decS crCp (semXIR I (cr1Pos bX pL capW) s)).M r =
        rd (semXIR I (cr1Pos bX pL capW) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hy : ∀ y, regs ≤ y → y ≠ crCp := fun y hy => by simp only [crCp, regs] at *; omega
    have hsz' : bX ≤ (decS crCp (semXIR I (cr1Pos bX pL capW) s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    obtain ⟨d1, d2, d3⟩ := cr1_posLoop hD hX hcl hcw hcap hwB hwB2 m (j + 1) _ (by omega) hM'
      hsz'
      (fun a ha => by
        rw [dk _ (hy _ (by simp only [regs] at hbX ⊢; omega)),
          b2 _ (by simp only [regs] at hbX ⊢; omega) (.inr (by omega)), hXs a ha])
      (by rw [dk _ (by decide), b5])
      (by rw [dk _ (by decide), b4, e1, Nat.add_assoc])
    have e3 : 48 * (j + 1 + m) = 48 * (j + (m + 1)) := by
      rw [show j + 1 + m = j + (m + 1) by omega]
    rw [e3] at d2
    simp only [iterL]
    refine ⟨fun q h1 h2 t ht => ?_, fun y hy1 hy2 => ?_, d3⟩
    · by_cases hq : q = j
      · subst hq
        rw [d2 _ (by omega) (.inl (by omega)), dk _ (hy _ (by omega)), b1 t ht]
      · exact d1 q (by omega) (by omega) t ht
    · rw [d2 _ hy1 (by omega), dk _ (hy _ hy1), b2 _ hy1 (by omega)]

/-- **The level-1 column reads on a sorted index**: `read1IR bX pL capW wB` stores at
`wB + 48 p + t` leaf word `t` of the reading at position `p < 2^12` and keeps every heap cell
outside `[wB, wB + 48 · 2^12)`. -/
theorem read1IR_sem4 (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW wB : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 ≤ bX) (hsz : bX ≤ s.M.size) :
    (∀ p < 2 ^ 12, ∀ t < 48,
      rd (semXIR (crTape c π L) (read1IR bX pL capW wB) s).M (wB + 48 * p + t) =
        crLeafW (xLeafBytes1 L cap p) t) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 48 * 2 ^ 12 ≤ y) →
      rd (semXIR (crTape c π L) (read1IR bX pL capW wB) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (read1IR bX pL capW wB) s).M := by
  set I := crTape c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (2 ^ 12))]) := by
    simp +decide only [WF, Prim.dst, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 12))]) s).M crP = toWord 0 ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 12))]) s).M crWA = toWord (wB + 48 * 0) ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 12))]) s).M crNp = toWord (2 ^ 12) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crP, crWA, crNp]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals rfl
  have hH0 := hframe I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 12))]) s
    (by simp +decide only [Lo, Prim.dst, regs, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 12))]) s
  rw [read1IR, semXIR_seq]
  generalize semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 12))]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ crCp → i ≠ cTmp →
      rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) crCp = toWord (2 ^ 12) :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCp) (n := crNp) (K := toWord (2 ^ 12)) hM0 (by decide)
  have e : semXIR I (.loopK crCp crNp (toWord (2 ^ 12)) (cr1Pos bX pL capW)) s0 =
      iterL (semXIR I (cr1Pos bX pL capW)) crCp (2 ^ 12)
        ⟨entryK crCp crNp (toWord (2 ^ 12)) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 2 ^ 12 < 2 ^ 64 by norm_num)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCp ∧ y ≠ cTmp := fun y hy => by
    simp only [crCp, cTmp, regs] at *; omega
  have hHE : ∀ y, regs ≤ y → rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) y = rd s.M y :=
    fun y hy' => by rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : 48 * (0 + 2 ^ 12) = 48 * 2 ^ 12 := by norm_num
  obtain ⟨d1, d2, d3⟩ := cr1_posLoop hbX hbX2 hpL hD hX hcl hcw hcap hwB hwB2 (2 ^ 12) 0
    ⟨entryK crCp crNp (toWord (2 ^ 12)) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega)
    (fun a ha => by
      show rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) crP = _
      rw [hE _ (by decide) (by decide), p0])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) crWA = _
      rw [hE _ (by decide) (by decide), a0])
  rw [e0] at d2
  refine ⟨fun q hq t ht => d1 q (by omega) (by omega) t ht, fun y hy1 hy2 => ?_, d3⟩
  rw [d2 y hy1 (by omega)]
  show rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) y = _
  rw [hHE y hy1]

end Pos1

/-- **The level-1 column reads** (as v1's `readIR_sem`, tree (12, 48, 7)). -/
theorem read1IR_sem {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 ≤ bX) :
    (∀ p < 2 ^ 12, ∀ t < 48,
      rdK (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M (wB + 48 * p + t) =
        (readRow1 L cap p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 48 * 2 ^ 12 ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M y = rd s₂.M y) ∧
    (∀ a < L.length,
      rd (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M (bX + a) =
        rd s₂.M (bX + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M := by
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  have hSX : Sorted4 pL (crTape c π L) L
      (fun a => rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a)) :=
    ⟨r1, r2, r3⟩
  obtain ⟨w1, w2, w3⟩ := read1IR_sem4 hbX hbX2 hpL ⟨hs, hq, ht⟩ hSX s₂ hM₂ hX₂ hcl hcw hcap hwB
    hwB2 hsz₂
  refine ⟨fun p hp t ht' => ?_, w2, fun a _ => w2 _ (by simp only [regs] at hbX ⊢; omega)
    (.inr (by omega)), w3⟩
  rw [rdK, w1 p hp t ht', crLeafW_readRow1 L cap p ht']

/-- The same, as the decoder's word (`readWd1`). -/
theorem read1IR_readWd {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 ≤ bX) {p t : ℕ} (hp : p < 2 ^ 12) (ht' : t < 48) :
    rdK (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M (wB + 48 * p + t) =
      readWd1 L cap p t :=
  (read1IR_sem hbX hbX2 hpL c π L hs hq ht s hM hsz s₂ hM₂ hsz₂ hX₂ hcl hcw hcap hwB hwB2).1 p hp
    t ht'

end Lvm.X
