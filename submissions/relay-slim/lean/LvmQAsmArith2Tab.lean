-- New for lvm (HAR-BT): phase 3 of Q_arith (`tabPh`: ξ, the table sumcheck, the evaluations, the
-- constraints and bus forms over them, the final check) as one gadget `tabG` from the tables' static
-- shapes and phase 2's output cells, its replay theorem, and the committed columns' claims as cells.
-- Reuses QA2's `scRunP4_eq`, `tableW_eq`, `tableFinal_check`, `eqTab_eq`; the rest is this family's.
import LvmQAsmArith2TabW

/-!
# Phase 3: the table sumcheck (`tabPh`)

`tabG S R P z o g bc` for the shapes `S` of the sumcheck tables, `R` rounds, start position `P`,
phase 2's cells `bc`: ξ (a load), `ξ^k` for the largest constraint count, `ξ^{cur_j}` per table and
`fp = ξ^{nC..nC+2}`, `eqα` (QA2's `eqTab`), the leaf constants, the block weights of both stackings,
the totals and the target, the rounds (`scRunP4`), the table weights (`tableW`), the evaluations
(loads), each table's term (`termG`), the final check (`tableFinal`). Output per table: its point cells
(`point.take τ`) and its evaluation cells.

**`tabG_replays`**: with `m.tables pub` the native tables of `st` and `bus = busFinalR st ⟨…⟩` on
phase 2's values, wherever `tabG (st.map Tab.shape) …` holds and asserts (gate on), `F`'s table phase
keeps `ok`, ends at `tabEnd`, and its evaluations are the output cells' values. **`tabClaims`**: the
committed columns' claims as `CClaim`s, `= tableClaimsR st evals` (`tabClaims_val`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.M3 Lvm.Loop Lvm.Loop.Build

/-! ## Helper gadgets -/

/-- `ξ^0 … ξ^n`. -/
def powsG (z o xi : Cell) : Nat → BM (List Cell)
  | 0 => pure [o]
  | n + 1 => do
    let l ← powsG z o xi n
    let x ← mulAdd .E (l.getD n o) xi z
    pure (l ++ [x])

/-- `X, X·ξ^{n₀}, X·ξ^{n₀+n₁}, …` (`ξ^n` from the powers `pw`). -/
def curG (z o : Cell) (pw : List Cell) : List Nat → Cell → BM (List Cell)
  | [], X => pure [X]
  | n :: ns, X => do
    let X' ← mulAdd .E X (pw.getD n o) z
    let r ← curG z o pw ns X'
    pure (X :: r)

/-- `Σ w`. -/
def sumG (z : Cell) : List Cell → BM Cell
  | [] => pure z
  | w :: ws => do
    let r ← sumG z ws
    lin .E 1 0 r w

/-- The weights of blocks `(κ, off)`. -/
def bwsG (z o : Cell) (facs : List (Cell × Cell)) (lt : List (Nat × Nat × Nat))
    (hi : List ((Nat × Nat) × Cell)) (D : Nat) : List (Nat × Nat) → BM (List Cell)
  | [] => pure []
  | b :: bs => do
    let w ← bwG z o facs lt hi D b.1 (b.2 >>> b.1)
    let r ← bwsG z o facs lt hi D bs
    pure (w :: r)

/-- Each table's evaluations, `3` lanes per scalar from lane `a`. -/
def evLoads (a : Nat) : List Nat → BM (List (List Cell))
  | [] => pure []
  | w :: ws => do
    let e ← ldEs a 3 w
    let r ← evLoads (a + 3 * w) ws
    pure (e :: r)

/-- The prefix sums. -/
def pre (l : List Nat) (j : Nat) : Nat := (l.take j).sum

section
variable {c : Ctx} {M : Mem} {z o : Cell}

theorem powsG_sound (hz : z.val M = 0) (ho : o.val M = 1) (xi : Cell) : ∀ n,
    SoundG c M (powsG z o xi n) fun l => l.length = n + 1 ∧ ∀ i ≤ n, (l.getD i o).val M = xi.val M ^ i
  | 0 => soundG_pure ⟨rfl, fun i hi => by rw [show i = 0 by omega]; simp [ho]⟩
  | n + 1 => soundG_bind (powsG_sound hz ho xi n) fun l hl =>
      soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (l.getD n o) xi z)) fun x hx =>
        soundG_pure ⟨by simp [hl.1], fun i hi => by
          rcases Nat.lt_or_ge i (n + 1) with h | h
          · rw [List.getD_append _ _ _ _ (by omega)]; exact hl.2 i (by omega)
          · obtain rfl : i = n + 1 := by omega
            rw [List.getD_append_right _ _ _ _ (by omega), hl.1, Nat.sub_self, List.getD_cons_zero,
              hx.1, hl.2 n le_rfl, hz, add_zero, pow_succ]⟩

theorem curG_sound (hz : z.val M = 0) {pw : List Cell} {ξ : FE} :
    ∀ (ns : List Nat) (X : Cell), (∀ n ∈ ns, (pw.getD n o).val M = ξ ^ n) →
      SoundG c M (curG z o pw ns X) fun l =>
      l.length = ns.length + 1 ∧ ∀ j ≤ ns.length, (l.getD j o).val M = X.val M * ξ ^ pre ns j
  | [], X, _ => soundG_pure ⟨rfl, fun j hj => by
      rw [show j = 0 by simpa using hj]; simp [pre]⟩
  | n :: ns, X, hpw => soundG_bind (soundG_aspec (QB.aspec_mulAdd .E X (pw.getD n o) z)) fun X' hX =>
      soundG_bind (curG_sound hz ns X' fun k hk => hpw k (List.mem_cons_of_mem _ hk)) fun r hr =>
        soundG_pure ⟨by simp [hr.1], fun j hj => by
        rcases j with _ | j
        · simp [pre]
        · simp only [List.getD_cons_succ]
          rw [hr.2 j (by simpa using hj), hX.1, hpw n List.mem_cons_self, hz, add_zero]
          simp only [pre, List.take_succ_cons, List.sum_cons, pow_add]
          ring⟩

theorem sumG_sound (hz : z.val M = 0) : ∀ ws : List Cell,
    SoundG c M (sumG z ws) fun r => r.val M = sumE (vs M ws)
  | [] => soundG_pure (by rw [hz]; rfl)
  | w :: ws => soundG_bind (sumG_sound hz ws) fun r hr =>
      soundG_mono (soundG_aspec (QB.aspec_lin .E 1 0 r w)) fun x hx => by
        rw [hx.1, hr, ofK_one, ofK_zero, one_mul, add_zero]
        simp only [vs, List.map_cons, sumE_cons]; ring

theorem bwsG_sound (hz : z.val M = 0) (ho : o.val M = 1) {facs : List (Cell × Cell)} {ζ : List FE}
    (hf1 : (facs.map (·.2)).map (·.val M) = ζ) (hf2 : FacOk M facs) {hi : List ((Nat × Nat) × Cell)}
    (hhi : HiOk M ζ hi) {lt : List (Nat × Nat × Nat)} (hlt : LvlOk M ζ lt) {D : Nat} (hD : D = ζ.length) :
    ∀ bs : List (Nat × Nat), SoundG c M (bwsG z o facs lt hi D bs) fun ws =>
      vs M ws = bs.map fun b => blockWeight ζ b.1 b.2
  | [] => soundG_pure rfl
  | b :: bs => soundG_bind (bwG_sound hz ho hf1 hf2 hhi hlt hD b.1 (b.2 >>> b.1)) fun w hw =>
      soundG_bind (bwsG_sound hz ho hf1 hf2 hhi hlt hD bs) fun r hr => soundG_pure (by
        rw [vs, List.map_cons, List.map_cons, ← vs, hr, hw, blockWeight_eqW])

theorem evLoads_sound {sig : ByteArray} {T : Nat} (hS : Q1.Streamed M sig T) :
    ∀ (ws : List Nat) (a : Nat), 8 * (a + 3 * ws.sum) ≤ 8 * T →
      SoundG c M (evLoads a ws) fun es => es.length = ws.length ∧
        ∀ j < ws.length, vs M (es.getD j []) =
          Q1.scalarsAt (feAt sig) (8 * a + 24 * pre ws j) (ws.getD j 0)
  | [], _, _ => soundG_pure ⟨rfl, fun j h => absurd h (by simp)⟩
  | w :: ws, a, hT => soundG_bind (ldEs_sound hS a 3 w fun i hi => by simp at hT; omega) fun e he =>
      soundG_bind (evLoads_sound hS ws (a + 3 * w) (by simp at hT ⊢; omega)) fun r hr =>
        soundG_pure ⟨by simp [hr.1], fun j hj => by
          rcases j with _ | j
          · simp only [List.getD_cons_zero, he, Q1.scalarsAt, pre, List.take_zero, List.sum_nil]
            exact List.map_congr_left fun i _ => congrArg _ (by omega)
          · simp only [List.getD_cons_succ]
            rw [hr.2 j (by simpa using hj)]
            simp only [pre, List.take_succ_cons, List.sum_cons]
            congr 1; omega⟩

end

/-! ## The terms of all tables -/

/-- Each table's term (`termG`), table `j` with its stacked blocks. -/
def termsG (z xi fp2 : Cell) (K : TK) (Xs : List Cell) (evs : List (List Cell))
    (Lpp : List ((SBlk × Nat) × Cell)) (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) :
    List (TShape × Nat) → BM (List Cell)
  | [] => pure []
  | tj :: rest => do
    let x ← termG z xi (Xs.getD tj.2 z) fp2 K tj.1.cons (evs.getD tj.2 [])
      (Lpp.filter fun y => y.1.1.tab == tj.2) (Lc.filter fun y => y.1.1.1 == tj.2)
    let r ← termsG z xi fp2 K Xs evs Lpp Lc rest
    pure (x :: r)

/-- The value `termG` computes for table `(t, j)`. -/
def termVal (M : Mem) (xi X fp2 : Cell) (fp0 fp1 β : FE) (eqα : List FE) (cons : List CPoly)
    (ev : List Cell) (Lpp : List ((SBlk × Nat) × Cell)) (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) : FE :=
  X.val M * polyEval (cons.map (CPoly.evalE ((vs M ev).getD · 0))) (xi.val M) +
    sumE (Lpp.map fun x => x.2.val M * (fp0 * (fPush eqα β x.1.1).form.value ((vs M ev).getD · 0) +
      fp1 * (fPull eqα β x.1.1).form.value ((vs M ev).getD · 0))) +
    fp2.val M * sumE (Lc.map fun x => x.2.val M * (vs M ev).getD x.1.1.2.2 0)

section
variable {c : Ctx} {M : Mem} {z : Cell}

theorem termsG_sound (hz : z.val M = 0) (hzE : z.ty = .E) {K : TK} {fp0 fp1 β : FE} {eqα : List FE}
    (hK : TKOk M z K fp0 fp1 β eqα) (xi fp2 : Cell) (Xs : List Cell) (evs : List (List Cell))
    (Lpp : List ((SBlk × Nat) × Cell)) (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) :
    ∀ l : List (TShape × Nat), SoundG c M (termsG z xi fp2 K Xs evs Lpp Lc l) fun ts =>
      vs M ts = l.map fun tj => termVal M xi (Xs.getD tj.2 z) fp2 fp0 fp1 β eqα tj.1.cons
        (evs.getD tj.2 []) (Lpp.filter fun y => y.1.1.tab == tj.2) (Lc.filter fun y => y.1.1.1 == tj.2)
  | [] => soundG_pure rfl
  | tj :: rest => soundG_bind (termG_sound hz hzE hK xi _ fp2 tj.1.cons _ _ _) fun x hx =>
      soundG_bind (termsG_sound hz hzE hK xi fp2 Xs evs Lpp Lc rest) fun r hr => soundG_pure (by
        rw [vs, List.map_cons, List.map_cons, ← vs, hr, hx]; rfl)

end

/-! ## The static plan of the weights -/

/-- The separators of the shapes' keys. -/
def sepsOf (S : List TShape) : List FK := ((ppBlocks S).map (·.key.sep)).eraseDups

/-- Every stacked block of both sides: (height, offset). -/
def allKO (S : List TShape) : List (Nat × Nat) :=
  (ppS S).map (fun bo => (bo.1.κ, bo.2)) ++ (cS S).map (fun bo => (bo.1.2.1, bo.2))

/-- The rows of a level with `s` table coordinates: table, products, high parts. -/
def costS (D κ s : Nat) (qs : List Nat) : Nat :=
  (if s = 0 then 0 else 2 * 2 ^ s + qs.length) + (qs.map (· / 2 ^ s)).eraseDups.length * (D - κ - s)

/-- The cheapest `s` of a level. -/
def bestS (D κ : Nat) (qs : List Nat) : Nat :=
  (List.range (D - κ + 1)).foldl (fun b s => if costS D κ s qs < costS D κ b qs then s else b) 0

/-- The levels' table sizes. -/
def planLv (D : Nat) (ko : List (Nat × Nat)) : List (Nat × Nat) :=
  (ko.map (·.1)).eraseDups.map fun κ => (κ, bestS D κ ((ko.filter (·.1 == κ)).map fun x => x.2 >>> κ))

/-- The high parts the blocks use. -/
def planHi (D : Nat) (lv : List (Nat × Nat)) (ko : List (Nat × Nat)) : List (Nat × Nat) :=
  (ko.map fun x =>
    let s := ((lv.find? (·.1 == x.1)).map (·.2)).getD 0
    if s ≠ 0 ∧ x.1 + s ≤ D then (x.1 + s, (x.2 >>> x.1) / 2 ^ s) else (x.1, x.2 >>> x.1)).eraseDups

/-! ## The table phase's gadget -/

/-- The rounds, with the pointer of their first cell. -/
def scP (R L₀ : Nat) (tgt : Cell) : BM (Cell × Nat) := do
  let q ← getPtr
  let fin ← QB.scRunP4 (binParts R) L₀ tgt
  pure (fin, q.e)

/-- Round `i`'s challenge cell of a run from `qe`. -/
def chC (qe i : Nat) : Cell := ec (qe + 1 + 8 * i + 3)

/-- **Phase 3's gadget.** -/
def tabG (S : List TShape) (R P : Nat) (z o g : Cell) (bc : BusC) : BM (List (List Cell × List Cell)) := do
  let xi ← ldE ((P + 40) / 8)
  let pw ← powsG z o xi ((S.map (·.cons.length)).foldl max 0)
  let Xs ← curG z o pw (S.map (·.cons.length)) o
  let fp0 := Xs.getD S.length o
  let fp1 ← mulAdd .E fp0 xi z
  let fp2 ← mulAdd .E fp1 xi z
  let eb ← eqTab (fun i => bc.al.getD i z) z o false bc.al.length
  let K ← tkG z fp0 fp1 bc.be eb (2 ^ bc.al.length) (sepsOf S)
  let facs ← facG bc.pt
  let lv := planLv bc.pt.length (allKO S)
  let lt ← lvlsG z o bc.pt lv
  let hi ← hisG z o facs (planHi bc.pt.length lv (allKO S))
  let wpp ← bwsG z o facs lt hi bc.pt.length ((ppS S).map fun bo => (bo.1.κ, bo.2))
  let wc ← bwsG z o facs lt hi bc.pt.length ((cS S).map fun bo => (bo.1.2.1, bo.2))
  let spp ← sumG z wpp
  let scc ← sumG z wc
  let T0 ← lin .E 1 1 (bc.vals.getD 0 z) spp
  let T1 ← lin .E 1 1 (bc.vals.getD 1 z) spp
  let T2 ← lin .E 1 1 (bc.vals.getD 2 z) scc
  let t0 ← mulAdd .E fp0 T0 z
  let t1 ← mulAdd .E fp1 T1 t0
  let tgt ← mulAdd .E fp2 T2 t1
  let r ← scP R ((P + 72) / 8) tgt
  let ws ← QB.tableW z o (fun k => bc.pt.getD k z) (chC r.2) R (S.map (·.τ))
  let evs ← evLoads ((P + 72 + 144 * R + 40) / 8) (S.map (·.cols.length))
  let terms ← termsG z xi fp2 K Xs evs ((ppS S).zip wpp) ((cS S).zip wc) S.zipIdx
  QB.tableFinal z g r.1 ws terms
  pure ((S.zip evs).map fun x => (((List.range R).map (chC r.2)).reverse.take x.1.τ, x.2))

/-- The position after phase 3. -/
def tabEnd (S : List TShape) (R P : Nat) : Nat := P + 72 + 144 * R + 24 * (S.map (·.cols.length)).sum

/-! ## Soundness -/

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem eqTab_sound {z o : Cell} (hz : z.val M = 0) (hzE : z.ty = .E) (hoE : o.ty = .E) (ho : o.val M = 1)
    {al : List Cell} (halE : ∀ x ∈ al, x.ty = .E) {alphas : List FE} (hal : vs M al = alphas) :
    SoundG c M (eqTab (fun i => al.getD i z) z o false al.length) fun eb =>
      ∀ x < 2 ^ alphas.length, M.e (eb + x) = (eqKernel alphas).getD x 0 := by
  intro p hH _ x hx
  have hlen : al.length = alphas.length := by rw [← hal, vs, List.length_map]
  have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp at hoE; subst hoE; rfl
  have hty : ∀ i, (al.getD i z).ty = .E := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases h : al[i]? with
    | none => exact hzE
    | some y => exact halE y (List.mem_of_getElem? h)
  have hv : ∀ i < alphas.length, (al.getD i z).val M = alphas.getD i 0 := fun i hi => by
    rw [← hal, vs, List.getD_eq_getElem _ _ (by rw [hlen]; exact hi),
      List.getD_eq_getElem _ _ (by simp [hlen]; exact hi), List.getElem_map]
  rw [hlen] at hH
  have := eqTab_eq (fun i => al.getD i z) z o false alphas (p := p) hH hz hty hone hv x hx
  rw [hlen]
  simp only [Bool.false_eq_true, ite_false] at this
  rw [this, eqKernelA_getD _ _ hx, List.getD_eq_getElem?_getD, eqKernel_get? _ _ hx]
  rfl

theorem scP_sound (hS : Q1.Streamed M sig T) (R L₀ : Nat) (tgt : Cell) (hT : L₀ + 18 * R ≤ T) :
    SoundG c M (scP R L₀ tgt) fun r => ∀ s : RS, s.msg = 0 → s.ent = 8 * L₀ →
      r.1.val M = (sumcheck (tgt.val M) 4 (List.replicate R none) sig s).1.2 ∧
      ∀ i < R, (chC r.2 i).val M = (sumcheck (tgt.val M) 4 (List.replicate R none) sig s).1.1.getD i 0 := by
  intro p hH _
  simp only [scP, getPtr, bind_apply, pure_apply, Ptr.adv_nil, List.nil_append,
    List.append_nil] at hH ⊢
  intro s hs hent
  have := QB.scRunP4_eq (binParts R) L₀ tgt p hH sig s hs hent (fun j h1 h2 => by
    rw [nRounds_binParts] at h2; exact hS j (by omega))
  rw [nRounds_binParts] at this
  exact ⟨this.1, fun i hi => this.2 i hi⟩

theorem tableW_sound {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (e ch : Nat → Cell) (R : Nat)
    (hs : List Nat) (eqPt : List FE) (he : ∀ k, (e k).val M = eqPt.getD k 0) :
    SoundG c M (QB.tableW z o e ch R hs) fun ws => ∀ chs : List FE, chs.length = R →
      (∀ j < R, (ch j).val M = chs.getD j 0) → vs M ws = tableWeights hs eqPt chs.reverse := by
  intro p hH _ chs hl hch
  subst hl
  exact QB.tableW_eq hz ho e ch hs eqPt chs (fun k _ => he k) hch p hH

theorem tableFinal_sound {z g claim : Cell} (hz : z.val M = 0) (hg : g.val M = 1) (ws ts : List Cell) :
    SoundG c M (QB.tableFinal z g claim ws ts) fun _ =>
      (QB.finalOf (vs M ws) (vs M ts) 0 == claim.val M) = true :=
  fun p hH hA => (QB.tableFinal_check hz hg ws ts p hH).mp hA

end

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem termsAt_getD (v : Nat → FE) (cp fp pt : List FE) (d : TRow) : ∀ (rows : List TRow) (cur o j : Nat),
    j < rows.length →
    (termsAt v cp fp pt rows cur o).getD j 0 =
      termF cp fp pt (rows.getD j d).1 (rows.getD j d).2.1 (cur + pre (rows.map (·.1.nConstraints)) j)
        (Q1.scalarsAt v (o + 24 * pre (rows.map (·.1.width)) j) (rows.getD j d).1.width)
  | [], _, _, _, h => absurd h (by simp)
  | r :: rest, cur, o, j, h => by
    rcases j with _ | j
    · simp [termsAt, pre]
    · simp only [termsAt, List.getD_cons_succ]
      rw [termsAt_getD v cp fp pt d rest _ _ j (by simpa using h)]
      simp only [pre, List.map_cons, List.take_succ_cons, List.sum_cons]
      rw [show cur + r.1.nConstraints + (List.take j (List.map (fun x => x.1.nConstraints) rest)).sum =
          cur + (r.1.nConstraints + (List.take j (List.map (fun x => x.1.nConstraints) rest)).sum) by omega,
        show o + 24 * r.1.width + 24 * (List.take j (List.map (fun x => x.1.width) rest)).sum =
          o + 24 * (r.1.width + (List.take j (List.map (fun x => x.1.width) rest)).sum) by omega]

theorem termsAt_length (v : Nat → FE) (cp fp pt : List FE) : ∀ (rows : List TRow) (cur o : Nat),
    (termsAt v cp fp pt rows cur o).length = rows.length
  | [], _, _ => rfl
  | r :: rest, cur, o => by simp [termsAt, termsAt_length v cp fp pt rest]

theorem evsAt_getD (v : Nat → FE) (pt : List FE) (d : TRow) : ∀ (rows : List TRow) (o j : Nat),
    j < rows.length →
    (evsAt v pt rows o).getD j ([], []) =
      (pt.take (rows.getD j d).1.logHeight,
        Q1.scalarsAt v (o + 24 * pre (rows.map (·.1.width)) j) (rows.getD j d).1.width)
  | [], _, _, h => absurd h (by simp)
  | r :: rest, o, j, h => by
    rcases j with _ | j
    · simp [evsAt, pre]
    · simp only [evsAt, List.getD_cons_succ]
      rw [evsAt_getD v pt d rest _ j (by simpa using h)]
      simp only [pre, List.map_cons, List.take_succ_cons, List.sum_cons]
      congr 2; omega

theorem evsAt_length (v : Nat → FE) (pt : List FE) : ∀ (rows : List TRow) (o : Nat),
    (evsAt v pt rows o).length = rows.length
  | [], _ => rfl
  | r :: rest, o => by simp [evsAt, evsAt_length v pt rest]

theorem sumE_zip_filter {M : Mem} {α : Type} (W : α → FE) (q : α → Bool) (f : α → FE) :
    ∀ (l : List α) (ws : List Cell), vs M ws = l.map W →
      sumE (((l.zip ws).filter fun y => q y.1).map fun y => y.2.val M * f y.1) =
        sumE ((l.filter q).map fun a => W a * f a)
  | [], _, _ => rfl
  | a :: l, [], h => by simp [vs] at h
  | a :: l, w :: ws, h => by
    simp only [vs, List.map_cons, List.cons.injEq] at h
    have ih := sumE_zip_filter W q f l ws h.2
    simp only [List.zip_cons_cons, List.filter_cons]
    split <;> simp only [List.map_cons, sumE_cons, ih, h.1]

theorem pre_add_le (l : List Nat) {j : Nat} (hj : j < l.length) : pre l j + l.getD j 0 ≤ l.sum := by
  rw [pre, List.getD_eq_getElem _ _ hj, ← List.sum_take_succ, ← List.sum_take_add_sum_drop l (j + 1)]
  omega

theorem take_drop_take {α : Type} (l : List α) {m c n : Nat} (h : c + n ≤ m) :
    ((l.take m).drop c).take n = (l.drop c).take n := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

theorem sumE_W2 {α : Type} (W f g : α → FE) (A B : FE) (l : List α) :
    sumE (l.map fun x => W x * (A * f x + B * g x)) =
      A * sumE (l.map fun x => W x * f x) + B * sumE (l.map fun x => W x * g x) := by
  rw [← sumE_map_mul, ← sumE_map_mul, ← sumE_map_add]
  exact congrArg sumE (List.map_congr_left fun x _ => by ring)

theorem le_foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a ∧ ∀ n ∈ l, n ≤ l.foldl max a
  | [], a => ⟨le_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max a x)
    refine ⟨le_trans (le_max_left a x) h1, fun n hn => ?_⟩
    rcases List.mem_cons.mp hn with rfl | hn
    · exact le_trans (le_max_right a n) h1
    · exact h2 n hn

/-- **Phase 3, soundness of the gadget.** -/
theorem tabG_sound (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hg : g.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (p : Params) (m : M3) (pub : Pub)
    (tabs : List Tab) (hm : m.tables pub = (sumcheckTabs tabs).map nativeTable) (bc : BusC)
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    (hal : vs M bc.al = alphas) (hbe : bc.be.val M = beta) (hpt : vs M bc.pt = point)
    (hvals : vs M bc.vals = values) (hal2 : 2 ≤ alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E)
    (hptE : ∀ x ∈ bc.pt, x.ty = .E) (bus : BusOut)
    (hbus : bus = busFinalR (sumcheckTabs tabs) ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩)
    {P : Nat} (hP : P % 8 = 0)
    (hT : tabEnd ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P + 40 ≤ 8 * T) :
    SoundG c M (tabG ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P z o g bc) fun out =>
      ∀ s : RS, pos s = P → s.ok = true →
        (tabPh p m pub bus point sig s).2.ok = true ∧
        pos (tabPh p m pub bus point sig s).2 = tabEnd ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P ∧
        (tabPh p m pub bus point sig s).1 = out.map fun x => (vs M x.1, vs M x.2) := by
  set st := sumcheckTabs tabs with hst
  set S := st.map Tab.shape with hS'
  set R := p.tableRounds with hR
  have hTE : tabEnd S R P = P + 72 + 144 * R + 24 * (S.map (·.cols.length)).sum := rfl
  unfold tabG
  refine soundG_bind (ldE_sound hS (a := (P + 40) / 8) (by omega)) fun xi hxi => ?_
  refine soundG_bind (powsG_sound hz ho xi _) fun pw hpw => ?_
  have hpw' : ∀ n ∈ S.map (·.cons.length), (pw.getD n o).val M = xi.val M ^ n := fun n hn =>
    hpw.2 n ((le_foldl_max _ 0).2 n hn)
  refine soundG_bind (curG_sound hz _ o hpw') fun Xs hXs => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (Xs.getD S.length o) xi z)) fun fp1 hfp1 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E fp1 xi z)) fun fp2 hfp2 => ?_
  refine soundG_bind (eqTab_sound hz hzE hoE ho halE hal) fun eb heb => ?_
  have hall : bc.al.length = alphas.length := by rw [← hal, vs, List.length_map]
  have hlenα : (eqKernel alphas).length = 2 ^ bc.al.length := by rw [eqKernel_length, hall]
  refine soundG_bind (tkG_sound hz (Xs.getD S.length o) fp1 bc.be eb (2 ^ bc.al.length) (sepsOf S)
    (eqα := eqKernel alphas) hlenα (by
      have : 2 ^ 2 ≤ 2 ^ bc.al.length := Nat.pow_le_pow_right (by omega) (by omega)
      omega) fun i hi => heb i (by rw [hall] at hi; exact hi)) fun K hK => ?_
  refine soundG_bind (facG_sound bc.pt) fun facs hfacs => ?_
  have hf1 : (facs.map (·.2)).map (·.val M) = point := by rw [hfacs.1, ← hpt]; rfl
  have hD : bc.pt.length = point.length := by rw [← hpt, vs, List.length_map]
  refine soundG_bind (lvlsG_sound hz hzE hoE ho hptE hpt _) fun lt hlt => ?_
  refine soundG_bind (hisG_sound hz ho hf1 hfacs.2 _) fun hi hhi => ?_
  refine soundG_bind (bwsG_sound hz ho hf1 hfacs.2 hhi hlt hD _) fun wpp hwpp => ?_
  refine soundG_bind (bwsG_sound hz ho hf1 hfacs.2 hhi hlt hD _) fun wc hwc => ?_
  refine soundG_bind (sumG_sound hz wpp) fun spp hspp => ?_
  refine soundG_bind (sumG_sound hz wc) fun scc hscc => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 1 (bc.vals.getD 0 z) spp)) fun T0 hT0 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 1 (bc.vals.getD 1 z) spp)) fun T1 hT1 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 1 (bc.vals.getD 2 z) scc)) fun T2 hT2 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (Xs.getD S.length o) T0 z)) fun t0 ht0 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E fp1 T1 t0)) fun t1 ht1 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E fp2 T2 t1)) fun tgt htgt => ?_
  refine soundG_bind (scP_sound hS R ((P + 72) / 8) tgt (by omega)) fun r hr => ?_
  refine soundG_bind (tableW_sound hz ho (fun k => bc.pt.getD k z) (chC r.2) R (S.map (·.τ)) point
    (fun k => by
      simp only [← hpt, vs, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases bc.pt[k]? <;> simp [hz])) fun ws hws => ?_
  refine soundG_bind (evLoads_sound hS (S.map (·.cols.length)) ((P + 72 + 144 * R + 40) / 8)
    (by rw [Nat.mul_add, show 8 * ((P + 72 + 144 * R + 40) / 8) = P + 72 + 144 * R + 40 by omega]
        omega)) fun evs hevs => ?_
  refine soundG_bind (termsG_sound hz hzE hK xi fp2 Xs evs _ _ S.zipIdx) fun terms hterms => ?_
  refine soundG_bind (tableFinal_sound hz hg ws terms) fun _ hfin => soundG_pure ?_
  intro s hs hok
  rw [tabPh_run p m pub bus point st hm sig s, hs, hok]
  dsimp only
  have hξ : feAt sig (P + 40) = xi.val M := by rw [hxi]; exact congrArg _ (by omega)
  have hnC : S.map (·.cons.length) = st.map (·.cons.length) := by simp [hS', Tab.shape]
  have hfp0 : (Xs.getD S.length o).val M = xi.val M ^ (st.map (·.cons.length)).sum := by
    rw [hXs.2 S.length (by simp), ho, one_mul, hnC, pre, show S.length = (st.map (·.cons.length)).length by
      simp [hS'], List.take_length]
  rw [← hR]
  generalize hnC' : (st.map (·.cons.length)).sum = nC at hfp0
  rw [hξ]
  have hfp1v : fp1.val M = xi.val M ^ (nC + 1) := by rw [hfp1.1, hfp0, hz, add_zero, pow_succ]
  have hfp2v : fp2.val M = xi.val M ^ (nC + 2) := by rw [hfp2.1, hfp1v, hz, add_zero]; ring
  have hvk : ∀ k, (bc.vals.getD k z).val M = values.getD k 0 := fun k => by
    simp only [← hvals, vs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases bc.vals[k]? <;> simp [hz]
  have hWpp : vs M wpp = (ppS S).map fun bo => blockWeight point bo.1.κ bo.2 := by
    rw [hwpp, List.map_map]; rfl
  have hWc : vs M wc = (cS S).map fun bo => blockWeight point bo.1.2.1 bo.2 := by
    rw [hwc, List.map_map]; rfl
  have htgtv : tgt.val M = dot ((powers (xi.val M) (nC + 3)).drop nC) bus.totals := by
    rw [drop_powers3, hbus, totals_eq, dot3, htgt.1, ht1.1, ht0.1, hT0.1, hT1.1, hT2.1, hspp, hscc,
      hWpp, hWc, hvk, hvk, hvk, hfp0, hfp1v, hfp2v, hz, ofK_one]
    ring
  obtain ⟨hr1, hr2⟩ := hr ⟨P + 72, 0, true⟩ rfl (by show P + 72 = _; omega)
  rw [htgtv] at hr1 hr2
  have hscl := sumcheck_len (dot ((powers (xi.val M) (nC + 3)).drop nC) bus.totals) 4 (by decide)
    (List.replicate R none) sig ⟨P + 72, 0, true⟩ rfl
  rw [List.length_replicate] at hscl
  generalize sumcheck (dot ((powers (xi.val M) (nC + 3)).drop nC) bus.totals) 4 (List.replicate R none) sig
    ⟨P + 72, 0, true⟩ = SC at hr1 hr2 hscl ⊢
  have hτ : S.map (·.τ) = st.map (·.τ) := by simp [hS', Tab.shape]
  have hW := hws SC.1.1 hscl (fun j hj => hr2 j hj)
  rw [hτ] at hW
  generalize hWdef : tableWeights (st.map (·.τ)) point SC.1.1.reverse = W at hW ⊢
  have hlS : S.length = st.length := by simp [hS']
  have hlF : bus.forms.length = st.length := by rw [hbus, busFinalR_forms_def]; simp
  have hlW : W.length = st.length := by rw [← hWdef, QB.tableWeights_eq]; simp
  have hrows1 : ((st.map nativeTable).zip (bus.forms.zip W)).map (·.1) = st.map nativeTable :=
    List.map_fst_zip (by simp [hlF, hlW])
  have hrows2 : ((st.map nativeTable).zip (bus.forms.zip W)).map (·.2.2) = W := by
    rw [show (fun x : TRow => x.2.2) = Prod.snd ∘ Prod.snd from rfl, ← List.map_map,
      List.map_snd_zip (by simp [hlF, hlW]),
      List.map_snd_zip (by simp [hlF, hlW])]
  have hwid : ((st.map nativeTable).zip (bus.forms.zip W)).map (·.1.width) = S.map (·.cols.length) := by
    rw [show (fun x : TRow => x.1.width) = TableSpec.width ∘ Prod.fst from rfl, ← List.map_map, hrows1,
      List.map_map, hS', List.map_map]
    exact List.map_congr_left fun t _ => by simp [nativeTable, Tab.shape, Tab.w]
  have hncs : ((st.map nativeTable).zip (bus.forms.zip W)).map (·.1.nConstraints) =
      st.map (·.cons.length) := by
    rw [show (fun x : TRow => x.1.nConstraints) = TableSpec.nConstraints ∘ Prod.fst from rfl,
      ← List.map_map, hrows1, List.map_map]; rfl
  have hB : 8 * ((P + 72 + 144 * R + 40) / 8) = P + 72 + 144 * R + 40 := by omega
  have hlX : Xs.length = S.length + 1 := by rw [hXs.1, List.length_map]
  have hev : ∀ j < st.length, vs M (evs.getD j []) =
      Q1.scalarsAt (feAt sig) (P + 72 + 144 * R + 40 + 24 * pre (S.map (·.cols.length)) j)
        ((S.map (·.cols.length)).getD j 0) := fun j hj => by
    rw [hevs.2 j (by simp [hlS, hj]), hB]
  have hWSj : ∀ j (hj : j < st.length), (S.map (·.cols.length)).getD j 0 = (nativeTable st[j]).width := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simp [hlS, hj])]
    simp [hS', Tab.shape, nativeTable, Tab.w]
  have hXj : ∀ j < st.length, (Xs.getD j z).val M = xi.val M ^ pre (st.map (·.cons.length)) j := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by rw [hlX]; omega), ← List.getD_eq_getElem _ o (by rw [hlX]; omega),
      hXs.2 j (by simp [hlS]; omega), ho, one_mul, hnC]
  let d0 : TRow := (⟨0, 0, 0, fun _ _ => []⟩, [], 0)
  have hrowj : ∀ j (hj : j < st.length), ((st.map nativeTable).zip (bus.forms.zip W)).getD j d0 =
      (nativeTable st[j], bus.forms.getD j [], W.getD j 0) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simp [hlF, hlW, hj]), List.getD_eq_getElem _ _ (by rw [hlF]; exact hj),
      List.getD_eq_getElem _ _ (by rw [hlW]; exact hj)]
    simp
  have key : ∀ j (hj : j < st.length),
      termF (List.take nC (powers (xi.val M) (nC + 3))) (List.drop nC (powers (xi.val M) (nC + 3)))
        SC.1.1.reverse (nativeTable st[j]) (bus.forms.getD j []) (pre (st.map (·.cons.length)) j)
        (vs M (evs.getD j [])) =
      termVal M xi (Xs.getD j z) fp2 ((Xs.getD S.length o).val M) (fp1.val M) (bc.be.val M)
        (eqKernel alphas) st[j].cons (evs.getD j [])
        (((ppS S).zip wpp).filter fun y => y.1.1.tab == j) (((cS S).zip wc).filter fun y => y.1.1.1 == j) := by
    intro j hj
    have hcn : pre (st.map (·.cons.length)) j + st[j].cons.length ≤ nC := by
      rw [← hnC']
      have := pre_add_le (st.map (·.cons.length)) (j := j) (by simp [hj])
      rwa [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map] at this
    unfold termF termVal
    rw [show (nativeTable st[j]).nConstraints = st[j].cons.length from rfl,
      show ∀ q, (nativeTable st[j]).constraints q (vs M (evs.getD j [])) =
        st[j].cons.map (CPoly.evalE ((vs M (evs.getD j [])).getD · 0)) from fun _ => rfl,
      take_drop_take _ hcn, take_drop_powers _ _ _ _ (by omega)]
    have hdp := dot_pows (xi.val M) (st[j].cons.map (CPoly.evalE ((vs M (evs.getD j [])).getD · 0)))
      (pre (st.map (·.cons.length)) j)
    rw [List.length_map] at hdp
    rw [hdp, hbus, forms_value _ _ hj, drop_powers3, dot3, hXj j hj]
    dsimp only
    rw [sumE_zip_filter (fun bo : SBlk × Nat => blockWeight point bo.1.κ bo.2) (fun bo => bo.1.tab == j)
        (fun bo => (Xs.getD S.length o).val M *
            (fPush (eqKernel alphas) (bc.be.val M) bo.1).form.value (fun x => (vs M (evs.getD j [])).getD x 0) +
          fp1.val M *
            (fPull (eqKernel alphas) (bc.be.val M) bo.1).form.value (fun x => (vs M (evs.getD j [])).getD x 0))
        (ppS S) wpp hWpp,
      sumE_zip_filter (fun bo : (Nat × Nat × Nat) × Nat => blockWeight point bo.1.2.1 bo.2)
        (fun bo => bo.1.1 == j) (fun bo => (vs M (evs.getD j [])).getD bo.1.2.2 0) (cS S) wc hWc,
      sumE_W2, hfp0, hfp1v, hfp2v, hbe]
    ring
  have hlr : ((st.map nativeTable).zip (bus.forms.zip W)).length = st.length := by simp [hlF, hlW]
  have hterms' : termsAt (feAt sig) (List.take nC (powers (xi.val M) (nC + 3)))
      (List.drop nC (powers (xi.val M) (nC + 3))) SC.1.1.reverse ((st.map nativeTable).zip (bus.forms.zip W))
      0 (P + 72 + 144 * R + 40) = vs M terms := by
    apply List.ext_getElem
    · rw [termsAt_length, hterms, List.length_map, List.length_zipIdx, hlr, hlS]
    · intro j h1 h2
      have hj : j < st.length := by rw [termsAt_length, hlr] at h1; exact h1
      rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2,
        termsAt_getD _ _ _ _ d0 _ 0 _ j (by rw [hlr]; exact hj), hrowj j hj, hncs, hwid]
      dsimp only
      rw [Nat.zero_add, ← hWSj j hj, ← hev j hj, key j hj, hterms,
        List.getD_eq_getElem (List.map _ S.zipIdx) 0 (by rw [List.length_map, List.length_zipIdx, hlS]; exact hj),
        List.getElem_map, List.getElem_zipIdx]
      simp only [Nat.zero_add, hS', List.getElem_map]
      rfl
  have hch : (List.range R).map (fun i => (chC r.2 i).val M) = SC.1.1 := by
    apply List.ext_getElem (by simp [hscl])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hr2 i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrows2, hterms', ← hW, ← hr1, Bool.and_true]; exact hfin
  · simp only [pos, hwid, tabEnd]
  · apply List.ext_getElem
    · rw [evsAt_length, hlr]; simp [hlS, hevs.1]
    · intro j h1 h2
      have hj : j < st.length := by rw [evsAt_length, hlr] at h1; exact h1
      rw [← List.getD_eq_getElem _ ([], []) h1, evsAt_getD _ _ d0 _ _ j (by rw [hlr]; exact hj),
        hrowj j hj, hwid]
      dsimp only
      rw [← hWSj j hj, ← hev j hj]
      have hej : evs.getD j [] = evs[j]'(by rw [hevs.1]; simpa [hlS] using hj) :=
        List.getD_eq_getElem _ _ _
      simp only [List.getElem_map, List.getElem_zip, Function.comp_apply]
      refine Prod.ext ?_ (by simp only [hej])
      simp only [vs, List.map_take, List.map_reverse, List.map_map, Function.comp_def]
      rw [hch]
      simp [hS', Tab.shape, nativeTable]

end

/-! ## The headline -/

/-- What phase 3 hands on: `F`'s evaluations are the output cells' values, per table its point cells
(`point.take τ`) and its evaluation cells. -/
def TabR (M : Mem) (evals : List (List FE × List FE)) (out : List (List Cell × List Cell)) : Prop :=
  evals = out.map fun x => (vs M x.1, vs M x.2)

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **Phase 3 replayed** (soundness direction): with `m.tables pub` the native tables of the sumcheck
tables `st` of `tabs` and `bus = busFinalR st ⟨…⟩` on the values of phase 2's cells, wherever
`tabG (st.map Tab.shape) …` holds and asserts (gate on), `F`'s table phase from any state at position
`P` with `ok` keeps `ok`, ends at `tabEnd`, and its evaluations are the output cells' values. -/
theorem tabG_replays (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hg : g.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (p : Params) (m : M3) (pub : Pub)
    (tabs : List Tab) (hm : m.tables pub = (sumcheckTabs tabs).map nativeTable) (bc : BusC)
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    (hal : vs M bc.al = alphas) (hbe : bc.be.val M = beta) (hpt : vs M bc.pt = point)
    (hvals : vs M bc.vals = values) (hal2 : 2 ≤ alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E)
    (hptE : ∀ x ∈ bc.pt, x.ty = .E) (bus : BusOut)
    (hbus : bus = busFinalR (sumcheckTabs tabs) ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩)
    {P : Nat} (hP : P % 8 = 0)
    (hT : tabEnd ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig (tabPh p m pub bus point)
      (tabG ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P z o g bc) ptr P
      (tabEnd ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P) (TabR M) :=
  fun hok s hs hsok => soundG_ok (tabG_sound hS hz ho hg hzE hoE p m pub tabs hm bc hal hbe hpt hvals
    hal2 halE hptE bus hbus hP hT) hok s hs hsok

end

/-- Phase 3's start at `P20`/`P8`: right after phase 2. -/
def tabPos (p : Params) : Nat := busEnd p (busPos p)

theorem tabPos_mod_P20 : tabPos P20 % 8 = 0 := by decide
theorem tabPos_mod_P8 : tabPos P8 % 8 = 0 := by decide

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **Phase 3 at `P20`** (from `tabPos P20`, right after phase 2). -/
theorem tabG_replays_P20 (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0)
    (ho : o.val M = 1) (hg : g.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (m : M3) (pub : Pub)
    (tabs : List Tab) (hm : m.tables pub = (sumcheckTabs tabs).map nativeTable) (bc : BusC)
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    (hal : vs M bc.al = alphas) (hbe : bc.be.val M = beta) (hpt : vs M bc.pt = point)
    (hvals : vs M bc.vals = values) (hal2 : 2 ≤ alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E)
    (hptE : ∀ x ∈ bc.pt, x.ty = .E) (bus : BusOut)
    (hbus : bus = busFinalR (sumcheckTabs tabs) ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩)
    (hT : tabEnd ((sumcheckTabs tabs).map Tab.shape) P20.tableRounds (tabPos P20) + 40 ≤ 8 * T)
    (ptr : Ptr) :
    Replays c M sig (tabPh P20 m pub bus point)
      (tabG ((sumcheckTabs tabs).map Tab.shape) P20.tableRounds (tabPos P20) z o g bc) ptr (tabPos P20)
      (tabEnd ((sumcheckTabs tabs).map Tab.shape) P20.tableRounds (tabPos P20)) (TabR M) :=
  tabG_replays hS hz ho hg hzE hoE P20 m pub tabs hm bc hal hbe hpt hvals hal2 halE hptE bus hbus
    tabPos_mod_P20 hT ptr

/-- **Phase 3 at `P8`.** -/
theorem tabG_replays_P8 (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0)
    (ho : o.val M = 1) (hg : g.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (m : M3) (pub : Pub)
    (tabs : List Tab) (hm : m.tables pub = (sumcheckTabs tabs).map nativeTable) (bc : BusC)
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    (hal : vs M bc.al = alphas) (hbe : bc.be.val M = beta) (hpt : vs M bc.pt = point)
    (hvals : vs M bc.vals = values) (hal2 : 2 ≤ alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E)
    (hptE : ∀ x ∈ bc.pt, x.ty = .E) (bus : BusOut)
    (hbus : bus = busFinalR (sumcheckTabs tabs) ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩)
    (hT : tabEnd ((sumcheckTabs tabs).map Tab.shape) P8.tableRounds (tabPos P8) + 40 ≤ 8 * T)
    (ptr : Ptr) :
    Replays c M sig (tabPh P8 m pub bus point)
      (tabG ((sumcheckTabs tabs).map Tab.shape) P8.tableRounds (tabPos P8) z o g bc) ptr (tabPos P8)
      (tabEnd ((sumcheckTabs tabs).map Tab.shape) P8.tableRounds (tabPos P8)) (TabR M) :=
  tabG_replays hS hz ho hg hzE hoE P8 m pub tabs hm bc hal hbe hpt hvals hal2 halE hptE bus hbus
    tabPos_mod_P8 hT ptr

end

/-! ## The committed columns' claims as cells -/

/-- **The tables' committed-column claims** as `CClaim`s: per table, each committed column's
evaluation cell at the table's point cells, on its commitment, block `⟨τ, off⟩`. -/
def tabClaims (S : List TShape) (out : List (List Cell × List Cell)) (z : Cell) : List CClaim :=
  (S.zip out).flatMap fun x => x.1.cols.zipIdx.filterMap fun ci => match ci.1 with
    | some (rec, off) => some ⟨if rec then .crec else .main, .point ⟨x.1.τ, off⟩ x.2.1, x.2.2.getD ci.2 z⟩
    | none => none

/-- **The claims' values are `F`'s** (`tableClaimsR` on the evaluations phase 3 returns). -/
theorem tabClaims_val {M : Mem} {z : Cell} (hz : z.val M = 0) (st : List Tab)
    (out : List (List Cell × List Cell)) :
    (tabClaims (st.map Tab.shape) out z).map (CClaim.val M) =
      tableClaimsR st (out.map fun x => (vs M x.1, vs M x.2)) := by
  unfold tabClaims tableClaimsR
  rw [List.map_flatMap, List.zip_map_left, List.zip_map_right, List.flatMap_map, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  rw [List.map_filterMap]
  simp only [Prod.map, Tab.shape, id_eq]
  rw [List.zipIdx_map, List.filterMap_map]
  refine List.filterMap_congr fun ci _ => ?_
  rcases ci with ⟨col, i⟩
  cases col with
  | com rec off =>
    show Option.map (CClaim.val M) (some _) = some _
    rw [Option.map_some]
    refine congrArg some (Prod.ext rfl ?_)
    show BlockClaim.point _ _ ((x.2.2.getD i z).val M) = BlockClaim.point _ _ _
    congr 1
    simp only [vs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x.2.2[i]? <;> simp [hz]
  | fix f ev => rfl

end Lvm.Har
