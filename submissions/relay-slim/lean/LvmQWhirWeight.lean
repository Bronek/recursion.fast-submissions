import LvmQWhirFold

/-!
# QA2: WHIR column weights (`inducedWeight`) as builder gadgets

`F`'s glued weight of a level (`LvmDecideWhir.inducedWeight`, leanVM `induced_weight`):
`Σ_q w_q · Π_k (1 + p_k (1 + W_k(x_q) · inv_k))` with the subspace-polynomial chain
`W_0 = x_q`, `W_{k+1} = W_k² + R_k W_k` (`R` = `subspaceRoots`, `inv` their inverses).

**The F side** (`inducedWeight_eq`): the outer fold is a sum over the positions of `iwSeq … κ`,
the inner fold after `κ = |point|` coordinates (`iwSeq`, one `iwStep` per coordinate).

**The circuit** (`colWeight`), for `2^a` positions and the coordinates cut into chunks `2^c_i`
(`Σ 2^c_i = κ`):
* constants, per coordinate `k` (`E` cells at `cb + 2k`, `cb + 2k + 1`): `A_k = 1 + p_k`,
  `B_k = p_k · I_k` (`I_k` a `K` cell holding `inv_k`);
* prologue (loop `[a]`): `acc_q = w_q`, `W_q = x_q` (copies, laid out as the main loop's carried rows);
* per chunk a loop of dims `[a, c]` (**position inner, coordinate outer**), four rows:
  `f = B_k · W + A_k` (E·K), `acc' = acc · f` (E·E), `u = W + R_k` (K lin), `W' = W · u` (K muladd); the
  carried `acc`, `W` are read at offset `−2·2^a` (the previous coordinate, or the prologue);
* the sum over positions (loop `[a]`, running `lin`) and one difference row.
Cost per (position, coordinate): 14 + 16 + 6 + 8 = 44 words.

Reuse: leanerVM `Protocol/NovelBasis.lean` (`vanish`: `V_{k+1} = V_k (V_k + root_k)`, `normW`)
states the same chain; restated here on `Lvm.FE` against `F`'s own definitions.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-! ## The F side -/

/-- One coordinate of `inducedWeight`'s inner fold (`LvmDecideWhir:54-56`). -/
def iwStep (R I : List FE) (acc : FE × FE) (ck : FE × Nat) : FE × FE :=
  (acc.1 * (1 + ck.1 * (1 + acc.2 * I.getD ck.2 0)), FE.sq acc.2 + R.getD ck.2 0 * acc.2)

/-- The inner fold after `k` coordinates. -/
def iwSeq (R I pt : List FE) (w x : FE) : Nat → FE × FE
  | 0 => (w, x)
  | k + 1 => iwStep R I (iwSeq R I pt w x k) (pt.getD k 0, k)

theorem iwSeq_congr (R I : List FE) (w x : FE) {pt pt' : List FE} :
    ∀ k, (∀ j < k, pt.getD j 0 = pt'.getD j 0) → iwSeq R I pt w x k = iwSeq R I pt' w x k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [iwSeq]
    rw [iwSeq_congr R I w x k (fun j hj => h j (by omega)), h k (by omega)]

theorem foldl_zipIdx_eq (R I : List FE) (w x : FE) : ∀ (pt : List FE),
    pt.zipIdx.foldl (iwStep R I) (w, x) = iwSeq R I pt w x pt.length := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.zipIdx_append, List.foldl_append, ih]
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton, iwSeq, Nat.zero_add]
    rw [iwSeq_congr R I w x (pt := l ++ [a]) (pt' := l) l.length
      (fun j hj => by rw [List.getD_append _ _ _ _ hj])]
    simp

theorem foldl_add_map {α : Type} (g : α → FE) : ∀ (l : List α) (a : FE),
    l.foldl (fun acc x => acc + g x) a = a + (l.map g).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_map g l]; simp [add_assoc]

/-- The roots and inverses `inducedWeight` uses. -/
def iwRoots (m : Nat) : List FE := subspaceRoots m

/-- The inverses `inducedWeight` uses. -/
def iwInvs (m : Nat) : List FE := (subspaceRoots m).map fun v => if v == 0 then 0 else v⁻¹

/-- **`inducedWeight` as a sum over the positions** of the inner fold after `|point|`
coordinates (`x_q = eOfNat q`). -/
theorem inducedWeight_eq (m : Nat) (qs : List Nat) (ws pt : List FE) :
    inducedWeight m qs ws pt = ((List.zip ws qs).map fun wq =>
      (iwSeq (iwRoots m) (iwInvs m) pt wq.1 (eOfNat wq.2) pt.length).1).sum := by
  show List.foldl (fun total x => total +
      (List.foldl (iwStep (iwRoots m) (iwInvs m)) (x.1, eOfNat x.2) pt.zipIdx).1) 0 (ws.zip qs) = _
  rw [foldl_add_map (fun x : FE × Nat =>
      (List.foldl (iwStep (iwRoots m) (iwInvs m)) (x.1, eOfNat x.2) pt.zipIdx).1), zero_add]
  congr 1
  apply List.map_congr_left
  intro wq _
  rw [foldl_zipIdx_eq]

/-! ## The circuit -/

/-- Constants of coordinates `[k₀, k₀ + 2^c)`: `A_k = 1 + p_k`, `B_k = p_k · I_k` (`p_k` the `E`
cell `ptb + k`, `I_k` the `K` cell `ib + k`, `z` an `E` zero cell). -/
def cwConsts (c k₀ ptb ib z : Nat) : BM LoopOut :=
  loop [c] [⟨.lin 0 1, .E, [.abs ⟨.E, ptb + k₀, [1]⟩, .abs ⟨.E, ptb + k₀, [1]⟩]⟩,
    ⟨.muladd, .E, [.abs ⟨.E, ptb + k₀, [1]⟩, .abs ⟨.K, ib + k₀, [1]⟩, .abs ⟨.E, z, [0]⟩]⟩]

/-- The prologue: `acc_q = w_q` (`E` cell `wb + q`), `W_q = x_q` (`K` cell `xb + q`), each after a
padding row so that they sit where the main loop's carried rows do. -/
def cwPro (a wb xb : Nat) : BM LoopOut :=
  loop [a] [⟨.lin 0 0, .E, [.abs ⟨.E, wb, [1]⟩, .abs ⟨.E, wb, [1]⟩]⟩,
    ⟨.lin 0 0, .E, [.abs ⟨.E, wb, [1]⟩, .abs ⟨.E, wb, [1]⟩]⟩,
    ⟨.lin 0 0, .K, [.abs ⟨.K, xb, [1]⟩, .abs ⟨.K, xb, [1]⟩]⟩,
    ⟨.lin 0 0, .K, [.abs ⟨.K, xb, [1]⟩, .abs ⟨.K, xb, [1]⟩]⟩]

/-- The template of a chunk at pointer `p`: coordinates `k₀ + k`, constants at `cb + 2k`, roots
`R_k` at the `K` cells `rb + k₀ + k`. -/
def cwTpl (a k₀ cb rb z zk : Nat) (p : Ptr) : List LRow :=
  [⟨.muladd, .E, [.abs ⟨.E, cb + 2 * k₀ + 1, [0, 2]⟩, .abs ⟨.K, p.k + 1 - 2 * 2 ^ a, [2, 2 * 2 ^ a]⟩,
      .abs ⟨.E, cb + 2 * k₀, [0, 2]⟩]⟩,
   ⟨.muladd, .E, [.abs ⟨.E, p.e + 1 - 2 * 2 ^ a, [2, 2 * 2 ^ a]⟩, .cur 0, .abs ⟨.E, z, [0, 0]⟩]⟩,
   ⟨.lin 1 0, .K, [.abs ⟨.K, p.k + 1 - 2 * 2 ^ a, [2, 2 * 2 ^ a]⟩, .abs ⟨.K, rb + k₀, [0, 1]⟩]⟩,
   ⟨.muladd, .K, [.abs ⟨.K, p.k + 1 - 2 * 2 ^ a, [2, 2 * 2 ^ a]⟩, .cur 2, .abs ⟨.K, zk, [0, 0]⟩]⟩]

/-- The chunks: coordinates `[k₀, k₀ + Σ 2^c)`. -/
def cwChunks (a cb rb z zk : Nat) : Nat → List Nat → BM Unit
  | _, [] => pure ()
  | k₀, cc :: cs => fun p =>
    ((), (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2 ++
      (cwChunks a cb rb z zk (k₀ + 2 ^ cc) cs (p.adv (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2)).2)

/-- The constants of every chunk, contiguous: `A_k`, `B_k` at `p.e + 2k`, `p.e + 2k + 1`. -/
def cwConstsAll (ptb ib z : Nat) : Nat → List Nat → BM Unit
  | _, [] => pure ()
  | k₀, cc :: cs => fun p =>
    ((), (cwConsts cc k₀ ptb ib z p).2 ++
      (cwConstsAll ptb ib z (k₀ + 2 ^ cc) cs (p.adv (cwConsts cc k₀ ptb ib z p).2)).2)

/-- The sum over the positions of the carried `acc` cells at `base + 2q` (running `lin`, then the
difference with the cell before the loop). -/
def cwSum (a n base : Nat) : BM Cell := do
  let p ← getPtr
  let s ← loop [a] [⟨.lin 1 0, .E, [.abs ⟨.E, base, [2]⟩, .prev 0]⟩]
  add (s.cell 0 (n - 1)) (ec (p.e - 1))

/-- **The column weight of one level** over `n ≤ 2^a` positions (the loops run `2^a`, the sum stops
at `n`) (weights `w_q` at `E` cells `wb + q`,
points `x_q` at `K` cells `xb + q`) and the coordinates in chunks `cs` (point coordinates at the
`E` cells `ptb + k`, roots and inverses at the `K` cells `rb + k`, `ib + k`; `z`, `zk` zero cells). -/
def colWeight (a n : Nat) (cs : List Nat) (ptb ib rb wb xb z zk : Nat) : BM Cell := do
  let p ← getPtr
  cwConstsAll ptb ib z 0 cs
  let _ ← cwPro a wb xb
  cwChunks a p.e rb z zk 0 cs
  let p' ← getPtr
  cwSum a n (p'.e + 1 - 2 * 2 ^ a)

variable {c : Ctx} {M : Mem}

theorem unflat_qk {a c q k : Nat} (hq : q < 2 ^ a) (hk : k < 2 ^ c) :
    unflat [a, c] (q + 2 ^ a * k) = [q, k] := unflat_two hq hk

/-- The four row equations of a chunk at position `q`, coordinate `k`. -/
theorem cwChunk_rows {p : Ptr} {a cc k₀ cb rb z zk : Nat}
    (h : SegsHold c M p (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2) {q k : Nat} (hq : q < 2 ^ a)
    (hk : k < 2 ^ cc) :
    M.e (p.e + 2 * (q + 2 ^ a * k)) = M.e (cb + 2 * k₀ + 1 + 2 * k) *
        FE.ofK (M.k (p.k + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * k))) + M.e (cb + 2 * k₀ + 2 * k) ∧
    M.e (p.e + 1 + 2 * (q + 2 ^ a * k)) =
      M.e (p.e + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * k)) * M.e (p.e + 2 * (q + 2 ^ a * k)) + M.e z ∧
    FE.ofK (M.k (p.k + 2 * (q + 2 ^ a * k))) =
      FE.ofK (M.k (p.k + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * k))) + FE.ofK (M.k (rb + k₀ + k)) ∧
    FE.ofK (M.k (p.k + 1 + 2 * (q + 2 ^ a * k))) =
      FE.ofK (M.k (p.k + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * k))) *
        FE.ofK (M.k (p.k + 2 * (q + 2 ^ a * k))) + FE.ofK (M.k zk) := by
  have hjf : q + 2 ^ a * k < 2 ^ [a, cc].sum := by
    have := lt_size_la hq hk; simpa using this
  have hu := unflat_qk hq hk
  have r0 := loop_rel h (jf := q + 2 ^ a * k) (t := 0) hjf (by simp [cwTpl])
  have r1 := loop_rel h (jf := q + 2 ^ a * k) (t := 1) hjf (by simp [cwTpl])
  have r2 := loop_rel h (jf := q + 2 ^ a * k) (t := 2) hjf (by simp [cwTpl])
  have r3 := loop_rel h (jf := q + 2 ^ a * k) (t := 3) hjf (by simp [cwTpl])
  simp only [LRel, cwTpl, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at r0 r1 r2 r3
  rw [Opd.val_cur M _ hjf] at r1 r3
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, LoopOut.cell_val,
    Mem.rd_E, Mem.rd_K] at r0 r1 r2 r3
  rw [ofK_one, ofK_zero, one_mul, add_zero] at r2
  exact ⟨r0, r1, r2, r3⟩

/-- The values a chunk carries: `acc` and `W` of position `q` after `k` coordinates, at the cells
`base + 2q + 2·2^a·k` (`base` = the carried rows' first cells, one coordinate before the chunk). -/
def CwAt (M : Mem) (R I pt : List FE) (w x : Nat → FE) (a be bk k₀ k : Nat) : Prop :=
  ∀ q < 2 ^ a, M.e (be + (2 * q + 2 * 2 ^ a * k)) = (iwSeq R I pt (w q) (x q) (k₀ + k)).1 ∧
    FE.ofK (M.k (bk + (2 * q + 2 * 2 ^ a * k))) = (iwSeq R I pt (w q) (x q) (k₀ + k)).2

/-- **A chunk advances the carried values** by its `2^cc` coordinates. -/
theorem cwChunk_spec {p : Ptr} {a cc k₀ cb rb z zk : Nat} {R I pt : List FE} {w x : Nat → FE}
    (h : SegsHold c M p (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2)
    (hpe : 2 * 2 ^ a ≤ p.e) (hpk : 2 * 2 ^ a ≤ p.k) (hz : M.e z = 0) (hzk : M.k zk = 0)
    (hA : ∀ k < 2 ^ cc, M.e (cb + 2 * k₀ + 2 * k) = 1 + pt.getD (k₀ + k) 0)
    (hB : ∀ k < 2 ^ cc, M.e (cb + 2 * k₀ + 1 + 2 * k) = pt.getD (k₀ + k) 0 * I.getD (k₀ + k) 0)
    (hR : ∀ k < 2 ^ cc, FE.ofK (M.k (rb + k₀ + k)) = R.getD (k₀ + k) 0)
    (hin : CwAt M R I pt w x a (p.e + 1 - 2 * 2 ^ a) (p.k + 1 - 2 * 2 ^ a) k₀ 0) :
    ∀ k ≤ 2 ^ cc, CwAt M R I pt w x a (p.e + 1 - 2 * 2 ^ a) (p.k + 1 - 2 * 2 ^ a) k₀ k := by
  intro k hk
  induction k with
  | zero => exact hin
  | succ k ih =>
    intro q hq
    obtain ⟨r0, r1, r2, r3⟩ := cwChunk_rows h hq (k := k) (by omega)
    obtain ⟨ha, hw⟩ := ih (by omega) q hq
    have m : 2 * 2 ^ a * (k + 1) = 2 * (2 ^ a * k) + 2 * 2 ^ a := by ring
    have m' : 2 * 2 ^ a * k = 2 * (2 ^ a * k) := by ring
    have e1 : p.e + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * (k + 1)) = p.e + 1 + 2 * (q + 2 ^ a * k) := by
      rw [m]; omega
    have e2 : p.k + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * (k + 1)) = p.k + 1 + 2 * (q + 2 ^ a * k) := by
      rw [m]; omega
    rw [e1, e2, r1, r3, r2, r0, ha, hw, hz, hzk, ofK_zero, hA k (by omega), hB k (by omega),
      hR k (by omega), show k₀ + (k + 1) = (k₀ + k) + 1 by ring]
    simp only [iwSeq, iwStep, FE.sq_eq_mul]
    constructor <;> ring

/-! ### Pointer advances -/

/-- The total number of coordinates of a chunk list. -/
def csum (cs : List Nat) : Nat := (cs.map (2 ^ ·)).sum

theorem csum_cons (cc : Nat) (cs : List Nat) : csum (cc :: cs) = 2 ^ cc + csum cs := by
  simp [csum]

/-! ### Constants -/

theorem cwConsts_spec {p : Ptr} {cc k₀ ptb ib z : Nat} (h : SegsHold c M p (cwConsts cc k₀ ptb ib z p).2)
    {k : Nat} (hk : k < 2 ^ cc) :
    M.e (p.e + 2 * k) = 1 + M.e (ptb + k₀ + k) ∧
      M.e (p.e + 2 * k + 1) = M.e (ptb + k₀ + k) * FE.ofK (M.k (ib + k₀ + k)) + M.e z := by
  have hjf : k < 2 ^ [cc].sum := by simpa using hk
  have hu : unflat [cc] k = [k] := by simp [unflat, Nat.mod_eq_of_lt hk]
  have r0 := loop_rel h (jf := k) (t := 0) hjf (by simp)
  have r1 := loop_rel h (jf := k) (t := 1) hjf (by simp)
  simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at r0 r1
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, Mem.rd_K] at r0 r1
  rw [ofK_zero, ofK_one, zero_mul, add_zero] at r0
  refine ⟨by rw [r0]; ring_nf, by rw [show p.e + 2 * k + 1 = p.e + 1 + 2 * k by ring, r1]⟩

theorem cwConstsAll_adv (ptb ib z : Nat) : ∀ (cs : List Nat) (k₀ : Nat) (p : Ptr),
    p.adv (cwConstsAll ptb ib z k₀ cs p).2 = ⟨p.k, p.e + 2 * csum cs⟩
  | [], _, p => by simp [cwConstsAll, pure_apply, csum]
  | cc :: cs, k₀, p => by
    simp only [cwConstsAll, Ptr.adv_append, cwConstsAll_adv ptb ib z cs, cwConsts, loop_adv, csum_cons]
    simp [ltw, LRow.w, Row.w, Row.writes]; ring

theorem cwConstsAll_spec (ptb ib z : Nat) : ∀ (cs : List Nat) (k₀ : Nat) (p : Ptr),
    SegsHold c M p (cwConstsAll ptb ib z k₀ cs p).2 → ∀ k < csum cs,
      M.e (p.e + 2 * k) = 1 + M.e (ptb + k₀ + k) ∧
        M.e (p.e + 2 * k + 1) = M.e (ptb + k₀ + k) * FE.ofK (M.k (ib + k₀ + k)) + M.e z
  | [], _, _, _, k, hk => by simp [csum] at hk
  | cc :: cs, k₀, p, h, k, hk => by
    simp only [cwConstsAll] at h
    rw [segsHold_append] at h
    rw [csum_cons] at hk
    by_cases hlt : k < 2 ^ cc
    · exact cwConsts_spec h.1 hlt
    · have ih := cwConstsAll_spec ptb ib z cs (k₀ + 2 ^ cc) _ h.2 (k - 2 ^ cc) (by omega)
      have ha : (p.adv (cwConsts cc k₀ ptb ib z p).2).e = p.e + 2 * 2 ^ cc := by
        simp [cwConsts, loop_adv, ltw, LRow.w, Row.w, Row.writes]
      rw [ha] at ih
      have e1 : p.e + 2 * 2 ^ cc + 2 * (k - 2 ^ cc) = p.e + 2 * k := by omega
      have e2 : ptb + (k₀ + 2 ^ cc) + (k - 2 ^ cc) = ptb + k₀ + k := by omega
      have e3 : ib + (k₀ + 2 ^ cc) + (k - 2 ^ cc) = ib + k₀ + k := by omega
      rw [e1, e2, e3] at ih
      exact ih

/-! ### Prologue, chunks, sum -/

theorem cwPro_adv (a wb xb : Nat) (p : Ptr) :
    p.adv (cwPro a wb xb p).2 = ⟨p.k + 2 * 2 ^ a, p.e + 2 * 2 ^ a⟩ := by
  simp [cwPro, loop_adv, ltw, LRow.w, Row.w, Row.writes]

theorem cwPro_spec {p : Ptr} {a wb xb : Nat} (h : SegsHold c M p (cwPro a wb xb p).2) {q : Nat}
    (hq : q < 2 ^ a) :
    M.e (p.e + 1 + 2 * q) = M.e (wb + q) ∧ M.k (p.k + 1 + 2 * q) = M.k (xb + q) := by
  have hjf : q < 2 ^ [a].sum := by simpa using hq
  have hu : unflat [a] q = [q] := by simp [unflat, Nat.mod_eq_of_lt hq]
  have r1 := loop_rel h (jf := q) (t := 1) hjf (by simp [cwPro])
  have r3 := loop_rel h (jf := q) (t := 3) hjf (by simp [cwPro])
  simp only [cwPro, LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at r1 r3
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, Mem.rd_K,
    ofK_zero] at r1 r3
  exact ⟨by rw [← r1], ofK_inj (by rw [← r3])⟩

theorem cwChunks_adv (a cb rb z zk : Nat) : ∀ (cs : List Nat) (k₀ : Nat) (p : Ptr),
    p.adv (cwChunks a cb rb z zk k₀ cs p).2 =
      ⟨p.k + 2 * 2 ^ a * csum cs, p.e + 2 * 2 ^ a * csum cs⟩
  | [], _, p => by simp [cwChunks, pure_apply, csum]
  | cc :: cs, k₀, p => by
    simp only [cwChunks, Ptr.adv_append, cwChunks_adv a cb rb z zk cs, loop_adv, csum_cons]
    simp [cwTpl, ltw, LRow.w, Row.w, Row.writes, pow_add]; constructor <;> ring

theorem CwAt.shift {R I pt : List FE} {w x : Nat → FE} {a be bk k₀ n : Nat}
    (h : CwAt M R I pt w x a be bk k₀ n) :
    CwAt M R I pt w x a (be + 2 * 2 ^ a * n) (bk + 2 * 2 ^ a * n) (k₀ + n) 0 := by
  intro q hq
  have := h q hq
  simp only [Nat.mul_zero, Nat.add_zero] at this ⊢
  rw [show be + 2 * 2 ^ a * n + 2 * q = be + (2 * q + 2 * 2 ^ a * n) by ring,
    show bk + 2 * 2 ^ a * n + 2 * q = bk + (2 * q + 2 * 2 ^ a * n) by ring]
  exact this

/-- **The chunks carry the values through every coordinate.** -/
theorem cwChunks_spec {a cb rb z zk K : Nat} {R I pt : List FE} {w x : Nat → FE}
    (hz : M.e z = 0) (hzk : M.k zk = 0)
    (hA : ∀ k < K, M.e (cb + 2 * k) = 1 + pt.getD k 0)
    (hB : ∀ k < K, M.e (cb + 2 * k + 1) = pt.getD k 0 * I.getD k 0)
    (hR : ∀ k < K, FE.ofK (M.k (rb + k)) = R.getD k 0) :
    ∀ (cs : List Nat) (k₀ : Nat) (p : Ptr), SegsHold c M p (cwChunks a cb rb z zk k₀ cs p).2 →
      k₀ + csum cs ≤ K → 2 * 2 ^ a ≤ p.e → 2 * 2 ^ a ≤ p.k →
      CwAt M R I pt w x a (p.e + 1 - 2 * 2 ^ a) (p.k + 1 - 2 * 2 ^ a) k₀ 0 →
      CwAt M R I pt w x a (p.e + 2 * 2 ^ a * csum cs + 1 - 2 * 2 ^ a)
        (p.k + 2 * 2 ^ a * csum cs + 1 - 2 * 2 ^ a) (k₀ + csum cs) 0
  | [], k₀, p, _, _, _, _, hin => by simpa [csum] using hin
  | cc :: cs, k₀, p, h, hK, hpe, hpk, hin => by
    simp only [cwChunks] at h
    rw [segsHold_append] at h
    rw [csum_cons] at hK ⊢
    have hc := cwChunk_spec (R := R) (I := I) (pt := pt) (w := w) (x := x) h.1 hpe hpk hz hzk
      (fun k hk => by rw [show cb + 2 * k₀ + 2 * k = cb + 2 * (k₀ + k) by ring]; exact hA _ (by omega))
      (fun k hk => by
        rw [show cb + 2 * k₀ + 1 + 2 * k = cb + 2 * (k₀ + k) + 1 by ring]; exact hB _ (by omega))
      (fun k hk => by rw [show rb + k₀ + k = rb + (k₀ + k) by ring]; exact hR _ (by omega))
      hin (2 ^ cc) le_rfl
    have hs := hc.shift
    have hp' : p.adv (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2 =
        ⟨p.k + 2 * 2 ^ a * 2 ^ cc, p.e + 2 * 2 ^ a * 2 ^ cc⟩ := by
      rw [loop_adv]; congr 1 <;> simp [cwTpl, ltw, LRow.w, Row.w, Row.writes, pow_add] <;> ring
    have ih := cwChunks_spec hz hzk hA hB hR cs (k₀ + 2 ^ cc) _ h.2 (by omega)
      (by rw [hp']; exact le_trans hpe (Nat.le_add_right _ _))
      (by rw [hp']; exact le_trans hpk (Nat.le_add_right _ _))
      (by
        rw [hp']; dsimp only
        have e1 : p.e + 2 * 2 ^ a * 2 ^ cc + 1 - 2 * 2 ^ a = p.e + 1 - 2 * 2 ^ a + 2 * 2 ^ a * 2 ^ cc := by
          omega
        have e2 : p.k + 2 * 2 ^ a * 2 ^ cc + 1 - 2 * 2 ^ a = p.k + 1 - 2 * 2 ^ a + 2 * 2 ^ a * 2 ^ cc := by
          omega
        rw [e1, e2]; exact hs)
    rw [hp'] at ih
    dsimp only at ih
    rw [show k₀ + (2 ^ cc + csum cs) = k₀ + 2 ^ cc + csum cs by ring,
      show p.e + 2 * 2 ^ a * (2 ^ cc + csum cs) = p.e + 2 * 2 ^ a * 2 ^ cc + 2 * 2 ^ a * csum cs by ring,
      show p.k + 2 * 2 ^ a * (2 ^ cc + csum cs) = p.k + 2 * 2 ^ a * 2 ^ cc + 2 * 2 ^ a * csum cs by ring]
    exact ih

/-- **The sum over the positions**: `Σ_q acc_q`, `acc_q` the `E` cell `base + 2q`. -/
theorem cwSum_spec {p : Ptr} {a n base : Nat} (h : SegsHold c M p (cwSum a n base p).2) (hp : 1 ≤ p.e)
    (hn : 1 ≤ n) (hna : n ≤ 2 ^ a) :
    (cwSum a n base p).1.val M = ∑ q ∈ Finset.range n, M.e (base + 2 * q) := by
  simp only [cwSum, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  have hs := lin_spec h.2
  simp only [add] at hs ⊢
  rw [hs]
  have hstep : ∀ x < 2 ^ a, M.e (p.e + 1 * x) = M.e (base + 2 * x) + M.e (p.e - 1 + 1 * x) := by
    intro x hx
    have hjf : x < 2 ^ [a].sum := by simpa using hx
    have hu : unflat [a] x = [x] := by simp [unflat, Nat.mod_eq_of_lt hx]
    have r := loop_rel h.1 (jf := x) (t := 0) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Opd.val_abs] at r
    rw [Opd.val_prev M _ hjf] at r
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, ofK_one,
      ofK_zero] at r
    simp only [Nat.one_mul]
    rw [r]
  have hpre := prefix_cells M.e p.e 1 (2 ^ a) hp (fun q => M.e (base + 2 * q)) hstep
  have hl := hpre n hna
  simp only [Nat.one_mul] at hl
  have hc : (LoopOut.cell ⟨p, [a], [⟨.lin 1 0, .E, [.abs ⟨.E, base, [2]⟩, .prev 0]⟩]⟩ 0 (n - 1)).val M
      = M.e (p.e - 1 + n) := by
    simp [LoopOut.cell_val, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Mem.rd_E]
    congr 1; omega
  simp only [loop_apply] at hc ⊢
  rw [hc, hl, ofK_one, ofK_zero, one_mul, add_zero, Cell.val_E, add_right_comm,
    CharTwo.add_self_eq_zero, zero_add]

/-- **The column weight gadget**: its cell is `Σ_q (iwSeq R I pt w_q x_q κ).1`, `κ = csum cs`. -/
theorem colWeight_spec {p : Ptr} {a n : Nat} {cs : List Nat} {ptb ib rb wb xb z zk : Nat}
    (h : SegsHold c M p (colWeight a n cs ptb ib rb wb xb z zk p).2) (hz : M.e z = 0) (hzk : M.k zk = 0)
    (hn : 1 ≤ n) (hna : n ≤ 2 ^ a)
    (R I pt : List FE)
    (hpt : ∀ k < csum cs, M.e (ptb + k) = pt.getD k 0)
    (hI : ∀ k < csum cs, FE.ofK (M.k (ib + k)) = I.getD k 0)
    (hR : ∀ k < csum cs, FE.ofK (M.k (rb + k)) = R.getD k 0) :
    (colWeight a n cs ptb ib rb wb xb z zk p).1.val M = ∑ q ∈ Finset.range n,
      (iwSeq R I pt (M.e (wb + q)) (FE.ofK (M.k (xb + q))) (csum cs)).1 := by
  simp only [colWeight, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil,
    Ptr.adv_nil] at h ⊢
  rw [segsHold_append, segsHold_append, segsHold_append] at h
  obtain ⟨hc, hpr, hch, hs⟩ := h
  rw [cwConstsAll_adv] at hpr hch hs ⊢
  rw [cwPro_adv] at hch hs ⊢
  rw [cwChunks_adv] at hs ⊢
  dsimp only at hch hs ⊢
  have hcon := cwConstsAll_spec ptb ib z cs 0 p hc
  have hA : ∀ k < csum cs, M.e (p.e + 2 * k) = 1 + pt.getD k 0 := fun k hk => by
    rw [(hcon k hk).1, Nat.add_zero, hpt k hk]
  have hB : ∀ k < csum cs, M.e (p.e + 2 * k + 1) = pt.getD k 0 * I.getD k 0 := fun k hk => by
    rw [(hcon k hk).2, Nat.add_zero, Nat.add_zero, hpt k hk, hI k hk, hz, add_zero]
  have hin : CwAt M R I pt (fun q => M.e (wb + q)) (fun q => FE.ofK (M.k (xb + q))) a
      (p.e + 2 * csum cs + 2 * 2 ^ a + 1 - 2 * 2 ^ a) (p.k + 2 * 2 ^ a + 1 - 2 * 2 ^ a) 0 0 := by
    intro q hq
    obtain ⟨h1, h2⟩ := cwPro_spec hpr hq
    simp only [Nat.mul_zero, Nat.add_zero, iwSeq]
    rw [show p.e + 2 * csum cs + 2 * 2 ^ a + 1 - 2 * 2 ^ a + 2 * q = p.e + 2 * csum cs + 1 + 2 * q by
      omega, show p.k + 2 * 2 ^ a + 1 - 2 * 2 ^ a + 2 * q = p.k + 1 + 2 * q by omega]
    exact ⟨h1, by rw [h2]⟩
  have hout := cwChunks_spec (c := c) (M := M) (K := csum cs) hz hzk hA hB
    (fun k hk => hR k hk) cs 0 _ hch (by simp) (by dsimp only; omega) (by dsimp only; omega) hin
  rw [cwSum_spec hs (by have := Nat.one_le_two_pow (n := a); dsimp only; omega) hn hna]
  refine Finset.sum_congr rfl fun q hq => ?_
  have := (hout q (lt_of_lt_of_le (Finset.mem_range.mp hq) hna)).1
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
  exact this

/-! ## Equivalence with `F` -/

theorem sum_zip_map (g : FE × Nat → FE) : ∀ (ws : List FE) (qs : List Nat), ws.length = qs.length →
    ((ws.zip qs).map g).sum = ∑ i ∈ Finset.range qs.length, g (ws.getD i 0, qs.getD i 0)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | w :: ws, q :: qs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
      Finset.sum_range_succ', List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_zip_map g ws qs (by simpa using h), add_comm]

/-- **`inducedWeight` as a sum over the positions** (`Finset` form). -/
theorem inducedWeight_sum (m : Nat) (qs : List Nat) (ws pt : List FE) (h : ws.length = qs.length) :
    inducedWeight m qs ws pt = ∑ i ∈ Finset.range qs.length,
      (iwSeq (iwRoots m) (iwInvs m) pt (ws.getD i 0) (eOfNat (qs.getD i 0)) pt.length).1 := by
  rw [inducedWeight_eq, sum_zip_map _ ws qs h]

/-- **Q_arith_eq, column weights**: the gadget over the positions `[q₀, q₀ + 2^a)` of a level is
their part of `F`'s `inducedWeight m qs ws pt` (`inducedWeight_sum`), when the weight cells hold
`ws`, the position cells hold `x_q = eOfNat q` (`K`), the point cells `pt`, and the constant cells
the roots and inverses of `subspaceRoots m` (`K`-valued: `iwRoots_isK`, `iwInvs_isK`). -/
theorem colWeight_eq {p : Ptr} {a n : Nat} {cs : List Nat} {ptb ib rb wb xb z zk : Nat}
    (h : SegsHold c M p (colWeight a n cs ptb ib rb wb xb z zk p).2) (hz : M.e z = 0) (hzk : M.k zk = 0)
    (hn : 1 ≤ n) (hna : n ≤ 2 ^ a)
    (m q₀ : Nat) (qs : List Nat) (ws pt : List FE) (hκ : csum cs = pt.length)
    (hpt : ∀ k < pt.length, M.e (ptb + k) = pt.getD k 0)
    (hI : ∀ k < pt.length, FE.ofK (M.k (ib + k)) = (iwInvs m).getD k 0)
    (hR : ∀ k < pt.length, FE.ofK (M.k (rb + k)) = (iwRoots m).getD k 0)
    (hw : ∀ q < n, M.e (wb + q) = ws.getD (q₀ + q) 0)
    (hx : ∀ q < n, FE.ofK (M.k (xb + q)) = eOfNat (qs.getD (q₀ + q) 0)) :
    (colWeight a n cs ptb ib rb wb xb z zk p).1.val M = ∑ q ∈ Finset.range n,
      (iwSeq (iwRoots m) (iwInvs m) pt (ws.getD (q₀ + q) 0) (eOfNat (qs.getD (q₀ + q) 0))
        pt.length).1 := by
  rw [colWeight_spec h hz hzk hn hna (iwRoots m) (iwInvs m) pt (hκ ▸ hpt) (hκ ▸ hI) (hκ ▸ hR), hκ]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [hw q (Finset.mem_range.mp hq), hx q (Finset.mem_range.mp hq)]

/-! ## The roots and inverses are `K` values (the constant cells exist) -/

theorem subspaceRootsAux_isK : ∀ (n : Nat) (last : FE) (layer : List FE), Program.IsK last →
    (∀ v ∈ layer, Program.IsK v) → ∀ r ∈ subspaceRootsAux n last layer, Program.IsK r
  | 0, _, _, _, _ => by simp [subspaceRootsAux]
  | n + 1, last, layer, hl, hv => by
    intro r hr
    have hmap : ∀ v ∈ layer.map (fun value => FE.sq value + last * value), Program.IsK v := by
      intro v hv'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv'
      rw [FE.sq_eq_mul]
      exact Program.isK_add (Program.isK_mul (hv u hu) (hv u hu)) (Program.isK_mul hl (hv u hu))
    simp only [subspaceRootsAux] at hr
    split at hr
    · simp at hr
    · next root rest heq =>
      rw [heq] at hmap
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hmap _ (by simp)
      · exact subspaceRootsAux_isK n root rest (hmap _ (by simp))
          (fun v hv => hmap v (by simp [hv])) r hr

theorem isK_zero : Program.IsK 0 := rfl

theorem iwRoots_isK (m k : Nat) : Program.IsK ((iwRoots m).getD k 0) := by
  have hall : ∀ r ∈ iwRoots m, Program.IsK r := by
    intro r hr
    simp only [iwRoots, subspaceRoots] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Program.isK_ofK 1
    · refine subspaceRootsAux_isK m 1 _ (Program.isK_ofK 1) (fun v hv => ?_) r hr
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
      exact Program.isK_ofK _
  rw [List.getD_eq_getElem?_getD]
  cases h : (iwRoots m)[k]? with
  | none => exact isK_zero
  | some r => exact hall r (List.mem_of_getElem? h)

theorem isK_inv {v : FE} (hv : Program.IsK v) : Program.IsK v⁻¹ := by
  unfold Program.IsK at hv ⊢
  have e : (FE.ofK v.c₀)⁻¹ = FE.ofK v.c₀⁻¹ := (map_inv₀ Lvm.FE.ofKRingHom v.c₀).symm
  rw [← hv, e]
  rfl

theorem iwInvs_isK (m k : Nat) : Program.IsK ((iwInvs m).getD k 0) := by
  simp only [iwInvs, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : (subspaceRoots m)[k]? with
  | none => exact isK_zero
  | some r =>
    have := iwRoots_isK m k
    simp only [iwRoots, List.getD_eq_getElem?_getD, h, Option.getD_some] at this
    simp only [Option.map_some, Option.getD_some]
    split
    · exact isK_zero
    · exact isK_inv this

end Lvm.Loop.Build
