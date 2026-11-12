-- New for lvm (V-PERF): the shipped `V_S` with its header-independent tables built once.
import LvmSubmissionS20
import LvmVFastQ

/-!
# A fast `V_S` at `P20`, equal to `VS20`

`VS20 = VSL P20 M3.tabsP20` builds the node program's tables `M3.tabsP20 pub` five times per check
(`M3.real`'s fields), and every build recomputes Q_link's static table `qltData` (≈ 4.5 s); the
closed forms of the position `BITS` classes call `posCell`/`ansLane` per cell, which walk the
schedule each time (≈ 67 s per sweep). Here:

* `posCellF`: `posCell` with its schedule-derived bases passed in (`posCellF_eq`);
* `tabA S W O`: a `BITS` table whose address columns read cached powers (`W` for the word's cell,
  `O[j]` for output `j`'s), equal to `S.tab` when the caches hold `x^cell` on the real rows
  (`tabA_eq`: `S.row x < max S.n 1`, so the columns are the same functions);
* `Pre`: the header-independent parts of `QAsm.tabs C G D pub` (groups, the input arrays but `PUB`,
  the aux tables with cached position classes); `tabsPre (pre C G D) C D pub = QAsm.tabs C G D pub`
  (`tabsPre_eq`);
* `pre20` (a top-level constant: compiled Lean evaluates it once, at initialisation), `tabs20F`,
  **`VS20F`** and **`VS20F_eq : VS20F = VS20`**; `T.submissionF` (`V := VS20F`) equals
  `T.submission` (`submissionF_eq`), so the certificate transfers by rewriting.
-/

set_option autoImplicit false

namespace Lvm.VF

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.SigBits Lvm.QAsm

/-! ## L2 (V-LEV): the groups' coefficients precomputed, the MLE folded on arrays

`mleF r f` recurses through `|r|` nested closures per leaf and `coefF` re-reads the static
coefficients on every check. Here the coefficients of each (piece, column) are computed once, at
start-up (`leafT`), and the MLE halves an array (`mleE`); when every coefficient lies in `K` the first
layer is `E × K` (`mleK`, `smulBase`). `mleE_eq`, `mleK_eq`: they are `mleF`. -/

theorem mleF_congr : ∀ (r : List FE) (f g : Nat → FE), (∀ i < 2 ^ r.length, f i = g i) → mleF r f = mleF r g
  | [], f, g, h => h 0 (by simp)
  | r :: rs, f, g, h => by
    have h2 : 2 ^ (rs.length + 1) = 2 * 2 ^ rs.length := by rw [Nat.pow_succ]; ring
    simp only [mleF]
    rw [mleF_congr rs (fun x => f (2 * x)) (fun x => g (2 * x))
          (fun i hi => h _ (by simp only [List.length_cons, h2]; omega)),
        mleF_congr rs (fun x => f (2 * x + 1)) (fun x => g (2 * x + 1))
          (fun i hi => h _ (by simp only [List.length_cons, h2]; omega))]

theorem mleF_lin (r0 : FE) : ∀ (rs : List FE) (a b : Nat → FE),
    mleF rs (fun x => a x + r0 * (b x - a x)) = mleF rs a + r0 * (mleF rs b - mleF rs a)
  | [], _, _ => rfl
  | r :: rs, a, b => by
    simp only [mleF]
    rw [mleF_lin r0 rs (fun x => a (2 * x)) (fun x => b (2 * x)),
      mleF_lin r0 rs (fun x => a (2 * x + 1)) (fun x => b (2 * x + 1))]
    ring

/-- One halving: `v'[i] = v[2i] + r·(v[2i+1] − v[2i])`, `n` entries. -/
def halveE (r : FE) (v : Array FE) (n : Nat) : Array FE :=
  Array.ofFn (n := n) fun i => let a := v.getD (2 * i.val) 0; a + r * (v.getD (2 * i.val + 1) 0 - a)

/-- **The MLE of an array** (low variable first, `mleF`'s order), by halving. -/
def mleE : List FE → Array FE → FE
  | [], v => v.getD 0 0
  | r :: rs, v => mleE rs (halveE r v (2 ^ rs.length))

theorem getD_ofFn {α : Type} (n i : Nat) (f : Fin n → α) (d : α) (h : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem mleE_eq : ∀ (r : List FE) (v : Array FE), mleE r v = mleF r (fun i => v.getD i 0)
  | [], _ => rfl
  | r :: rs, v => by
    simp only [mleE, mleF]
    rw [mleE_eq rs, ← mleF_lin r rs]
    exact mleF_congr rs _ _ fun i hi => by unfold halveE; rw [getD_ofFn _ _ _ _ hi]

/-- The first halving from `K` leaves: `v'[i] = A[2i] + (A[2i+1] − A[2i])·r` (`E × K`). -/
def halveK (r : FE) (A : Array FK) (n : Nat) : Array FE :=
  Array.ofFn (n := n) fun i => let a := A.getD (2 * i.val) 0; FE.ofK a + FE.smulBase (A.getD (2 * i.val + 1) 0 - a) r

/-- **The MLE of `K` leaves.** -/
def mleK : List FE → Array FK → FE
  | [], A => FE.ofK (A.getD 0 0)
  | r :: rs, A => mleE rs (halveK r A (2 ^ rs.length))

theorem mleK_eq (r : List FE) (A : Array FK) : mleK r A = mleF r (fun i => FE.ofK (A.getD i 0)) := by
  cases r with
  | nil => rfl
  | cons r rs =>
    simp only [mleK, mleF]
    rw [mleE_eq rs, ← mleF_lin r rs]
    refine mleF_congr rs _ _ fun i hi => ?_
    unfold halveK
    rw [getD_ofFn _ _ _ _ hi]
    simp only [FE.smulBase_eq_mul, ← FE.algebraMap_eq_ofK, map_sub]
    ring

/-! ## Cached `BITS` tables -/

/-- An address column read from a cache `A` of powers (row `x` uses `A[S.row x]`). -/
def adrColA (S : BSpec) (A : Array FK) : ColSrc :=
  let P := Array.ofFn (n := 2 ^ S.τ) fun x => A.getD (S.row x.val) 0
  .fix (fun x => A.getD (S.row x) 0) fun r =>
    if r.length ≤ S.τ then mleK r P else mleF r fun x => FE.ofK (A.getD (S.row x) 0)

/-- Column `c` of the cached table (`BSpec.col` with the caches). -/
def colA (S : BSpec) (W : Array FK) (O : Array (Array FK)) (c : Nat) : ColSrc :=
  if c = 66 then adrColA S W
  else if 68 ≤ c ∧ c % 2 = 0 then adrColA S (O.getD ((c - 68) / 2) #[])
  else .com (S.pl c).1 (S.pl c).2

/-- **The cached `BITS` table** (`BSpec.tab` with `colA`). -/
def tabA (S : BSpec) (W : Array FK) (O : Array (Array FK)) : Tab where
  τ := S.τ
  cols := (List.range S.width).map (colA S W O)
  cons := cons
  reads := S.reads
  seeds := []
  deg := S.tab.deg

theorem row_lt (S : BSpec) (x : Nat) : S.row x < max S.n 1 := by
  unfold BSpec.row; split <;> omega

theorem adrColA_eq (S : BSpec) (A : Array FK) (a : Nat → Nat)
    (h : ∀ x < max S.n 1, A.getD x 0 = FK.x ^ a x) : adrColA S A = S.adrCol a := by
  have h' : ∀ x, A.getD (S.row x) 0 = FK.x ^ a (S.row x) := fun x => h _ (row_lt S x)
  unfold adrColA BSpec.adrCol
  simp only [h']
  refine congrArg (ColSrc.fix _) (funext fun r => ?_)
  split
  · rename_i hle
    rw [mleK_eq, ← mleF_eq]
    refine mleF_congr r _ _ fun i hi => ?_
    rw [getD_ofFn _ _ _ _ (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hle))]
  · rw [mleF_eq]

/-- **The cached table is the table** when the caches hold the powers of the real rows' cells. -/
theorem tabA_eq (S : BSpec) (W : Array FK) (O : Array (Array FK))
    (hW : ∀ x < max S.n 1, W.getD x 0 = FK.x ^ S.wc x)
    (hO : ∀ j < S.outs.length, ∀ x < max S.n 1, (O.getD j #[]).getD x 0 = FK.x ^ S.oc j x) :
    tabA S W O = S.tab := by
  have hc : (List.range S.width).map (colA S W O) = (List.range S.width).map S.col := by
    apply List.map_congr_left
    intro c hc
    rw [List.mem_range] at hc
    unfold colA BSpec.col
    by_cases h1 : c = 66
    · rw [if_pos h1, if_pos h1]; exact adrColA_eq S W S.wc hW
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : 68 ≤ c ∧ c % 2 = 0
      · rw [if_pos h2, if_pos h2]
        refine adrColA_eq S _ _ fun x hx => hO _ ?_ x hx
        unfold BSpec.width at hc; omega
      · rw [if_neg h2, if_neg h2]
  unfold tabA BSpec.tab
  rw [hc]

theorem getD_map_toArray {α β : Type} (f : α → β) (l : List α) (j : Nat) (d : β) (h : j < l.length) :
    (l.map f).toArray.getD j d = f l[j] := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_range {α : Type} (g : Nat → α) (m x : Nat) (d : α) (h : x < m) :
    ((List.range m).map g).toArray.getD x d = g x := by
  simp [Array.getD, h]

/-- **Any `BITS` class, cached** (L1, V-LEV): its address powers computed once. -/
def cacheTab (S : BSpec) : Tab :=
  let m := max S.n 1
  tabA S ((List.range m).map fun x => FK.x ^ S.wc x).toArray
    ((List.range S.outs.length).map fun j => ((List.range m).map fun x => FK.x ^ S.oc j x).toArray).toArray

theorem cacheTab_eq (S : BSpec) : cacheTab S = S.tab :=
  tabA_eq S _ _ (fun x hx => getD_range _ _ _ _ hx)
    (fun j hj x hx => by rw [getD_range _ _ _ _ hj, getD_range _ _ _ _ hx])

/-! ## `posCell` with its bases passed in -/

/-- `posCell C k o x` with `bb = bitBase`, `sb = spB C + spBefore`, `fl = flB C`, `pa2 = 2^pa`,
`px = posIdx … k 0` (`H`, `t`, `pT`, `nR` the opening's height, `t`, `padT t`, `nRows`). -/
def posCellF (H t pT nR bb sb fl pa2 px x : Nat) : BOut × Nat × Nat → Nat
  | (_, 0, n) =>
    let j := 8 * x + n / H
    if j < pT then bb + H * j + n % H else sb + 2 * (8 * nR - t) + H * (j - pT) + n % H
  | (_, kind, i) =>
    let j := 8 * x + i
    if j < t then fl + (if kind = 1 then 0 else pa2) + (px + j) else sb + 2 * (j - t) + (kind - 1)

theorem posCellF_eq (C : QCfg) (k : Nat) (o : OpenInfo) (x : Nat) (u : BOut × Nat × Nat) :
    posCellF o.L.height o.L.t (padT o.L.t) (nRows o) (bitBase C.p (lay C) k)
      (spB C + spBefore C.p k) (flB C) (2 ^ C.pa) (posIdx C.p k 0) x u = posCell C k o x u := by
  obtain ⟨b, kind, n⟩ := u
  cases kind with
  | zero => rfl
  | succ kind =>
    have hp : posIdx C.p k (8 * x + n) = posIdx C.p k 0 + (8 * x + n) := by unfold posIdx; omega
    simp only [posCellF, posCell]
    rw [hp]

/-- `posOc C l U r j` with the column's output `u = U[j]`, the opening's bases
`b = (bitBase, spB + spBefore, posIdx … 0)`, its row's outputs `LO = laneOuts H l`, `fl = flB C` and
`pa2 = 2^pa` passed in. -/
def posOcF (l : Nat) (u : BOut) (LO : List (BOut × Nat × Nat)) (fl pa2 : Nat) (b : Nat × Nat × Nat)
    (r : Nat × OpenInfo × Nat × Nat) (j : Nat) : Nat :=
  match LO.find? (fun e => e.1 == u) with
  | some e => posCellF r.2.1.L.height r.2.1.L.t (padT r.2.1.L.t) (nRows r.2.1) b.1 b.2.1 fl pa2 b.2.2 r.2.2.1 e
  | none => r.2.2.2 + (j - QAsm.laneBits r.2.1.L.height l)

theorem posOcF_eq (C : QCfg) (l : Nat) (U : List BOut) (r : Nat × OpenInfo × Nat × Nat) (j : Nat) :
    posOcF l (U.getD j (.bit 0)) (laneOuts r.2.1.L.height l) (flB C) (2 ^ C.pa)
      (bitBase C.p (lay C) r.1, spB C + spBefore C.p r.1, posIdx C.p r.1 0) r j = posOc C l U r j := by
  unfold posOcF posOc
  generalize (laneOuts r.2.1.L.height l).find? (fun e => e.1 == U.getD j (.bit 0)) = d
  cases d with
  | none => rfl
  | some e => exact posCellF_eq C r.1 r.2.1 r.2.2.1 e

/-- **The position classes' tables, cached** (`posSpecs`' lane classes; caches over `max n 1` rows; the
openings' bases computed once). -/
def posTabsA (C : QCfg) (bpl : Nat → Nat → Bool × Nat) : List Tab :=
  let O0 := offs C.p
  let PA := (plan C.p).toArray
  let fl := flB C
  let pa2 := 2 ^ C.pa
  let BA := ((List.range (opens C.p).length).map fun k =>
    (bitBase C.p (lay C) k, spB C + spBefore C.p k, posIdx C.p k 0)).toArray
  let bs : Nat → Nat × Nat × Nat := fun k => match BA[k]? with
    | some b => b
    | none => (bitBase C.p (lay C) k, spB C + spBefore C.p k, posIdx C.p k 0)
  (List.range (nPosCls C)).map fun l =>
    let U := lnOuts C.p l
    let UA := U.toArray
    let R := posRows C l
    let RA := R.toArray
    let m := max R.length 1
    let RD := ((List.range m).map fun y => let r := RA.getD y default;
      (r, laneOuts r.2.1.L.height l, bs r.1)).toArray
    let W := ((List.range m).map fun y => let r := (RD.getD y default).1;
      FK.x ^ (ansLaneF O0 PA C.p (r.2.1.pe + r.2.2.1) + l)).toArray
    let O := ((List.range U.length).map fun j => ((List.range m).map fun y =>
      let d := RD.getD y default; FK.x ^ posOcF l (UA.getD j (.bit 0)) d.2.1 fl pa2 d.2.2 d.1 j).toArray).toArray
    tabA (posSpec C bpl l) W O

theorem posTabsA_eq (C : QCfg) (bpl : Nat → Nat → Bool × Nat) :
    posTabsA C bpl = (posSpecs C bpl).map BSpec.tab := by
  have hbs : ∀ k, (match (((List.range (opens C.p).length).map fun k =>
      (bitBase C.p (lay C) k, spB C + spBefore C.p k, posIdx C.p k 0)).toArray)[k]? with
    | some b => b
    | none => (bitBase C.p (lay C) k, spB C + spBefore C.p k, posIdx C.p k 0)) =
      (bitBase C.p (lay C) k, spB C + spBefore C.p k, posIdx C.p k 0) := fun k => by
    rw [List.getElem?_toArray, List.getElem?_map]
    by_cases hk : k < (opens C.p).length <;> simp [hk]
  unfold posTabsA posSpecs
  rw [List.map_map]
  apply List.map_congr_left
  intro l _
  simp only [Function.comp]
  apply tabA_eq
  · intro y hy
    rw [posSpec_n] at hy
    rw [posSpec_wc]
    simp only [getD_range _ _ _ _ hy, ansLaneF_eq']
    simp only [toArray_getD]
  · intro j hj y hy
    rw [posSpec_n] at hy
    rw [posSpec_outs] at hj
    rw [posSpec_oc, getD_map_toArray _ _ j _ (by simpa using hj)]
    simp only [List.getElem_range, getD_range _ _ _ _ hy, hbs]
    simp only [toArray_getD, posOcF_eq]

/-- The aux tables with the position classes cached (then the `s'` bit class `sSpec` and the PoW class
`powSpec`). -/
def auxF (C : QCfg) (D : QData) : List Tab :=
  (sigSpecs (sigIn C) (sigOut C) (bplOf D)).map cacheTab ++ posTabsA C (fun c => bplOf D (6 + c)) ++
    [cacheTab (sSpec C (bplOf D (6 + nPosCls C))), cacheTab (powSpec C (bplOf D (7 + nPosCls C)))]

theorem auxF_eq (C : QCfg) (D : QData) : auxF C D = aux C D := by
  unfold auxF aux bspecs
  rw [show cacheTab = BSpec.tab from funext cacheTab_eq, List.map_append, List.map_append, posTabsA_eq]
  rfl

/-! ## Group closed forms with a box memo

A piece's `res`/`arg` closed form is `Σ_i eq(r_I, i)·coef_i·boxEval(dims, s_i, r_J)`; in the node
program every row of a column has the same strides `s_i` (QA1's Keccak layer: 1,024 rows), so the box
value is computed once per column (`boxMemo`, at most 8 stride lists) and looked up per row. -/

/-- Up to 8 stride lists with their box values at `rJ`. -/
def boxMemo (dims : List Nat) (rJ : List FE) (ss : List (List Nat)) : List (List Nat × FE) :=
  ss.foldl (fun acc s => if acc.length < 8 && !(acc.any (·.1 == s)) then (s, boxEval dims s rJ) :: acc else acc) []

theorem boxMemo_ok (dims : List Nat) (rJ : List FE) :
    ∀ (ss : List (List Nat)) (acc : List (List Nat × FE)), (∀ e ∈ acc, e.2 = boxEval dims e.1 rJ) →
      ∀ e ∈ ss.foldl (fun acc s => if acc.length < 8 && !(acc.any (·.1 == s)) then
        (s, boxEval dims s rJ) :: acc else acc) acc, e.2 = boxEval dims e.1 rJ
  | [], _, h => h
  | s :: ss, acc, h => by
    simp only [List.foldl_cons]
    apply boxMemo_ok dims rJ ss
    split
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact h e he
    · exact h

/-- The box value of `s` from the memo (computed when absent). -/
def boxLook (M : List (List Nat × FE)) (dims s : List Nat) (rJ : List FE) : FE :=
  match M.find? (fun e => e.1 == s) with
  | some e => e.2
  | none => boxEval dims s rJ

theorem boxLook_eq (M : List (List Nat × FE)) (dims s : List Nat) (rJ : List FE)
    (h : ∀ e ∈ M, e.2 = boxEval dims e.1 rJ) : boxLook M dims s rJ = boxEval dims s rJ := by
  unfold boxLook
  split
  · rename_i e he
    have hs : e.1 = s := by simpa using List.find?_some he
    rw [h e (List.mem_of_find?_eq_some he), hs]
  · rfl

/-- `boxMul` with the memo. -/
def boxMulM (M : List (List Nat × FE)) (a : FE) (dims s : List Nat) (r : List FE) : FE :=
  match dims with
  | [] => a
  | _ :: _ => a * boxLook M dims s r

theorem boxMulM_memo (dims : List Nat) (rJ : List FE) (ss : List (List Nat)) (a : FE) (s : List Nat) :
    boxMulM (boxMemo dims rJ ss) a dims s rJ = boxMul a dims s rJ := by
  cases dims with
  | nil => rfl
  | cons d ds =>
    simp only [boxMulM, boxMul]
    rw [boxLook_eq _ _ _ _ (by unfold boxMemo; exact boxMemo_ok (d :: ds) rJ ss [] (by simp))]

/-- `pieceEvalG` with the box memo. -/
def pieceEvalGM (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  let bc := G.C.bc pe.p.blk
  let rJ := r.take bc.B.lsize
  let rI := r.drop bc.B.lsize
  match c with
  | .res | .arg _ =>
    let M := boxMemo bc.B.dims rJ ((List.range pe.ts.size).map fun i => (colAffineF bc c (pe.ts.getD i 0)).2)
    mleF rI fun i => boxMulM M (coefF bc pe c i) bc.B.dims (colAffineF bc c (pe.ts.getD i 0)).2 rJ
  | .k | .k' => mleF rI (coefF bc pe c)
  | .F => 0

theorem pieceEvalGM_eq (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : pieceEvalGM G pe c r = pieceEvalG G pe c r := by
  cases c <;> simp only [pieceEvalGM, pieceEvalG, boxMulM_memo]

/-- `pieceFixEvalG` with the box memo. -/
def pieceFixEvalGM (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  match c with
  | .F => fixFEvalG G pe.p r
  | c => pieceEvalGM G pe c r

theorem pieceFixEvalGM_eq (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) :
    pieceFixEvalGM G pe c r = pieceFixEvalG G pe c r := by
  cases c <;> simp only [pieceFixEvalGM, pieceFixEvalG, pieceEvalGM_eq]

/-- **`grpEvalG` with the box memo.** -/
def grpEvalGM (G : PG) (g : Grp) (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let pe := G.pe n
    let h := heightF G.C pe.p
    eqSel (off >>> h) (r.drop h) * pieceFixEvalGM G pe c (r.take h)).foldl (· + ·) 0

theorem grpEvalGM_eq (G : PG) (g : Grp) : grpEvalGM G g = grpEvalG G g := by
  funext c r
  unfold grpEvalGM grpEvalG
  refine congrArg (List.foldl (· + ·) 0) ?_
  apply List.map_congr_left
  rintro ⟨n, off⟩ -
  simp only [pieceFixEvalGM_eq]

/-! ## Uniform strides: one `mleF` over the coefficients

When every template row of a piece has the same strides `s₀` in a column, its closed form is
`boxMul (mleF r_I coef) dims s₀ r_J` (`mleF` is linear). `unifS` decides it once per piece and
column (a table built with the parts, `unifT`). -/

theorem mleF_mul (B : FE) : ∀ (r : List FE) (f : Nat → FE), mleF r (fun i => f i * B) = mleF r f * B
  | [], _ => rfl
  | r :: rs, f => by
    simp only [mleF]
    rw [mleF_mul B rs (fun x => f (2 * x)), mleF_mul B rs (fun x => f (2 * x + 1))]
    ring

theorem mleF_boxMul (r rJ : List FE) (f : Nat → FE) (dims s : List Nat) :
    mleF r (fun i => boxMul (f i) dims s rJ) = boxMul (mleF r f) dims s rJ := by
  cases dims with
  | nil => rfl
  | cons d ds => exact mleF_mul _ r f

/-- A column's strides when every template row of the piece has the same ones. -/
def unifS (G : PG) (pe : M3.PE) (c : FCol) : Option (List Nat) :=
  match (List.range pe.ts.size).map (fun i => (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2) with
  | [] => none
  | s0 :: ss =>
    if ss.all (· == s0) && (colAffineF (G.C.bc pe.p.blk) c 0).2 == s0 then some s0 else none

theorem unifS_spec (G : PG) (pe : M3.PE) (c : FCol) (s0 : List Nat) (h : unifS G pe c = some s0) (i : Nat) :
    (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2 = s0 := by
  unfold unifS at h
  generalize hl : (List.range pe.ts.size).map (fun i => (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2) = l at h
  cases l with
  | nil => simp at h
  | cons a ss =>
    simp only at h
    split at h
    · rename_i hall'
      obtain rfl := Option.some.inj h
      have hall : (ss.all fun x => x == a) = true := by simp only [Bool.and_eq_true] at hall'; exact hall'.1
      have h0' : (colAffineF (G.C.bc pe.p.blk) c 0).2 = a := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hall'; exact hall'.2
      have hpos : 0 < pe.ts.size := by
        have := congrArg List.length hl; simp at this; omega
      -- every listed row's strides are `a`
      have hrow : ∀ j < pe.ts.size, (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD j 0)).2 = a := by
        intro j hj
        have hm : (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD j 0)).2 ∈ a :: ss := by
          rw [← hl]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
        rcases List.mem_cons.mp hm with he | he
        · exact he
        · have := List.all_eq_true.mp hall _ he; simpa using this
      by_cases hi : i < pe.ts.size
      · exact hrow i hi
      · have h0 : pe.ts.getD i 0 = 0 := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
        rw [h0]; exact h0'
    · simp at h

/-- `pieceEvalGM` with a uniform-stride hint `u` (`unifS`, or `none`). -/
def pieceEvalGU (u : Option (List Nat)) (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  match c, u with
  | .res, some s0 | .arg _, some s0 =>
    let bc := G.C.bc pe.p.blk
    boxMul (mleF (r.drop bc.B.lsize) (coefF bc pe c)) bc.B.dims s0 (r.take bc.B.lsize)
  | c, _ => pieceEvalGM G pe c r

theorem pieceEvalGU_eq (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) (u : Option (List Nat))
    (hu : ∀ s0, u = some s0 → unifS G pe c = some s0) : pieceEvalGU u G pe c r = pieceEvalG G pe c r := by
  cases u with
  | none => cases c <;> simp only [pieceEvalGU, pieceEvalGM_eq]
  | some s0 =>
    have hs := unifS_spec G pe c s0 (hu s0 rfl)
    cases c with
    | res => simp only [pieceEvalGU, pieceEvalG, hs, mleF_boxMul]
    | arg o => simp only [pieceEvalGU, pieceEvalG, hs, mleF_boxMul]
    | k => simp only [pieceEvalGU, pieceEvalGM_eq]
    | k' => simp only [pieceEvalGU, pieceEvalGM_eq]
    | F => simp only [pieceEvalGU, pieceEvalGM_eq]

/-- A row's strides for column `c`: `colAffineF`'s second part without its first (whose `BC.rank` takes
the template list's length: quadratic over a glue piece, ≈ 5 s of `pre20`). -/
def stridesOf (bc : BC) (c : FCol) (t : Nat) : List Nat :=
  let r := bc.tpl.getD t default
  match c with
  | .res => Loop.scaledStrides bc.B.dims (bc.tw r.ty)
  | .arg o => (r.args.getD o default).strides
  | _ => []

theorem stridesOf_eq (bc : BC) (c : FCol) (t : Nat) : stridesOf bc c t = (colAffineF bc c t).2 := by
  unfold stridesOf colAffineF; cases c <;> rfl

/-- `unifS` on `stridesOf`. -/
def unifSF (G : PG) (pe : M3.PE) (c : FCol) : Option (List Nat) :=
  match (List.range pe.ts.size).map (fun i => stridesOf (G.C.bc pe.p.blk) c (pe.ts.getD i 0)) with
  | [] => none
  | s0 :: ss =>
    if ss.all (· == s0) && stridesOf (G.C.bc pe.p.blk) c 0 == s0 then some s0 else none

theorem unifSF_eq : unifSF = unifS := by
  funext G pe c
  unfold unifSF unifS
  simp only [stridesOf_eq]

/-- Per piece, the uniform strides of its columns (`unifS`), built once. -/
def unifT (G : PG) : Array (List (FCol × Option (List Nat))) :=
  G.pes.map fun pe => [.res, .arg 0, .arg 1, .arg 2].map fun c => (c, unifSF G pe c)

/-- The hint for piece `n`, column `c`. -/
def unifH (U : Array (List (FCol × Option (List Nat)))) (n : Nat) (c : FCol) : Option (List Nat) :=
  match (U.getD n []).find? (fun x => x.1 == c) with
  | some x => x.2
  | none => none

theorem unifH_spec (G : PG) (n : Nat) (c : FCol) (s0 : List Nat) (h : unifH (unifT G) n c = some s0) :
    unifS G (G.pe n) c = some s0 := by
  unfold unifH at h
  split at h
  · rename_i x hx
    have hm := List.mem_of_find?_eq_some hx
    have hc : x.1 = c := by simpa using List.find?_some hx
    by_cases hn : n < G.pes.size
    · have hU : (unifT G).getD n [] = [.res, .arg 0, .arg 1, .arg 2].map fun c => (c, unifS G G.pes[n] c) := by
        simp [unifT, Array.getD_eq_getD_getElem?, hn, unifSF_eq]
      rw [hU] at hm
      obtain ⟨c', -, rfl⟩ := List.mem_map.mp hm
      simp only at hc h; subst hc
      have hpe : G.pe n = G.pes[n] := by unfold PG.pe; rw [dif_pos hn]
      rw [hpe]; exact h
    · have hU : (unifT G).getD n [] = [] := by
        simp [unifT, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hn)]
      rw [hU] at hm; simp at hm
  · simp at h

/-- `pieceFixEvalGM` with the hints. -/
def pieceFixEvalGU (U : Array (List (FCol × Option (List Nat)))) (n : Nat) (G : PG) (pe : M3.PE) (c : FCol)
    (r : List FE) : FE :=
  match c with
  | .F => fixFEvalG G pe.p r
  | c => pieceEvalGU (unifH U n c) G pe c r

/-- **`grpEvalG` with the uniform-stride hints.** -/
def grpEvalGU (U : Array (List (FCol × Option (List Nat)))) (G : PG) (g : Grp) (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let pe := G.pe n
    let h := heightF G.C pe.p
    eqSel (off >>> h) (r.drop h) * pieceFixEvalGU U n G pe c (r.take h)).foldl (· + ·) 0

theorem grpEvalGU_eq (G : PG) (g : Grp) : grpEvalGU (unifT G) G g = grpEvalG G g := by
  funext c r
  unfold grpEvalGU grpEvalG
  refine congrArg (List.foldl (· + ·) 0) ?_
  apply List.map_congr_left
  rintro ⟨n, off⟩ -
  have hp : ∀ r', pieceFixEvalGU (unifT G) n G (G.pe n) c r' = pieceFixEvalG G (G.pe n) c r' := by
    intro r'
    cases c <;> simp only [pieceFixEvalGU, pieceFixEvalG] <;>
      exact pieceEvalGU_eq G _ _ r' _ (unifH_spec G n _)
  simp only [hp]

/-- A (piece, column)'s coefficients: `2^a` of them as `E`, and as `K` when they all are. -/
structure Leaves where
  /-- The template rows' log-count. -/
  a : Nat
  /-- The coefficients. -/
  e : Array FE
  /-- The coefficients' `K` limbs, when every coefficient is in `K`. -/
  k : Option (Array FK)

/-- `K` leaves when every coefficient is `ofK`. -/
def kLeaves (e : Array FE) : Option (Array FK) :=
  if e.all (fun x => x.c₁ == 0 && x.c₂ == 0) then some (e.map (·.c₀)) else none

theorem kLeaves_spec (e : Array FE) (A : Array FK) (h : kLeaves e = some A) (i : Nat) :
    FE.ofK (A.getD i 0) = e.getD i 0 := by
  unfold kLeaves at h
  split at h
  · rename_i hall
    obtain rfl := Option.some.inj h
    by_cases hi : i < e.size
    · have hx := Array.all_eq_true.mp hall i hi
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi, Option.map_some,
        Option.getD_some]
      cases hy : e[i] with
      | mk a b c => rw [hy] at hx; simp only at hx; obtain ⟨rfl, rfl⟩ := hx; rfl
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_none (show e.size ≤ i by omega), Option.map_none, Option.getD_none]
      rfl
  · simp at h

/-- The MLE of the leaves (the `K` path when available). -/
def leafMle (L : Leaves) (r : List FE) : FE :=
  match L.k with
  | some A => mleK r A
  | none => mleE r L.e

theorem leafMle_eq (L : Leaves) (hk : L.k = kLeaves L.e) (r : List FE) :
    leafMle L r = mleF r (fun i => L.e.getD i 0) := by
  unfold leafMle
  split
  · rename_i A hA
    rw [mleK_eq]
    exact mleF_congr r _ _ fun i _ => kLeaves_spec L.e A (hk ▸ hA) i
  · exact mleE_eq r L.e

/-- The leaves of piece entry `pe`, column `c` (`2^a` coefficients). -/
def leavesOf (G : PG) (pe : M3.PE) (c : FCol) : Leaves :=
  let bc := G.C.bc pe.p.blk
  let e := Array.ofFn (n := 2 ^ pe.p.a) fun i => coefF bc pe c i.val
  ⟨pe.p.a, e, kLeaves e⟩

theorem leaves_mle (G : PG) (pe : M3.PE) (c : FCol) (rI : List FE) (h : rI.length ≤ pe.p.a) :
    leafMle (leavesOf G pe c) rI = mleF rI (coefF (G.C.bc pe.p.blk) pe c) := by
  rw [leafMle_eq _ rfl]
  refine mleF_congr rI _ _ fun i hi => ?_
  have hi' : i < 2 ^ pe.p.a := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) h)
  simp only [leavesOf]
  rw [getD_ofFn _ _ _ _ hi']

/-- `pieceEvalGU` on precomputed leaves `L` (= `leavesOf G pe c` when present). -/
def pieceEvalGL (L : Option Leaves) (u : Option (List Nat)) (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  match L with
  | none => pieceEvalGU u G pe c r
  | some lv =>
    let bc := G.C.bc pe.p.blk
    let rI := r.drop bc.B.lsize
    if rI.length ≤ lv.a then
      match c, u with
      | .res, some s0 | .arg _, some s0 => boxMul (leafMle lv rI) bc.B.dims s0 (r.take bc.B.lsize)
      | .k, _ | .k', _ => leafMle lv rI
      | _, _ => pieceEvalGU u G pe c r
    else pieceEvalGU u G pe c r

theorem pieceEvalGL_eq (L : Option Leaves) (u : Option (List Nat)) (G : PG) (pe : M3.PE) (c : FCol) (r : List FE)
    (hL : ∀ lv, L = some lv → lv = leavesOf G pe c) : pieceEvalGL L u G pe c r = pieceEvalGU u G pe c r := by
  cases L with
  | none => rfl
  | some lv =>
    obtain rfl := hL lv rfl
    simp only [pieceEvalGL]
    split
    · rename_i hle
      have hm := leaves_mle G pe c _ hle
      cases c with
      | res => cases u with
        | none => rfl
        | some s0 => simp only [hm, pieceEvalGU]
      | arg o => cases u with
        | none => rfl
        | some s0 => simp only [hm, pieceEvalGU]
      | k => cases u <;> simp only [hm, pieceEvalGU, pieceEvalGM]
      | k' => cases u <;> simp only [hm, pieceEvalGU, pieceEvalGM]
      | F => cases u <;> rfl
    · rfl

/-- Per piece, the leaves of its fixed columns (but `F`), built once. -/
def leafT (G : PG) : Array (List (FCol × Leaves)) :=
  G.pes.map fun pe => (pe.p.shape.fcols.filter (· != .F)).map fun c => (c, leavesOf G pe c)

/-- The leaves of piece `n`, column `c`. -/
def leafH (LT : Array (List (FCol × Leaves))) (n : Nat) (c : FCol) : Option Leaves :=
  ((LT.getD n []).find? (fun x => x.1 == c)).map (·.2)

theorem leafH_spec (G : PG) (n : Nat) (c : FCol) (lv : Leaves) (h : leafH (leafT G) n c = some lv) :
    lv = leavesOf G (G.pe n) c := by
  unfold leafH at h
  cases hx : (((leafT G).getD n []).find? (fun x => x.1 == c)) with
  | none => rw [hx] at h; simp at h
  | some x =>
    rw [hx] at h
    simp only [Option.map_some] at h
    obtain rfl := Option.some.inj h
    have hm := List.mem_of_find?_eq_some hx
    have hc : x.1 = c := by simpa using List.find?_some hx
    by_cases hn : n < G.pes.size
    · have hU : (leafT G).getD n [] =
          (G.pes[n].p.shape.fcols.filter (· != .F)).map fun c => (c, leavesOf G G.pes[n] c) := by
        simp [leafT, Array.getD_eq_getD_getElem?, hn]
      rw [hU] at hm
      obtain ⟨c', -, rfl⟩ := List.mem_map.mp hm
      simp only at hc; subst hc
      have hpe : G.pe n = G.pes[n] := by unfold PG.pe; rw [dif_pos hn]
      rw [hpe]
    · have hU : (leafT G).getD n [] = [] := by
        simp [leafT, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hn)]
      rw [hU] at hm; simp at hm

/-- `pieceFixEvalGU` with the leaves. -/
def pieceFixEvalGL (LT : Array (List (FCol × Leaves))) (U : Array (List (FCol × Option (List Nat)))) (n : Nat)
    (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  match c with
  | .F => fixFEvalG G pe.p r
  | c => pieceEvalGL (leafH LT n c) (unifH U n c) G pe c r

/-- **`grpEvalG` with the leaves and the uniform-stride hints.** -/
def grpEvalGL (LT : Array (List (FCol × Leaves))) (U : Array (List (FCol × Option (List Nat)))) (G : PG) (g : Grp)
    (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let pe := G.pe n
    let h := heightF G.C pe.p
    eqSel (off >>> h) (r.drop h) * pieceFixEvalGL LT U n G pe c (r.take h)).foldl (· + ·) 0

theorem grpEvalGL_eq (G : PG) (g : Grp) : grpEvalGL (leafT G) (unifT G) G g = grpEvalG G g := by
  rw [← grpEvalGU_eq]
  funext c r
  unfold grpEvalGL grpEvalGU
  refine congrArg (List.foldl (· + ·) 0) ?_
  apply List.map_congr_left
  rintro ⟨n, off⟩ -
  have hp : ∀ r', pieceFixEvalGL (leafT G) (unifT G) n G (G.pe n) c r' = pieceFixEvalGU (unifT G) n G (G.pe n) c r' := by
    intro r'
    cases c <;> simp only [pieceFixEvalGL, pieceFixEvalGU] <;>
      exact pieceEvalGL_eq _ _ G _ _ r' (leafH_spec G n _)
  simp only [hp]

/-! ## The header-independent tables -/

/-- The input arrays before `PUB`. -/
def arrsHead (C : QCfg) (D : QData) : List InArr :=
  let R := 2 ^ C.rl
  (List.range 17).map (fun l => ⟨.K, C.rl, l, 17, [(true, l * R)], fin D l, none⟩) ++
  [⟨.K, 10, sgB C, 1, [(true, 17 * R)], fin D 17, none⟩] ++
  (List.range 17).map (fun l => ⟨.K, 9, xsB C + l, 17, [(false, xOff C + l * R)], fin D (18 + l), none⟩) ++
  (List.range 4).map (fun l => ⟨.K, 9, ysB C + l, 4, [(false, ksY C l + R)], fin D (35 + l), none⟩) ++
  (List.range 4).map (fun l =>
    ⟨.K, 0, mdB C + l, 4, [(false, ksY C l + (spongeBlocks C.p - 1))], fin D (39 + l), none⟩)

/-- `PUB`, the one header-dependent array. -/
def pubA (C : QCfg) (D : QData) (P : Pub) : InArr := pubArr 10 (pbB C) 1 (false, 0) (fin D 43) (hdrOfPub P)

/-- The input arrays after `PUB` (`QLT`, the `BITS` outputs). -/
def arrsTail (C : QCfg) (D : QData) : List InArr :=
  [pubArr C.aQT (qtB C) 1 (false, 0) (fin D 44) (qltDataF C.p (lay C)),
   ⟨.K, C.bo, obB C, 1, [(false, D.aval)], fin D 45, none⟩]

theorem arrs_split (C : QCfg) (D : QData) (P : Pub) :
    arrs C D P = arrsHead C D ++ [pubA C D P] ++ arrsTail C D := by
  unfold arrs arrsHead pubA arrsTail
  simp only [List.append_assoc, List.cons_append, List.nil_append, qltDataF_eq]

/-- The header-independent parts of the tables. -/
structure Pre where
  /-- The uniform-stride hints (kept so that they are built once with the parts). -/
  unif : Array (List (FCol × Option (List Nat)))
  /-- The groups' coefficient leaves (L2). -/
  leaves : Array (List (FCol × Leaves))
  /-- The groups' tables. -/
  grps : List Tab
  /-- The input arrays' tables before `PUB`. -/
  head : List Tab
  /-- The input arrays' tables after `PUB`. -/
  tail : List Tab
  /-- The aux tables. -/
  aux : List Tab

/-- **The parts** of `QAsm.tabs C G D`. -/
def pre (C : QCfg) (G : PG) (D : QData) : Pre :=
  let U := unifT G
  let LT := leafT G
  { unif := U
    leaves := LT
    grps := (List.range D.groups.length).map fun i =>
    shapeTab (D.groups.getD i default).σ (D.groups.getD i default).τ (grpFix G.C.Q (D.groups.getD i default))
      (grpEvalGL LT U G (D.groups.getD i default)) (plOf D i)
    head := (arrsHead C D).map InArr.tab
    tail := (arrsTail C D).map InArr.tab
    aux := auxF C D }

/-- The tables from the parts and the header. -/
def tabsPre (R : Pre) (C : QCfg) (D : QData) (P : Pub) : List Tab :=
  R.grps ++ (R.head ++ [InArr.tab (pubA C D P)] ++ R.tail) ++ R.aux

/-- **The parts make the tables.** -/
theorem tabsPre_eq (C : QCfg) (G : PG) (D : QData) (P : Pub) :
    tabsPre (pre C G D) C D P = QAsm.tabs C G D P := by
  unfold tabsPre pre QAsm.tabs lvmTabsC
  rw [arrs_split, auxF_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, grpEvalGL_eq]

/-! ## `V_S` at `P20` -/

/-- The parts at `P20` (a top-level constant: evaluated once per process). -/
def pre20 : Pre := pre cfg20 M3.G20 data20

/-- **The `P20` tables**, header-independent parts shared. -/
def tabs20F (P : Pub) : List Tab := tabsPre pre20 cfg20 data20 P

theorem tabs20F_eq : tabs20F = M3.tabsP20 := funext fun P => tabsPre_eq cfg20 M3.G20 data20 P

/-! ## The bus decomposition with linear stacking -/

/-- `stackBlocks` with the offsets consed and reversed (no repeated append). -/
def stackBlocksF (bs : List NBlock) : List (NBlock × Nat) :=
  let sorted := bs.mergeSort fun a b => decide (b.κ ≤ a.κ)
  (sorted.foldl (fun (acc : List (NBlock × Nat) × Nat) b => ((b, acc.2) :: acc.1, acc.2 + 2 ^ b.κ))
    ([], 0)).1.reverse

theorem stack_fold : ∀ (l : List NBlock) (acc : List (NBlock × Nat)) (off : Nat),
    (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => (a.1 ++ [(b, a.2)], a.2 + 2 ^ b.κ)) (acc, off)).1 =
      acc ++ (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ)) ([], off)).1.reverse
  | [], acc, off => by simp
  | b :: l, acc, off => by
    simp only [List.foldl_cons]
    rw [stack_fold l (acc ++ [(b, off)]) (off + 2 ^ b.κ), stack_fold' l [(b, off)] (off + 2 ^ b.κ)]
    simp
where
  stack_fold' : ∀ (l : List NBlock) (acc : List (NBlock × Nat)) (off : Nat),
      (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ)) (acc, off)).1 =
        (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ)) ([], off)).1 ++ acc
    | [], acc, off => by simp
    | b :: l, acc, off => by
      simp only [List.foldl_cons]
      rw [stack_fold' l ((b, off) :: acc), stack_fold' l [(b, off)]]
      simp

theorem stackBlocksF_eq (bs : List NBlock) : stackBlocksF bs = stackBlocks bs := by
  unfold stackBlocksF stackBlocks
  rw [stack_fold _ [] 0]
  simp

/-- `busFinalR` with `stackBlocksF`. -/
def busFinalRF (tabs : List Tab) (i : BusIn) : BusOut :=
  let eqα := eqKernel i.alphas
  let sides := (sideBlocks tabs eqα i.beta).map fun bs =>
    (stackBlocksF bs).map fun (b, off) => (b, blockWeight i.point b.κ off)
  let bucket (s : List (NBlock × FE)) : Array (List (List Nat × FE)) :=
    s.foldl (fun acc (b, w) => acc.modify b.tab fun ts =>
      b.form.terms.map (fun t => (t.1, w * t.2)) ++ ts) (Array.replicate tabs.length [])
  let bs := sides.map bucket
  let forms := (List.range tabs.length).map fun j => bs.map fun a => (⟨a.getD j []⟩ : Form)
  let totals := (List.range 3).map fun k =>
    i.values.getD k 0 + 1 + sumE ((sides.getD k []).map (·.2))
  ⟨i.values.length == 3 && i.leafdec == [0], [], forms, totals⟩

theorem busFinalRF_eq : busFinalRF = busFinalR := by
  funext tabs i
  unfold busFinalRF busFinalR
  simp only [stackBlocksF_eq]

/-! ## L4 (V-LEV): the KS link's continuation sum in closed form

`contShift` sums `eq(ρ, i)·eq(ρ', i − 1)` over ≈ 14 k continuation rows of two `2^15` tables;
`Q1.contShift_eq` and `Q1.preCF_eq` give it as three `O(|ρ|)` prefix sums (`preCF`). -/

/-- `contShift` by `preCF` when the shapes allow (always at `P20`), else by the tables. -/
def contShiftF (p : Params) (rho rho' : List FE) : FE :=
  if rho.length = p.ksLog ∧ rho'.length = p.ksLog ∧ 1 ≤ spongeBlocks p ∧ spongeBlocks p ≤ 2 ^ p.ksLog ∧
      2 ^ p.recRowsLog + 431 ≤ 2 ^ p.ksLog then
    (Q1.preCF rho rho' (spongeBlocks p - 1)).1 + (Q1.preCF rho rho' (2 ^ p.recRowsLog + 399 + 31)).1 +
      (Q1.preCF rho rho' (2 ^ p.recRowsLog + 399)).1
  else contShift p rho rho'

theorem contShiftF_eq (p : Params) : contShiftF p = contShift p := by
  funext rho rho'
  unfold contShiftF
  split
  · rename_i h
    obtain ⟨h1, h2, hB, hB2, hK⟩ := h
    have hl : rho.length = rho'.length := by rw [h1, h2]
    rw [Q1.contShift_eq p rho rho' h1 h2 hB hB2 hK, Q1.preCF_eq _ _ _ hl, Q1.preCF_eq _ _ _ hl,
      Q1.preCF_eq _ _ _ hl]
  · rfl

/-- `ksLink0` with `contShiftF`. -/
def ksLinkF (p : Params) (i : KsLinkIn) : Bool × List (Com × BlockClaim) :=
  let L := layout0 p
  let rho := i.chal.take p.ksLog
  let om := eqKernel (i.chal.drop p.ksLog)
  let rho' := i.shift.1
  let lo := rho'.take p.recRowsLog
  let xr := rho'.getD p.recRowsLog 0
  let y := i.vals.getD 0 0
  let inv := i.vals.getD 1 0
  let mv := i.vals.getD 2 0
  let xv := i.vals.getD 3 0
  let ok := i.shift.2 == contShiftF p rho rho' * y + eqEval rho rho' * (inv + (1 + xr) * mv + xr * xv)
  let lanes25 := List.range 25
  let lanes17 := List.range 17
  let yC := sumClaim p.nuMain (lanes25.map fun l =>
    let (b, z) := ksYPart p L l rho'
    (om.getD l 0, b, z)) y
  let inC := sumClaim p.nuMain (lanes25.map fun l =>
    (om.getD l 0, (⟨p.ksLog + slotLog, L.ks⟩ : Placement), rho' ++ selectorPoint l slotLog)) inv
  let mC := sumClaim p.nuRec (lanes17.map fun l =>
    (om.getD l 0, (⟨p.recRowsLog, l * 2 ^ p.recRowsLog⟩ : Placement), lo)) mv
  let xC := sumClaim p.nuMain (lanes17.map fun l =>
    (om.getD l 0, (⟨p.recRowsLog, L.x + l * 2 ^ p.recRowsLog⟩ : Placement), lo)) xv
  (ok, [(.main, yC), (.main, inC), (.crec, mC), (.main, xC)])

theorem ksLinkF_eq (p : Params) : ksLinkF p = ksLink0 p := by
  funext i
  unfold ksLinkF ksLink0
  rw [contShiftF_eq]

/-! ## L3 (V-LEV): the bus forms by their values

The table sumcheck reads each table's three bus forms only through `Form.value` at the table's
evaluations. `tableTermsG`/`tableSumcheckG` take those values as functions of the column values;
`decideProgB` is `decideProg` with a bus step `BusIn → BusOutB` that returns these functions instead
of the forms (`decideProgB_eq`). The fast bus step keeps each table's (block, weight) pairs and
values a side as `Σ w_b · value(F_b)` (linearity of `Form.value`), with no weighted term lists. -/

open DM in
/-- `tableTerms` with each table's forms given by their values. -/
def tableTermsG (constraintPowers formPowers point : List FE) :
    List (TableSpec × ((Nat → FE) → List FE) × FE) → Nat → FE → DM (FE × List (List FE × List FE))
  | [], _, final => pure (final, [])
  | (table, fs, weight) :: rest, cursor, final => do
    let evaluations ← readEs table.width
    let ea := evaluations.toArray
    let tpoint := point.take table.logHeight
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints tpoint evaluations)
    let final := final + weight * (summand + dot formPowers (fs (ea.getD · 0)))
    let (final, rows) ← tableTermsG constraintPowers formPowers point rest
      (cursor + table.nConstraints) final
    pure (final, (tpoint, evaluations) :: rows)

theorem tableTermsG_eq (cp fp pt : List FE) : ∀ (rows : List (TableSpec × List Form × FE)) (cursor : Nat) (final : FE),
    tableTermsG cp fp pt (rows.map fun x => (x.1, fun col => x.2.1.map (·.value col), x.2.2)) cursor final =
      tableTerms cp fp pt rows cursor final
  | [], _, _ => rfl
  | (t, f, w) :: rest, cursor, final => by
    simp only [List.map_cons, tableTermsG, tableTerms, tableTermsG_eq cp fp pt rest, toArray_getD]

open DM in
/-- `tableSumcheck` with the forms given by their values. -/
def tableSumcheckG (rounds : Nat) (tables : List TableSpec) (fv : List ((Nat → FE) → List FE))
    (constraintPowers formPowers equalityPoint : List FE) (target : FE) : DM (List (List FE × List FE)) := do
  let (challenges, claim) ← sumcheck target 4 (List.replicate rounds none)
  let point := challenges.reverse
  let weights := tableWeights (tables.map (·.logHeight)) equalityPoint point
  let rows := List.zip tables (List.zip fv weights)
  let (final, evaluations) ← tableTermsG constraintPowers formPowers point rows 0 0
  require (final == claim)
  pure evaluations

theorem zip_zip_map {α β γ δ : Type} (g : β → δ) : ∀ (a : List α) (b : List β) (c : List γ),
    List.zip a (List.zip (b.map g) c) = (List.zip a (List.zip b c)).map fun x => (x.1, g x.2.1, x.2.2)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | x :: a, y :: b, z :: c => by simp only [List.map_cons, List.zip_cons_cons, zip_zip_map g a b c]

theorem tableSumcheckG_eq (rounds : Nat) (tables : List TableSpec) (busForms : List (List Form))
    (cp fp eqPt : List FE) (target : FE) :
    tableSumcheckG rounds tables (busForms.map fun f col => f.map (·.value col)) cp fp eqPt target =
      tableSumcheck rounds tables busForms cp fp eqPt target := by
  unfold tableSumcheckG tableSumcheck
  simp only [zip_zip_map, tableTermsG_eq]

/-- The bus step's output with each table's forms as values. -/
structure BusOutB where
  /-- The decomposition's check. -/
  ok : Bool
  /-- Column claims on the commitments. -/
  claims : List (Com × BlockClaim)
  /-- Each table's three side values, as functions of its columns' values. -/
  fv : List ((Nat → FE) → List FE)
  /-- The three sides' totals. -/
  totals : List FE

/-- `bb` computes `m.busFinal`, its forms by value. -/
def BusAgree (m : M3) (bb : BusIn → BusOutB) : Prop :=
  ∀ i, (bb i).ok = (m.busFinal i).ok ∧ (bb i).claims = (m.busFinal i).claims ∧
    (bb i).totals = (m.busFinal i).totals ∧ (bb i).fv = (m.busFinal i).forms.map fun f col => f.map (·.value col)

open DM in
/-- **`decideProg` with the bus step `bb`.** -/
def decideProgB (p : Params) (m : M3) (bb : BusIn → BusOutB) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  -- 1] commit
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)
  -- 2] bus
  let alphas ← samples busBits
  let beta ← sampleE
  let (countRoot, point, values) ← verifyGkrGrandProducts p.busDepth
  require (countRoot != 0)
  let leafdec ← readEs p.leafdecReads
  let bus := bb ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
  require bus.ok
  -- 3] tables
  let xi ← sampleE
  let tables := m.tables pub
  let nC := (tables.map (·.nConstraints)).sum
  let xiPowers := powers xi (nC + 3)
  let formPowers := xiPowers.drop nC
  let evals ← tableSumcheckG p.tableRounds tables bus.fv (xiPowers.take nC) formPowers
    point (dot formPowers bus.totals)
  let accOut ← accFold p m pub evals
  -- 4] the tape (lvm2 S2, T1–T2)
  let tp ← dTape p.logN
  -- 5] the wire (T3–T4), after A1's range of `n`
  dRange p pub
  let wo ← dWire p pub tp.claim
  -- 6] KS
  let rk ← samples p.ksLog
  let vks ← readEs lanes
  let kko ← verifyKeccak p.ksLog rk vks
  let kring ← ringSwitch kko.slicePoint kko.slices
  let ksClaims := keccakClaims m.ksBlock kko kring
  -- 7] KS link
  let kchal ← samples (p.ksLog + laneBits)
  let kshift ← sumcheck (m.ksShiftTarget kchal) 3 (List.replicate p.ksLog none)
  let kvals ← readEs 4
  let (okK, kLinkClaims) := m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩
  require okK
  -- 8] the openings
  let claims : List (Com × BlockClaim) :=
    bus.claims ++ m.tableClaims pub evals ++ (tapeClaims p tp wo pub ++ ksClaims).map (.main, ·) ++
      m.ksOutputClaims rk vks ++ kLinkClaims
  let on (com : Com) := (claims.filter (·.1 == com)).map (·.2.onStack)
  verifyStackedOpening p.recLevels p.nuRec (on .crec) false p.grind false
  verifyStackedOpening p.mainLevels p.nuMain (on .main) false p.grind p.mainOod
  pure accOut

theorem decideProgB_eq (p : Params) (m : M3) (bb : BusIn → BusOutB) (h : BusAgree m bb) (vk c : Vector UInt8 32) :
    decideProgB p m bb vk c = decideProg p m vk c := by
  have hok : ∀ i, (bb i).ok = (m.busFinal i).ok := fun i => (h i).1
  have hcl : ∀ i, (bb i).claims = (m.busFinal i).claims := fun i => (h i).2.1
  have hto : ∀ i, (bb i).totals = (m.busFinal i).totals := fun i => (h i).2.2.1
  have hfv : ∀ i, (bb i).fv = (m.busFinal i).forms.map fun f col => f.map (·.value col) := fun i => (h i).2.2.2
  unfold decideProgB decideProg
  simp only [hok, hcl, hto, hfv, tableSumcheckG_eq]

/-- `decideF` on `decideProgB`. -/
def decideFB (p : Params) (m : M3) (bb : BusIn → BusOutB) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (a, s) := (decideProgB p m bb vk c).runOn sig
  (s.ok && s.ent == sig.size && s.msg == 0) && AccOk p m (pubOf vk c sig) a

/-- `VS` on `decideFB`. -/
def VSB (p : Params) (m : M3) (bb : BusIn → BusOutB) (vk c : Digest) (π : Proof) : OProg Bool :=
  if parseOk p vk c π then drive p π (decideFB p m bb vk c) else .ret false

theorem VSB_eq (p : Params) (m : M3) (bb : BusIn → BusOutB) (h : BusAgree m bb) : VSB p m bb = VS p m := by
  funext vk c π
  unfold VSB VS decideFB decideF
  simp only [decideProgB_eq p m bb h]

/-! ### The fast bus step: (block, weight) pairs per table -/

theorem foldl_add_sum : ∀ (l : List FE) (a : FE), l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | x :: l, a => by simp only [List.foldl_cons, List.sum_cons, foldl_add_sum l]; ring

theorem sumE_eq_sum (l : List FE) : sumE l = l.sum := by
  unfold sumE; rw [foldl_add_sum, zero_add]

theorem foldl_mul_init (col : Nat → FE) : ∀ (ms : List Nat) (w a : FE),
    ms.foldl (fun acc i => acc * col i) (w * a) = w * ms.foldl (fun acc i => acc * col i) a
  | [], _, _ => rfl
  | m :: ms, w, a => by simp only [List.foldl_cons]; rw [mul_assoc, foldl_mul_init col ms]

theorem value_append (l₁ l₂ : List (List Nat × FE)) (col : Nat → FE) :
    (⟨l₁ ++ l₂⟩ : Form).value col = (⟨l₁⟩ : Form).value col + (⟨l₂⟩ : Form).value col := by
  simp only [Form.value, List.map_append, sumE_eq_sum, List.sum_append]

theorem value_scale (w : FE) (l : List (List Nat × FE)) (col : Nat → FE) :
    (⟨l.map fun t => (t.1, w * t.2)⟩ : Form).value col = w * (⟨l⟩ : Form).value col := by
  simp only [Form.value, List.map_map, sumE_eq_sum, Function.comp_def, foldl_mul_init, List.sum_map_mul_left]

/-- A side's value at table `j` from its (block, weight) pairs. -/
def sideVal (a : Array (List (NBlock × FE))) (j : Nat) (col : Nat → FE) : FE :=
  sumE ((a.getD j []).map fun x => x.2 * x.1.form.value col)

/-- The bus forms' bucketing as written in `busFinalR`. -/
def bucketT (n : Nat) (s : List (NBlock × FE)) : Array (List (List Nat × FE)) :=
  s.foldl (fun acc (b, w) => acc.modify b.tab fun ts => b.form.terms.map (fun t => (t.1, w * t.2)) ++ ts)
    (Array.replicate n [])

/-- **The pairs' bucketing**: no weighted term lists. -/
def bucketB (n : Nat) (s : List (NBlock × FE)) : Array (List (NBlock × FE)) :=
  s.foldl (fun acc (b, w) => acc.modify b.tab fun ts => (b, w) :: ts) (Array.replicate n [])

theorem getD_modify {α : Type} (xs : Array α) (i j : Nat) (f : α → α) (d : α) :
    (xs.modify i f).getD j d = if i = j ∧ j < xs.size then f (xs.getD j d) else xs.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getD_eq_getD_getElem?]
  by_cases h : i = j
  · by_cases hj : j < xs.size
    · simp [h, hj, Array.getElem?_eq_getElem hj]
    · simp [h, hj, Array.getElem?_eq_none (show xs.size ≤ j by omega)]
  · simp [h]

theorem bucket_fold (col : Nat → FE) : ∀ (s : List (NBlock × FE)) (acc : Array (List (List Nat × FE)))
    (accB : Array (List (NBlock × FE))), acc.size = accB.size →
    (∀ j, (⟨acc.getD j []⟩ : Form).value col = sideVal accB j col) →
    ∀ j, (⟨(s.foldl (fun acc (x : NBlock × FE) => acc.modify x.1.tab fun ts =>
        x.1.form.terms.map (fun t => (t.1, x.2 * t.2)) ++ ts) acc).getD j []⟩ : Form).value col =
      sideVal (s.foldl (fun acc (x : NBlock × FE) => acc.modify x.1.tab fun ts => x :: ts) accB) j col
  | [], _, _, _, h => h
  | x :: s, acc, accB, hs, h => by
    simp only [List.foldl_cons]
    apply bucket_fold col s
    · simp only [Array.size_modify, hs]
    · intro j
      rw [getD_modify, sideVal, getD_modify, ← hs]
      split
      · rw [value_append, value_scale, h j, List.map_cons, sumE_eq_sum, List.sum_cons, ← sumE_eq_sum]
        rfl
      · exact h j

theorem bucketT_val (n : Nat) (s : List (NBlock × FE)) (col : Nat → FE) (j : Nat) :
    (⟨(bucketT n s).getD j []⟩ : Form).value col = sideVal (bucketB n s) j col := by
  unfold bucketT bucketB
  refine bucket_fold col s _ _ (by simp) (fun j => ?_) j
  have h1 : (Array.replicate n ([] : List (List Nat × FE))).getD j [] = [] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl
  have h2 : (Array.replicate n ([] : List (NBlock × FE))).getD j [] = [] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl
  rw [sideVal, h1, h2]; rfl

/-- **`busFinalRF` with the forms by value** (`busFinalB_agree`). -/
def busFinalB (tabs : List Tab) (i : BusIn) : BusOutB :=
  let eqα := eqKernel i.alphas
  let sides := (sideBlocks tabs eqα i.beta).map fun bs =>
    (stackBlocksF bs).map fun (b, off) => (b, blockWeight i.point b.κ off)
  let bs := sides.map (bucketB tabs.length)
  let totals := (List.range 3).map fun k =>
    i.values.getD k 0 + 1 + sumE ((sides.getD k []).map (·.2))
  ⟨i.values.length == 3 && i.leafdec == [0], [],
    (List.range tabs.length).map (fun j col => bs.map fun a => sideVal a j col), totals⟩

theorem busFinalB_agree (tabs : List Tab) (i : BusIn) :
    (busFinalB tabs i).ok = (busFinalRF tabs i).ok ∧ (busFinalB tabs i).claims = (busFinalRF tabs i).claims ∧
      (busFinalB tabs i).totals = (busFinalRF tabs i).totals ∧
      (busFinalB tabs i).fv = (busFinalRF tabs i).forms.map fun f col => f.map (·.value col) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [busFinalB, busFinalRF, List.map_map]
  apply List.map_congr_left
  intro j _
  funext col
  simp only [Function.comp_def, List.map_map]
  apply List.map_congr_left
  intro a _
  exact (bucketT_val tabs.length _ col j).symm

/-! ### L3b: block values from the static key polynomials (no forms built)

A block's form is `leafForm eqα β key cnt` (or `Form.col c`); its value at the columns is
`leafVal`: the key polynomials' `K` coefficients times column products (`E × K`), with no term
list and no `E × E` coefficient products (`leafVal_eq`). `busFinalV` stacks and buckets blocks
carrying these value functions (`NBlockV`); `busFinalV_agree`: it is `busFinalB`. -/

/-- A `CPoly` at the columns, its `K` coefficients by `smulBase`. -/
def cval (P : CPoly) (col : Nat → FE) : FE :=
  sumE (P.map fun m => match m.2 with
    | [] => FE.ofK m.1
    | [i] => FE.smulBase m.1 (col i)
    | [i, j] => FE.smulBase m.1 (col i * col j)
    | ms => ms.foldl (fun acc i => acc * col i) (FE.ofK m.1))

theorem cval_term (col : Nat → FE) (m : FK × List Nat) :
    (match m.2 with
      | [] => FE.ofK m.1
      | [i] => FE.smulBase m.1 (col i)
      | [i, j] => FE.smulBase m.1 (col i * col j)
      | ms => ms.foldl (fun acc i => acc * col i) (FE.ofK m.1)) =
      m.2.foldl (fun acc i => acc * col i) (FE.ofK m.1) := by
  obtain ⟨c, ms⟩ := m
  rcases ms with _ | ⟨i, _ | ⟨j, _ | ⟨k, ms⟩⟩⟩ <;>
    simp [FE.smulBase_eq_mul, mul_assoc]

theorem cpolyForm_value (w : FE) (P : CPoly) (col : Nat → FE) :
    (cpolyForm w P).value col = w * cval P col := by
  simp only [cpolyForm, Form.value, cval, cval_term, List.map_map, Function.comp_def, foldl_mul_init,
    sumE_eq_sum, List.sum_map_mul_left]

theorem formSum_value (fs : List Form) (col : Nat → FE) :
    (formSum fs).value col = sumE (fs.map (·.value col)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [formSum, List.flatMap_cons] at ih ⊢
    rw [value_append, ih, List.map_cons, sumE_eq_sum, sumE_eq_sum, List.sum_cons]

/-- **A leaf form's value**, from the key polynomials. -/
def leafVal (eqα : List FE) (β : FE) (k : Key) (cnt : CPoly) (col : Nat → FE) : FE :=
  (β + eqα.getD 0 0 * FE.ofK k.sep) + eqα.getD 1 0 * cval k.addr col + eqα.getD 2 0 * cval cnt col +
    sumE (k.val.zipIdx.map fun x => eqα.getD (3 + x.2) 0 * cval x.1 col)

theorem leafVal_eq (eqα : List FE) (β : FE) (k : Key) (cnt : CPoly) :
    (leafForm eqα β k cnt).value = leafVal eqα β k cnt := by
  funext col
  unfold leafForm leafVal
  rw [formSum_value]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, cpolyForm_value,
    sumE_eq_sum, List.sum_append, List.sum_cons, List.sum_nil]
  have hc : (Form.const (β + eqα.getD 0 0 * FE.ofK k.sep)).value col = β + eqα.getD 0 0 * FE.ofK k.sep := by
    simp [Form.const, Form.value, sumE]
  rw [hc]
  ring

/-- A bus block with its form's value function. -/
structure NBlockV where
  /-- The table. -/
  tab : Nat
  /-- The log-height. -/
  κ : Nat
  /-- The form's value at the columns. -/
  val : (Nat → FE) → FE

/-- A block's value view. -/
def _root_.Lvm.M3.NBlock.toV (b : NBlock) : NBlockV := ⟨b.tab, b.κ, b.form.value⟩

/-- `sideBlocks` with value functions. -/
def sideBlocksV (tabs : List Tab) (eqα : List FE) (β : FE) : List (List NBlockV) :=
  let ts := tabs.zipIdx
  [ts.flatMap fun x =>
      x.1.reads.map (fun r => ⟨x.2, x.1.τ, leafVal eqα β r.1 [(FK.x, [r.2])]⟩) ++
        x.1.seeds.map (fun s => ⟨x.2, x.1.τ, leafVal eqα β s.1 (CPoly.const 1)⟩),
   ts.flatMap fun x =>
      x.1.reads.map (fun r => ⟨x.2, x.1.τ, leafVal eqα β r.1 (CPoly.var r.2)⟩) ++
        x.1.seeds.map (fun s => ⟨x.2, x.1.τ, leafVal eqα β s.1 (CPoly.var s.2)⟩),
   ts.flatMap fun x => x.1.counts.map fun c => ⟨x.2, x.1.τ, (Form.col c.val).value⟩]

theorem sideBlocksV_eq (tabs : List Tab) (eqα : List FE) (β : FE) :
    sideBlocksV tabs eqα β = (sideBlocks tabs eqα β).map (List.map NBlock.toV) := by
  unfold sideBlocksV sideBlocks
  simp only [List.map_cons, List.map_nil, List.map_flatMap, List.map_append, List.map_map, Function.comp_def,
    NBlock.toV, leafVal_eq]

/-- `stackBlocksF` on value blocks. -/
def stackBlocksV (bs : List NBlockV) : List (NBlockV × Nat) :=
  let sorted := bs.mergeSort fun a b => decide (b.κ ≤ a.κ)
  (sorted.foldl (fun (acc : List (NBlockV × Nat) × Nat) b => ((b, acc.2) :: acc.1, acc.2 + 2 ^ b.κ))
    ([], 0)).1.reverse

theorem stackV_fold : ∀ (l : List NBlock) (acc : List (NBlock × Nat)) (off : Nat),
    ((l.map NBlock.toV).foldl (fun (a : List (NBlockV × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ))
      (acc.map fun x => (x.1.toV, x.2), off)) =
    ((l.foldl (fun (a : List (NBlock × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ)) (acc, off)).1.map
      (fun x => (x.1.toV, x.2)),
     (l.foldl (fun (a : List (NBlock × Nat) × Nat) b => ((b, a.2) :: a.1, a.2 + 2 ^ b.κ)) (acc, off)).2)
  | [], _, _ => rfl
  | b :: l, acc, off => by
    simp only [List.map_cons, List.foldl_cons]
    exact stackV_fold l ((b, off) :: acc) (off + 2 ^ b.κ)

theorem stackBlocksV_map (bs : List NBlock) :
    stackBlocksV (bs.map NBlock.toV) = (stackBlocksF bs).map fun x => (x.1.toV, x.2) := by
  unfold stackBlocksV stackBlocksF
  rw [← List.map_mergeSort (r := fun a b => decide (b.κ ≤ a.κ)) (fun _ _ _ _ => rfl)]
  have := stackV_fold (bs.mergeSort fun a b => decide (b.κ ≤ a.κ)) [] 0
  simp only [List.map_nil] at this
  dsimp only
  rw [this, List.map_reverse]

/-- The pairs' bucketing for value blocks. -/
def bucketV (n : Nat) (s : List (NBlockV × FE)) : Array (List (NBlockV × FE)) :=
  s.foldl (fun acc x => acc.modify x.1.tab fun ts => x :: ts) (Array.replicate n [])

theorem bucketV_map (n : Nat) (s : List (NBlock × FE)) :
    bucketV n (s.map fun x => (x.1.toV, x.2)) = (bucketB n s).map (List.map fun x => (x.1.toV, x.2)) := by
  unfold bucketV bucketB
  have key : ∀ (s : List (NBlock × FE)) (acc : Array (List (NBlock × FE))),
      (s.map fun x => (x.1.toV, x.2)).foldl (fun acc x => acc.modify x.1.tab fun ts => x :: ts)
        (acc.map (List.map fun x => (x.1.toV, x.2))) =
      (s.foldl (fun acc (x : NBlock × FE) => acc.modify x.1.tab fun ts => x :: ts) acc).map
        (List.map fun x => (x.1.toV, x.2)) := by
    intro s
    induction s with
    | nil => intro acc; rfl
    | cons x s ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      rw [← ih]
      congr 1
      apply Array.ext
      · simp
      · intro i h1 h2
        by_cases h : x.1.tab = i <;> simp [Array.getElem_modify, h, NBlock.toV]
  have h0 : Array.replicate n ([] : List (NBlockV × FE)) =
      (Array.replicate n ([] : List (NBlock × FE))).map (List.map fun x => (x.1.toV, x.2)) := by
    simp
  rw [h0, key]

/-- A side's value at table `j` from value blocks. -/
def sideValV (a : Array (List (NBlockV × FE))) (j : Nat) (col : Nat → FE) : FE :=
  sumE ((a.getD j []).map fun x => x.2 * x.1.val col)

theorem sideValV_map (a : Array (List (NBlock × FE))) (j : Nat) (col : Nat → FE) :
    sideValV (a.map (List.map fun x => (x.1.toV, x.2))) j col = sideVal a j col := by
  unfold sideValV sideVal
  have : (a.map (List.map fun x => (x.1.toV, x.2))).getD j [] = (a.getD j []).map fun x => (x.1.toV, x.2) := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases a[j]? <;> rfl
  rw [this, List.map_map]
  rfl

/-- **The bus step on value blocks** (no forms built). -/
def busFinalV (tabs : List Tab) (i : BusIn) : BusOutB :=
  let eqα := eqKernel i.alphas
  let sides := (sideBlocksV tabs eqα i.beta).map fun bs =>
    (stackBlocksV bs).map fun x => (x.1, blockWeight i.point x.1.κ x.2)
  let bs := sides.map (bucketV tabs.length)
  let totals := (List.range 3).map fun k =>
    i.values.getD k 0 + 1 + sumE ((sides.getD k []).map (·.2))
  ⟨i.values.length == 3 && i.leafdec == [0], [],
    (List.range tabs.length).map (fun j col => bs.map fun a => sideValV a j col), totals⟩

theorem busFinalV_agree (tabs : List Tab) (i : BusIn) :
    (busFinalV tabs i).ok = (busFinalB tabs i).ok ∧ (busFinalV tabs i).claims = (busFinalB tabs i).claims ∧
      (busFinalV tabs i).totals = (busFinalB tabs i).totals ∧ (busFinalV tabs i).fv = (busFinalB tabs i).fv := by
  have hs : ((sideBlocksV tabs (eqKernel i.alphas) i.beta).map fun bs =>
      (stackBlocksV bs).map fun x => (x.1, blockWeight i.point x.1.κ x.2)) =
      ((sideBlocks tabs (eqKernel i.alphas) i.beta).map fun bs =>
        (stackBlocksF bs).map fun x => (x.1, blockWeight i.point x.1.κ x.2)).map
        (List.map fun x => (x.1.toV, x.2)) := by
    rw [sideBlocksV_eq, List.map_map, List.map_map]
    apply List.map_congr_left
    intro bs _
    simp only [Function.comp_def, stackBlocksV_map, List.map_map]
    rfl
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [busFinalV, busFinalB]
    rw [hs]
    congr 1; funext k
    congr 2
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (List.map (fun bs => List.map (fun x => (x.1, blockWeight i.point x.1.κ x.2)) (stackBlocksF bs))
      (sideBlocks tabs (eqKernel i.alphas) i.beta))[k]? <;> simp [List.map_map, Function.comp_def]
  · simp only [busFinalV, busFinalB]
    rw [hs]
    apply List.map_congr_left
    intro j _
    funext col
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro x _
    rw [show (stackBlocksF x).map (fun y => (y.1.toV, blockWeight i.point y.1.κ y.2)) =
        ((stackBlocksF x).map fun y => (y.1, blockWeight i.point y.1.κ y.2)).map (fun y => (y.1.toV, y.2)) by
      rw [List.map_map]; rfl, bucketV_map, sideValV_map]

/-- `nativeTable` reading the evaluations from an array (L3c). -/
def nativeTableF (t : Tab) : TableSpec :=
  ⟨t.τ, t.w, t.cons.length, fun _ evals => let ea := evals.toArray; t.cons.map (CPoly.evalE (fun i => ea.getD i 0))⟩

theorem nativeTableF_eq : nativeTableF = nativeTable := by
  funext t
  simp only [nativeTableF, nativeTable, toArray_getD]

/-- **The `P20` M3 instance**: `M3.real P20 tabs20F` with `busFinalRF`. -/
def m20F : M3 :=
  { M3.ofParts P20 (fun i => busFinalRF (sumcheckTabs (tabs20F i.pub)) i)
      (fun pub => (sumcheckTabs (tabs20F pub)).map nativeTableF)
      (fun pub => tableClaimsR (sumcheckTabs (tabs20F pub)))
      (fun pub => fixValsR (sumcheckTabs (tabs20F pub)) P20.pubTab)
      (fun pub => fixSentR (sumcheckTabs (tabs20F pub)) P20.pubTab)
      (fun pub => pubCheckR P20.pubTab pub) with
    ksLink := ksLinkF P20 }

theorem m20F_eq : m20F = M3.real P20 M3.tabsP20 := by
  unfold m20F M3.real
  rw [busFinalRF_eq, tabs20F_eq, ksLinkF_eq, nativeTableF_eq]
  rfl

/-- The `P20` bus step with the forms by value. -/
def busB20 (i : BusIn) : BusOutB := busFinalV (sumcheckTabs (tabs20F i.pub)) i

theorem busB20_agree : BusAgree m20F busB20 := fun i => by
  obtain ⟨h1, h2, h3, h4⟩ := busFinalV_agree (sumcheckTabs (tabs20F i.pub)) i
  obtain ⟨g1, g2, g3, g4⟩ := busFinalB_agree (sumcheckTabs (tabs20F i.pub)) i
  exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩

/-- **`V_S` at `P20`**, compiled with the shared tables. -/
def VS20F (vk c : Digest) (π : Proof) : OProg Bool := VSB P20 m20F busB20 vk c π

/-- **It is `VS20`.** -/
theorem VS20F_eq : VS20F = VS20 := by
  funext vk c π
  unfold VS20F VS20 VSL
  rw [VSB_eq P20 m20F busB20 busB20_agree, m20F_eq]

end Lvm.VF

namespace Lvm.T

open RecursionFast

/-- **The shipped submission**: `submission` with `V_S = VS20F`. -/
def submissionF : Submission := subWith Lvm.VF.VS20F EX20 Lvm.X.extX

/-- **It is the certified one.** -/
theorem submissionF_eq : submissionF = submission := by
  unfold submissionF submission
  rw [Lvm.VF.VS20F_eq]

end Lvm.T
