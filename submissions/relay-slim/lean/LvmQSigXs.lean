import LvmQSigDefs

/-!
# `Q_sig`: the `KS` message lanes are input cells (decision A19)

New for lvm (WP-12). The `KS` rows read their message lanes from the input array `I.xs` (row `r`'s
lane `l` at `I.xs + 17 r + l`); `Q_sig` computes the message lanes consecutively from `o.x0`
(`xcell_eq`) and asserts, gated by the node flag, that they equal the input array (`gXeq`,
`qsig_xeq`). **`qsig_sound_in`** is `qsig_sound` with the `KS` hypothesis on the input array
(`SigKSin`, which does not mention `Q_sig`'s output).
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.KSponge Lvm.Wots

/-! ## The layout of the message lanes -/

theorem out_bind {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := rfl

theorem getPtr_apply (p : Ptr) : getPtr p = (p, []) := rfl

/-! The same equations as proof-producing `simp` rules (proofs that are not `rfl`): as `rfl` lemmas
`simp` applies them definitionally and the kernel re-derives each step by unfolding `>>=`, where it
compares the blocks' builders first (1 s each in `qsig_msg`, `qsig_gXeq`). -/

theorem out_bind_eq {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := (out_bind m f p).trans rfl

theorem getPtr_apply_eq (p : Ptr) : getPtr p = (p, []) := (getPtr_apply p).trans rfl

theorem pure_apply_eq {α : Type} (x : α) (p : Ptr) : (pure x : BM α) p = (x, []) := (pure_apply x p).trans rfl

/-- Every template row writes one `K` cell. -/
def AllK (tpl : List LRow) : Prop := ∀ r ∈ tpl, r.op ≠ .assert0 ∧ r.ty = .K

theorem ltw_allK {tpl : List LRow} (hw : AllK tpl) : ltw .K tpl = tpl.length := by
  have hall : ∀ r ∈ tpl, LRow.w .K r = 1 := fun r hr => by
    obtain ⟨h1, h2⟩ := hw r hr
    obtain ⟨op, ty, args⟩ := r
    simp only at h1 h2; subst h2
    cases op <;> simp_all [LRow.w, Row.w, Row.writes]
  unfold ltw
  rw [List.map_congr_left (g := fun _ => 1) hall]
  simp

theorem loop_cellK {dims : List Nat} {tpl : List LRow} (q : Ptr) (hw : AllK tpl) {t : Nat}
    (jf : Nat) (ht : t < tpl.length) :
    ((loop dims tpl q).1.cell t jf).n = q.k + t + tpl.length * jf :=
  cell_lin1 _ t jf ht hw

theorem loop_advK {dims : List Nat} {tpl : List LRow} (q : Ptr) (hw : AllK tpl) :
    (q.adv (loop dims tpl q).2).k = q.k + tpl.length * 2 ^ dims.sum := by
  have hs : (mkLoop q dims tpl).size = 2 ^ dims.sum := rfl
  show q.k + segsW .K [.blk (mkLoop q dims tpl)] = _
  simp only [segsW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Seg.w, mkLoop_tw,
    ltw_allK hw, hs, Nat.add_zero]

/-- A sequence of loops of the same size. -/
theorem seqAll_loops {d : List Nat} {tp : Nat → List LRow} {w : Nat} (hw : ∀ u, AllK (tp u))
    (hl : ∀ u, (tp u).length * 2 ^ d.sum = w) :
    ∀ (ls : List Nat) (q : Ptr),
      (q.adv (seqAll (ls.map fun u => loop d (tp u)) q).2).k = q.k + w * ls.length ∧
      ∀ i < ls.length, ∃ q' : Ptr, q'.k = q.k + w * i ∧
        (seqAll (ls.map fun u => loop d (tp u)) q).1.getD i dLoop = (loop d (tp (ls.getD i 0)) q').1
  | [], q => ⟨by simp [seqAll, pure_apply], fun i hi => absurd hi (by simp)⟩
  | u :: ls, q => by
    obtain ⟨ih1, ih2⟩ := seqAll_loops hw hl ls (q.adv (loop d (tp u) q).2)
    rw [List.map_cons, seqAll_cons_apply]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [List.append_nil, Ptr.adv_append, ih1, loop_advK q (hw u), hl u, List.length_cons,
        Nat.mul_succ]
      omega
    · cases i with
      | zero => exact ⟨q, by simp, rfl⟩
      | succ i =>
        obtain ⟨q', e1, e2⟩ := ih2 i (by simpa using hi)
        refine ⟨q', ?_, by simpa using e2⟩
        rw [e1, loop_advK q (hw u), hl u, Nat.mul_succ]
        omega

theorem forN_loops {n : Nat} {d : List Nat} {tp : Nat → List LRow} {w : Nat} (hw : ∀ u, AllK (tp u))
    (hl : ∀ u, (tp u).length * 2 ^ d.sum = w) (q : Ptr) :
    (q.adv (forN n (fun u => loop d (tp u)) q).2).k = q.k + w * n ∧
      ∀ i < n, ∃ q' : Ptr, q'.k = q.k + w * i ∧
        (forN n (fun u => loop d (tp u)) q).1.getD i dLoop = (loop d (tp i) q').1 := by
  obtain ⟨h1, h2⟩ := seqAll_loops hw hl (List.range n) q
  refine ⟨by rw [List.length_range] at h1; exact h1, fun i hi => ?_⟩
  obtain ⟨q', e1, e2⟩ := h2 i (by simpa using hi)
  refine ⟨q', e1, ?_⟩
  rw [show (List.range n).getD i 0 = i by simp [hi]] at e2
  exact e2

theorem stepsTpl_allK (I : SigIn) (Zn : Nat) (T : Opd) (c1 : Nat → UInt64) (xb st : Nat) :
    AllK (stepsTpl I Zn T c1 xb st) := by
  simp only [AllK, stepsTpl, stepLanes, zeroLanes, padLane, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_map]
  simp

theorem stepsTpl_len (I : SigIn) (Zn : Nat) (T : Opd) (c1 : Nat → UInt64) (xb st : Nat) :
    (stepsTpl I Zn T c1 xb st).length = 51 := by
  simp [stepsTpl, stepLanes, zeroLanes]

theorem leafA_allK (I : SigIn) : AllK (leafA I) := by
  simp only [AllK, leafA, List.forall_mem_cons]
  simp

theorem leafB_allK (I : SigIn) : AllK (leafB I) := by
  simp only [AllK, leafB, List.forall_mem_cons]
  simp

theorem leafC_allK (I : SigIn) (Zn : Nat) : AllK (leafC I Zn) := by
  simp only [AllK, leafC, zeroLanes, padLane, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map]
  simp

theorem leafC_len (I : SigIn) (Zn : Nat) : (leafC I Zn).length = 30 := by simp [leafC, zeroLanes]

theorem twoLanes_allK (Zn : Nat) (tag : UInt64) (aB bB st : Nat) :
    AllK (twoLanes Zn tag aB bB st) := by
  simp only [AllK, twoLanes, zeroLanes, padLane, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map]
  simp

theorem twoLanes_len (Zn : Nat) (tag : UInt64) (aB bB st : Nat) :
    (twoLanes Zn tag aB bB st).length = 17 := by simp [twoLanes, zeroLanes]

theorem leafStmt_allK (I : SigIn) (Zn : Nat) : AllK (leafStmtLanes I Zn) := by
  simp only [AllK, leafStmtLanes, zeroLanes, padLane, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map]
  simp

theorem leafStmt_len (I : SigIn) (Zn : Nat) : (leafStmtLanes I Zn).length = 17 := by
  simp [leafStmtLanes, zeroLanes]

/-- **The message lanes of `gMsg` at `q` are consecutive from `q.k`.** -/
theorem gMsg_xcell {I : SigIn} {Zn Tb : Nat} {q : Ptr} {o : SigOut} (hm : o.msg = (gMsg I Zn Tb q).1)
    {r l : Nat} (hr : r < 449) (hl : l < 17) : xcell o r l = q.k + 17 * r + l := by
  simp only [gMsg, out_bind, pure_apply] at hm
  obtain ⟨hF, hG⟩ := forN_loops (n := 5) (d := []) (w := 51)
    (tp := fun u => stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0)
    (fun u => stepsTpl_allK _ _ _ _ _ _) (fun u => by simp [stepsTpl_len])
    (q.adv (loop [7] (stepsTpl I Zn (oS Tb 1) (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) q).2)
  unfold xcell leafLane
  rw [hm]
  dsimp only
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · rw [loop_cellK _ (stepsTpl_allK _ _ _ _ _ _) _ (by rw [stepsTpl_len]; omega), stepsTpl_len]
    omega
  · obtain ⟨q', e1, e2⟩ := hG ((r - 384) / 3) (by omega)
    rw [e2, loop_cellK _ (stepsTpl_allK _ _ _ _ _ _) _ (by rw [stepsTpl_len]; omega), e1,
      loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len]
    simp only [List.sum_cons, List.sum_nil]
    omega
  · rw [loop_cellK _ (leafA_allK I) _ (by simp [leafA]; omega), hF,
      loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len]
    simp only [List.sum_cons, List.sum_nil]
    omega
  · rw [loop_cellK _ (leafB_allK I) _ (by simp [leafB]), loop_advK _ (leafA_allK I), hF,
      loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    omega
  · rw [loop_cellK _ (leafC_allK I Zn) _ (by rw [leafC_len]; omega), loop_advK _ (leafB_allK I),
      loop_advK _ (leafA_allK I), hF, loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    omega
  · rw [loop_cellK _ (twoLanes_allK _ _ _ _ _) _ (by rw [twoLanes_len]; omega), twoLanes_len,
      loop_advK _ (leafC_allK I Zn), loop_advK _ (leafB_allK I),
      loop_advK _ (leafA_allK I), hF, loop_advK _ (stepsTpl_allK _ _ _ _ _ _), stepsTpl_len, leafC_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    omega
  · rw [loop_cellK _ (leafStmt_allK _ _) _ (by rw [leafStmt_len]; omega), leafStmt_len,
      loop_advK _ (twoLanes_allK _ _ _ _ _), twoLanes_len, loop_advK _ (leafC_allK I Zn),
      loop_advK _ (leafB_allK I), loop_advK _ (leafA_allK I), hF, loop_advK _ (stepsTpl_allK _ _ _ _ _ _),
      stepsTpl_len, leafC_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    omega
  · rw [loop_cellK _ (twoLanes_allK _ _ _ _ _) _ (by rw [twoLanes_len]; omega), twoLanes_len,
      loop_advK _ (leafStmt_allK _ _), leafStmt_len,
      loop_advK _ (twoLanes_allK _ _ _ _ _), twoLanes_len, loop_advK _ (leafC_allK I Zn),
      loop_advK _ (leafB_allK I), loop_advK _ (leafA_allK I), hF, loop_advK _ (stepsTpl_allK _ _ _ _ _ _),
      stepsTpl_len, leafC_len]
    simp only [List.sum_cons, List.sum_nil, leafA, leafB, List.length_cons, List.length_nil]
    omega

theorem qsig_msg (I : SigIn) (p : Ptr) : ∃ q : Ptr, (qsig I p).1.x0 = q.k ∧
    (qsig I p).1.msg = (gMsg I (qsig I p).1.pre.1.n (Tbase (qsig I p).1.pre) q).1 := by
  unfold qsig
  simp only [out_bind_eq, getPtr_apply_eq, pure_apply_eq, Ptr.adv_nil]
  exact ⟨_, rfl, rfl⟩

/-- **KS row `r`'s lane `l` is the cell `x0 + 17 r + l`.** -/
theorem xcell_eq {I : SigIn} {p : Ptr} {r l : Nat} (hr : r < 449) (hl : l < 17) :
    xcell (qsig I p).1 r l = (qsig I p).1.x0 + 17 * r + l := by
  obtain ⟨q, e1, e2⟩ := qsig_msg I p
  rw [e1]
  exact gMsg_xcell e2 hr hl

/-! ## The equality with the input array -/

/-- One `xeqTpl` loop: lane `off + j` of the message equals lane `off + j` of the input array when
the gate is on. -/
theorem xeq_loop {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {x0 d off : Nat}
    (h : SegsHold c M p (loop [d] (xeqTpl I x0 off) p).2)
    (hA : SegsAssert M p (loop [d] (xeqTpl I x0 off) p).2) (hg : M.k I.flag = 1) :
    ∀ j < 2 ^ d, M.k (x0 + off + j) = M.k (I.xs + off + j) := by
  intro j hj
  have hjf : j < 2 ^ ([d] : List Nat).sum := by simpa using hj
  have hK : OpdK (loop [d] (xeqTpl I x0 off) p).1 (.cur 0) := rfl
  have r := loopK_lin h hjf (t := 0) (by simp [xeqTpl]) rfl rfl rfl
  have a := loopK_as0 hA hjf (t := 1) (by simp [xeqTpl]) rfl hK rfl
  rw [ov_cur M _ hjf 0 rfl, r, ov_oA, ov_oS M _ rfl hj, ov_oS M _ rfl hj, hg] at a
  simp only [one_mul, add_zero] at a
  have := congrArg (· + M.k (I.xs + off + j)) a
  simpa [add_assoc, FK.add_self] using this

/-- **`gXeq`**: the 7,633 message lanes equal the input array when the gate is on. -/
theorem gXeq_spec {c : Ctx} {M : Mem} {q : Ptr} {I : SigIn} {x0 : Nat} (h : Ok c M (gXeq I x0) q)
    (hg : M.k I.flag = 1) : ∀ j < 7633, M.k (x0 + j) = M.k (I.xs + j) := by
  obtain ⟨h, hA⟩ := h
  simp only [gXeq, hold_bind, assert_bind] at h hA
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, -⟩ := hA
  have e0 := xeq_loop h0 a0 hg
  have e1 := xeq_loop h1 a1 hg
  have e2 := xeq_loop h2 a2 hg
  have e3 := xeq_loop h3 a3 hg
  have e4 := xeq_loop h4 a4 hg
  have e5 := xeq_loop h5 a5 hg
  have e6 := xeq_loop h6 a6 hg
  have e7 := xeq_loop h7 a7 hg
  intro j hj
  have key : ∀ off d, (∀ i < 2 ^ d, M.k (x0 + off + i) = M.k (I.xs + off + i)) →
      off ≤ j → j < off + 2 ^ d → M.k (x0 + j) = M.k (I.xs + j) := fun off d e h1 h2 => by
    have := e (j - off) (by omega)
    rwa [show x0 + off + (j - off) = x0 + j by omega,
      show I.xs + off + (j - off) = I.xs + j by omega] at this
  by_cases k0 : j < 4096
  · exact key 0 12 e0 (by omega) (by norm_num; omega)
  by_cases k1 : j < 6144
  · exact key 4096 11 e1 (by omega) (by norm_num; omega)
  by_cases k2 : j < 7168
  · exact key 6144 10 e2 (by omega) (by norm_num; omega)
  by_cases k3 : j < 7424
  · exact key 7168 8 e3 (by omega) (by norm_num; omega)
  by_cases k4 : j < 7552
  · exact key 7424 7 e4 (by omega) (by norm_num; omega)
  by_cases k5 : j < 7616
  · exact key 7552 6 e5 (by omega) (by norm_num; omega)
  by_cases k6 : j < 7632
  · exact key 7616 4 e6 (by omega) (by norm_num; omega)
  · exact key 7632 0 e7 (by omega) (by norm_num; omega)

set_option maxRecDepth 100000 in
theorem qsig_gXeq {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p) :
    ∃ q, Ok c M (gXeq I (qsig I p).1.x0) q := by
  unfold qsig at h ⊢
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨-, h, -⟩ := ok_bind' h
  obtain ⟨o, -, -⟩ := ok_bind' h
  simp only [getPtr_apply_eq, Ptr.adv_nil] at o
  simp only [out_bind_eq, getPtr_apply_eq, pure_apply_eq, Ptr.adv_nil]
  exact ⟨_, o⟩

/-- **The message lanes are the `KS` input lanes** (A19): with the node flag `1`, cell
`x0 + j` equals cell `xs + j` for every `j < 7633`. -/
theorem qsig_xeq {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) : ∀ j < 7633, M.k ((qsig I p).1.x0 + j) = M.k (I.xs + j) := by
  obtain ⟨q, hq⟩ := qsig_gXeq h
  exact gXeq_spec hq hg

/-! ## `qsig_sound` on the input array -/

/-- **The `KS` rows of the signature schedule, on the input array** (`SigKS` with row `r`'s lanes
the cells `I.xs + 17 r + l`). -/
structure SigKSin (I : SigIn) (v : Nat → FK) : Prop where
  step : ∀ r < 399, OneHash v (fun l => I.xs + 17 * r + l) (I.ys + 4 * r)
  leaf : ∃ sIn sOut : Nat → State, sIn 0 = zeroSt ∧
    (∀ u < 32, BlockPerm (xorMsg (sIn u) (laneByte (lanesW v (fun l => I.xs + 17 * (399 + u) + l))))
      (sOut u)) ∧
    (∀ u, u + 1 < 32 → sIn (u + 1) = sOut u) ∧ digAt v I.yc = stDigest (sOut 31)
  path : ∀ t < 16, OneHash v (fun l => I.xs + 17 * (431 + t) + l) (I.yc + 4 * (t + 1))
  ls : OneHash v (fun l => I.xs + 17 * 447 + l) I.yls
  ns : OneHash v (fun l => I.xs + 17 * 448 + l) I.yns

/-- A block's absorption reads only lanes `0 … 16`. -/
theorem xorMsg_lanes {a : State} {v : Nat → FK} {f g : Nat → Nat} (h : ∀ l < 17, v (f l) = v (g l)) :
    xorMsg a (laneByte (lanesW v f)) = xorMsg a (laneByte (lanesW v g)) := by
  have e : rateArr (laneByte (lanesW v f)) = rateArr (laneByte (lanesW v g)) := by
    unfold rateArr
    congr 1
    funext j
    have hj : j.val < 136 := j.2
    simp only [laneByte, lanesW]
    rw [h _ (by omega)]
  simp only [xorMsg, e]

theorem oneHash_lanes {v : Nat → FK} {f g : Nat → Nat} {y : Nat} (h : ∀ l < 17, v (f l) = v (g l))
    (hg : OneHash v g y) : OneHash v f y := by
  obtain ⟨s, h1, h2⟩ := hg
  exact ⟨s, by rw [xorMsg_lanes h]; exact h1, h2⟩

/-- `SigKSin` gives `SigKS`. -/
theorem sigKS_of_in {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p)
    (hg : M.k I.flag = 1) (hks : SigKSin I M.k) : SigKS I (qsig I p).1 M.k := by
  have hx : ∀ r < 449, ∀ l < 17, M.k (xcell (qsig I p).1 r l) = M.k (I.xs + 17 * r + l) :=
    fun r hr l hl => by
      rw [xcell_eq hr hl, Nat.add_assoc, qsig_xeq h hg _ (by omega), Nat.add_assoc]
  obtain ⟨sIn, sOut, h0, h1, h2, h3⟩ := hks.leaf
  refine ⟨fun r hr => oneHash_lanes (hx r (by omega)) (hks.step r hr),
    ⟨sIn, sOut, h0, fun u hu => ?_, h2, h3⟩,
    fun t ht => oneHash_lanes (hx _ (by omega)) (hks.path t ht),
    oneHash_lanes (hx _ (by omega)) hks.ls, oneHash_lanes (hx _ (by omega)) hks.ns⟩
  rw [xorMsg_lanes (hx _ (by omega))]
  exact h1 u hu

end Lvm.QSig
