import LvmLoopMle

/-!
# Self-evaluation: the program evaluates its own glue columns

BLUEPRINT §4.5 (D10). The child's verifier needs the extension of every fixed column of every piece
at its table-sumcheck point. Structured columns have closed forms (`pieceEval_eq`); the glue's
columns (pieces of blocks with no loop dimension, `Program.glue`) are evaluated *by the program*:

* `eqLevel`: one level of an `eq` table, a loop block of two `muladd` rows; `eqLevel_spec`: from
  `eq(pt, ·)` on `2^k` cells to `eq(ρ :: pt, ·)` on `2^(k+1)` cells. `n` levels give `eqW r` for any
  point (`r` reversed into the levels).
* `fixPro`: a prologue writing one zero per glue column (the accumulators' initial values).
* `fixBlock dc dx eb s₀`: dims `[dc, dx]`, one `fixmul` row
  `acc[c, x] = F_c(x)·eq[x] + acc[c, x - 1]` with `F_c(x)` the glue matrix (`fixMat [c, x]`), `eq[x]`
  the cell `eb + x`, `acc[c, x]` the cell `s₀ + c + 2^dc·x`.
* **`fixmul_mle`**: in every memory satisfying the rows, with `eq[x] = eqW r x` and zero initial
  values, the last accumulator of column `c` is `mle r (fixMat [c, ·])`: the extension of glue column
  `c` (zero-extended to `2^dx` rows) at `r`.
* `mle_fixF`: the `fixmul` piece's own multiplier column has extension
  `mle r_c (c ↦ mle r_x (fixMat [c, ·]))`, a combination of the accumulators: no new unstructured
  column appears, so a program that contains its glue's `fixmul` block is a fixed point (the toy in
  `LvmLoopToy` closes it).

All statements are about any memory with `Holds` (the committed one by `loopir_sound`'s proof, or the
interpreter's by `interp_holds`).
-/

namespace Lvm.Loop

open FE Program

/-! ## The sum form of the extension, and the order of two extensions -/

theorem sum_range_two_mul (g : Nat → FE) : ∀ N : Nat,
    ∑ x ∈ Finset.range (2 * N), g x = ∑ x ∈ Finset.range N, (g (2 * x) + g (2 * x + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul g N, Finset.sum_range_succ]
    ring

theorem eqW_even (r : FE) (rs : List FE) (x : Nat) : eqW (r :: rs) (2 * x) = (1 - r) * eqW rs x := by
  simp only [eqW]; rw [if_neg (by omega), show 2 * x / 2 = x by omega]

theorem eqW_odd (r : FE) (rs : List FE) (x : Nat) : eqW (r :: rs) (2 * x + 1) = r * eqW rs x := by
  simp only [eqW]; rw [if_pos (by omega), show (2 * x + 1) / 2 = x by omega]

/-- **The usual form of the extension**: `mle r f = Σ_{x < 2^|r|} eq(r, x)·f x`. -/
theorem mle_eq_sum : ∀ (r : List FE) (f : Nat → FE),
    mle r f = ∑ x ∈ Finset.range (2 ^ r.length), eqW r x * f x
  | [], f => by simp [mle, eqW]
  | r :: rs, f => by
    rw [mle, mle_eq_sum rs, mle_eq_sum rs, List.length_cons, pow_succ, mul_comm _ 2,
      sum_range_two_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [eqW_even, eqW_odd]; ring

theorem mle_comm : ∀ (r₁ r₂ : List FE) (f : Nat → Nat → FE),
    mle r₁ (fun x => mle r₂ (fun y => f x y)) = mle r₂ (fun y => mle r₁ (fun x => f x y))
  | [], _, _ => rfl
  | r :: r₁, r₂, f => by
    simp only [mle]
    rw [mle_comm r₁ r₂ (fun x y => f (2 * x) y), mle_comm r₁ r₂ (fun x y => f (2 * x + 1) y),
      ← mle_lin]

/-! ## A program without computed-address reads finds every cell -/

theorem foldl_inb_true (Q : Program) : ∀ (L : List Inst) (s : St), s.inb = true →
    (∀ i ∈ L, ∀ lo m, i.row.op ≠ .readd lo m) → (L.foldl Q.step s).inb = true
  | [], _, h, _ => h
  | i :: L, s, h, hL => by
    apply foldl_inb_true Q L
    · rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ <;>
        simp only [step, hop, St.put_inb] <;> first | exact h | exact absurd hop (hL i (by simp) lo m)
    · exact fun j hj => hL j (by simp [hj])

/-- No row of any block is a `readd`. -/
def Program.noReadd (Q : Program) : Bool :=
  Q.blocks.all fun B => B.tpl.all fun r => match r.op with
    | .readd .. => false
    | _ => true

theorem inb_of_noReadd (Q : Program) (h : Q.noReadd = true) (inK : Array FK) (inE : Array FE) :
    (Q.interp inK inE).inb = true := by
  refine foldl_inb_true Q _ _ rfl fun i hi lo m hop => ?_
  obtain ⟨b, hb, jf, -, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
  simp only [Program.noReadd, List.all_eq_true] at h
  have hB := h _ (List.getElem_mem hb)
  rw [← Q.blk_eq hb] at hB
  have hr := hB ((Q.blk b).tpl.getD t default) (by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
  have hop' : ((Q.blk b).tpl.getD t default).op = .readd lo m := hop
  rw [hop'] at hr
  exact absurd hr (by simp)

/-! ## `eq` tables -/

/-- One level of an `eq` table: the cells `prev + x` (`x < 2^k`) times `1 - ρ` and `ρ` (the cells
`omr` and `rho`), plus the zero cell, written at `2x` and `2x + 1`. -/
def eqLevel (k prev rho omr zero : Nat) : Block :=
  ⟨[k], [⟨.muladd, .E, [⟨.E, prev, [1]⟩, ⟨.E, omr, []⟩, ⟨.E, zero, []⟩]⟩,
    ⟨.muladd, .E, [⟨.E, prev, [1]⟩, ⟨.E, rho, []⟩, ⟨.E, zero, []⟩]⟩]⟩

theorem unflat_one {k x : Nat} (hx : x < 2 ^ k) : unflat [k] x = [x] := by
  simp [unflat, Nat.mod_eq_of_lt hx]

theorem unflat_two {dc dx c y : Nat} (hc : c < 2 ^ dc) (hy : y < 2 ^ dx) :
    unflat [dc, dx] (c + 2 ^ dc * y) = [c, y] := by
  have hm : (c + 2 ^ dc * y) % 2 ^ dc = c := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have hdv : (c + 2 ^ dc * y) / 2 ^ dc = y := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hc, Nat.zero_add]
  simp [unflat, hm, hdv, Nat.mod_eq_of_lt hy]

theorem eqLevel_step {Q : Program} {b k prev rho omr zero : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = eqLevel k prev rho omr zero) {M : Mem} (hM : Q.Holds M) {x : Nat}
    (hx : x < 2 ^ k) (t : Nat) (ht : t < 2) :
    M.e (Q.start .E b + (2 * x + t)) =
      M.e (prev + x) * M.e (if t = 0 then omr else rho) + M.e zero := by
  have hsz : x < (Q.blk b).size := by simp [Block.size, Block.lsize, hB, eqLevel]; exact hx
  have hi := (Q.mem_insts (Q.inst b x t)).mpr ⟨b, hb, _, hsz, t, by simp [hB, eqLevel]; omega, rfl⟩
  have hd := hM _ hi
  have hj : (Q.inst b x t).j = [x] := by
    show unflat (Q.blk b).dims x = [x]; rw [hB]; exact unflat_one hx
  have hce : (Q.inst b x t).ce = Q.start .E b + (2 * x + t) := by
    show Q.start .E b + (Q.blk b).tw .E * x + (Q.blk b).rank .E t = _
    rw [hB]
    interval_cases t <;> simp [Block.tw, Block.rank, eqLevel, Row.w, Row.writes] <;> ring
  interval_cases t
  · have hrow : (Q.inst b x 0).row =
        ⟨.muladd, .E, [⟨.E, prev, [1]⟩, ⟨.E, omr, []⟩, ⟨.E, zero, []⟩]⟩ := by
      simp [Program.inst, hB, eqLevel]
    simp only [RowDef, hrow, Mem.res, Mem.arg, Inst.arg, Inst.clock, hj, hce, Mem.rd,
      List.getD_cons_zero, List.getD_cons_succ, Addr.at, dot, Nat.one_mul, Nat.add_zero] at hd
    simpa using hd
  · have hrow : (Q.inst b x 1).row =
        ⟨.muladd, .E, [⟨.E, prev, [1]⟩, ⟨.E, rho, []⟩, ⟨.E, zero, []⟩]⟩ := by
      simp [Program.inst, hB, eqLevel]
    simp only [RowDef, hrow, Mem.res, Mem.arg, Inst.arg, Inst.clock, hj, hce, Mem.rd,
      List.getD_cons_zero, List.getD_cons_succ, Addr.at, dot, Nat.one_mul, Nat.add_zero] at hd
    simpa using hd

theorem eqLevel_spec {Q : Program} {b k prev rho omr zero : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = eqLevel k prev rho omr zero) {M : Mem} (hM : Q.Holds M) {pt : List FE}
    (hprev : ∀ x < 2 ^ k, M.e (prev + x) = eqW pt x) (hz : M.e zero = 0)
    (homr : M.e omr = 1 - M.e rho) :
    ∀ y < 2 ^ (k + 1), M.e (Q.start .E b + y) = eqW (M.e rho :: pt) y := by
  intro y hy
  have hx : y / 2 < 2 ^ k := by rw [pow_succ] at hy; omega
  rcases Nat.mod_two_eq_zero_or_one y with h0 | h1
  · have hy2 : y = 2 * (y / 2) + 0 := by omega
    rw [hy2, eqLevel_step hb hB hM hx 0 (by omega), Nat.add_zero, eqW_even, hprev _ hx, if_pos rfl,
      homr, hz]
    ring
  · have hy2 : y = 2 * (y / 2) + 1 := by omega
    rw [hy2, eqLevel_step hb hB hM hx 1 (by omega), eqW_odd, hprev _ hx, if_neg (by omega), hz]
    ring

/-! ## The `fixmul` block -/

/-- The prologue: one zero per glue column (`z + 0·z + 0`, `z` the zero cell). -/
def fixPro (dc zero : Nat) : Block :=
  ⟨[dc], [⟨.lin 0 0, .E, [⟨.E, zero, []⟩, ⟨.E, zero, []⟩]⟩]⟩

/-- The self-evaluation block: `acc[c, x] = F_c(x)·eq[x] + acc[c, x - 1]`, `acc[c, x]` the cell
`s₀ + c + 2^dc·x` (`s₀` the block's first `E` cell), `eq[x]` the cell `eb + x`. -/
def fixBlock (dc dx eb s₀ : Nat) : Block :=
  ⟨[dc, dx], [⟨.fixmul, .E, [⟨.E, eb, [0, 1]⟩, ⟨.E, s₀ - 2 ^ dc, [1, 2 ^ dc]⟩]⟩]⟩

theorem fixPro_spec {Q : Program} {b dc zero : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = fixPro dc zero) {M : Mem} (hM : Q.Holds M) (hz : M.e zero = 0) :
    ∀ c < 2 ^ dc, M.e (Q.start .E b + c) = 0 := by
  intro c hc
  have hsz : c < (Q.blk b).size := by simp [Block.size, Block.lsize, hB, fixPro]; exact hc
  have hi := (Q.mem_insts (Q.inst b c 0)).mpr ⟨b, hb, _, hsz, 0, by simp [hB, fixPro], rfl⟩
  have hd := hM _ hi
  have hrow : (Q.inst b c 0).row = ⟨.lin 0 0, .E, [⟨.E, zero, []⟩, ⟨.E, zero, []⟩]⟩ := by
    simp [Program.inst, hB, fixPro]
  have hce : (Q.inst b c 0).ce = Q.start .E b + c := by
    show Q.start .E b + (Q.blk b).tw .E * c + (Q.blk b).rank .E 0 = _
    rw [hB]; simp [Block.tw, Block.rank, fixPro, Row.w, Row.writes]
  simp only [RowDef, hrow, Mem.res, Mem.arg, Inst.arg, Inst.clock, hce, Mem.rd,
    List.getD_cons_zero, List.getD_cons_succ, Addr.at, dot, Nat.add_zero] at hd
  rw [hd, hz, show FE.ofK 0 = 0 from rfl]
  ring

theorem fixBlock_step {Q : Program} {b dc dx eb s₀ : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = fixBlock dc dx eb s₀) (hs : s₀ = Q.start .E b) {M : Mem} (hM : Q.Holds M)
    {c y : Nat} (hc : c < 2 ^ dc) (hy : y < 2 ^ dx) :
    M.e (s₀ + (c + 2 ^ dc * y)) =
      FE.ofK (Q.fixMat [c, y]) * M.e (eb + y) + M.e (s₀ - 2 ^ dc + (c + 2 ^ dc * y)) := by
  have hlt : c + 2 ^ dc * y < 2 ^ dc * 2 ^ dx := by
    have e1 : 2 ^ dc * (y + 1) = 2 ^ dc * y + 2 ^ dc := by ring
    have e2 : 2 ^ dc * (y + 1) ≤ 2 ^ dc * 2 ^ dx := Nat.mul_le_mul_left _ (by omega)
    omega
  have hsz : c + 2 ^ dc * y < (Q.blk b).size := by
    rw [show (Q.blk b).size = 2 ^ dc * 2 ^ dx by simp [Block.size, Block.lsize, hB, fixBlock, pow_add]]
    exact hlt
  have hi := (Q.mem_insts (Q.inst b (c + 2 ^ dc * y) 0)).mpr
    ⟨b, hb, _, hsz, 0, by simp [hB, fixBlock], rfl⟩
  have hd := hM _ hi
  have hj : (Q.inst b (c + 2 ^ dc * y) 0).j = [c, y] := by
    show unflat (Q.blk b).dims _ = _; rw [hB]; exact unflat_two hc hy
  have hrow : (Q.inst b (c + 2 ^ dc * y) 0).row =
      ⟨.fixmul, .E, [⟨.E, eb, [0, 1]⟩, ⟨.E, s₀ - 2 ^ dc, [1, 2 ^ dc]⟩]⟩ := by
    simp [Program.inst, hB, fixBlock]
  have hce : (Q.inst b (c + 2 ^ dc * y) 0).ce = s₀ + (c + 2 ^ dc * y) := by
    show Q.start .E b + (Q.blk b).tw .E * _ + (Q.blk b).rank .E 0 = _
    rw [hB, ← hs]; simp [Block.tw, Block.rank, fixBlock, Row.w, Row.writes]
  simp only [RowDef, hrow, Mem.res, Mem.arg, Inst.arg, Inst.clock, hj, hce, Mem.rd,
    List.getD_cons_zero, List.getD_cons_succ, Addr.at, dot, Nat.zero_mul, Nat.one_mul, Nat.add_zero,
    Nat.zero_add] at hd
  exact hd

/-- **The accumulator recursion**, summed. -/
theorem fixmul_acc {Q : Program} {b dc dx eb s₀ : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = fixBlock dc dx eb s₀) (hs : s₀ = Q.start .E b) (h2 : 2 ^ dc ≤ s₀)
    {M : Mem} (hM : Q.Holds M) {c : Nat} (hc : c < 2 ^ dc) :
    ∀ x < 2 ^ dx, M.e (s₀ + (c + 2 ^ dc * x)) = M.e (s₀ - 2 ^ dc + c) +
      ∑ x' ∈ Finset.range (x + 1), FE.ofK (Q.fixMat [c, x']) * M.e (eb + x') := by
  intro x hx
  induction x with
  | zero =>
    rw [fixBlock_step hb hB hs hM hc hx, Finset.sum_range_one]
    simp only [Nat.mul_zero, Nat.add_zero]
    ring
  | succ x ih =>
    rw [fixBlock_step hb hB hs hM hc hx, show s₀ - 2 ^ dc + (c + 2 ^ dc * (x + 1)) =
      s₀ + (c + 2 ^ dc * x) by rw [Nat.mul_succ]; omega, ih (by omega),
      Finset.sum_range_succ _ (x + 1)]
    ring

/-- **The accumulator is the extension of the glue column.** With the `eq` cells holding `eqW r`
(`|r| = dx`) and zero initial values, the last accumulator of column `c` is `mle r F_c`. -/
theorem fixmul_mle {Q : Program} {b dc dx eb s₀ : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = fixBlock dc dx eb s₀) (hs : s₀ = Q.start .E b) (h2 : 2 ^ dc ≤ s₀)
    {M : Mem} (hM : Q.Holds M) {r : List FE} (hr : r.length = dx)
    (heq : ∀ x < 2 ^ dx, M.e (eb + x) = eqW r x) (hinit : ∀ c < 2 ^ dc, M.e (s₀ - 2 ^ dc + c) = 0)
    {c : Nat} (hc : c < 2 ^ dc) :
    M.e (s₀ + (c + 2 ^ dc * (2 ^ dx - 1))) = mle r (fun x => FE.ofK (Q.fixMat [c, x])) := by
  rw [fixmul_acc hb hB hs h2 hM hc _ (by have := Nat.two_pow_pos dx; omega), hinit c hc, zero_add,
    mle_eq_sum, hr, show 2 ^ dx - 1 + 1 = 2 ^ dx by have := Nat.two_pow_pos dx; omega]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [heq x (Finset.mem_range.mp hx), mul_comm]

/-- **The `fixmul` piece's multiplier column** has extension `Σ_c eq(r_c, c)·mle r_x F_c`: a
combination of the accumulators, so the self-evaluation adds no unstructured column. -/
theorem mle_fixF {Q : Program} {dc dx eb s₀ : Nat} {p : Piece}
    (hB : Q.blk p.blk = fixBlock dc dx eb s₀) (hp : p.a = 0) (rc rx : List FE) (hrc : rc.length = dc)
    (hrx : rx.length = dx) :
    mle (rc ++ rx ++ []) (fun x => FE.ofK (Q.fval p .F x)) =
      mle rc (fun c => mle rx (fun x => FE.ofK (Q.fixMat [c, x]))) := by
  rw [List.append_nil, mle_split, hrc, mle_comm]
  apply mle_congr
  intro c hcc
  apply mle_congr
  intro y hy
  rw [hrx] at hy; rw [hrc] at hcc
  have hsz : (Q.blk p.blk).size = 2 ^ dc * 2 ^ dx := by
    simp [Block.size, Block.lsize, hB, fixBlock, pow_add]
  have hlt : c + 2 ^ dc * y < 2 ^ dc * 2 ^ dx := by
    calc c + 2 ^ dc * y < 2 ^ dc * (y + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ 2 ^ dc * 2 ^ dx := Nat.mul_le_mul_left _ hy
  show FE.ofK (Q.fixMat (unflat (Q.blk p.blk).dims ((c + 2 ^ dc * y) % (Q.blk p.blk).size))) = _
  rw [hsz, Nat.mod_eq_of_lt hlt, hB]
  simp only [fixBlock]
  rw [unflat_two hcc hy]

end Lvm.Loop
