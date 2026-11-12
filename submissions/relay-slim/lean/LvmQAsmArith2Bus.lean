-- New for lvm (HAR-BT): phase 2 of Q_arith (`busPh`: the bus challenges, the grand-product GKR, the
-- count root, the leaf-decomposition scalar) replayed from any reader position. Reuses QA2's H2
-- gadgets (`LvmQBusRound.scRunQ3/Q5_eq`, `LvmQBusGkr.gkrFinals_check`, `LvmQBusCount.countNZ_spec`)
-- and QA1's reading lemmas (`LvmQSumcheck`, `LvmQLinkArithRead`). Searched leanerVM
-- `Protocol/Bus.lean`, FR `FRSumcheck`: no circuit-level GKR replay to adapt.
import LvmQAsmHarBase
import LvmQBusRound
import LvmQBusGkr
import LvmQBusCount
import LvmQLinkArithRead
import LvmLoopPieces

/-!
# Phase 2: the bus GKR (`busPh`)

* **`F` from a position** (`busPh_run`): `gkrLayers d` is the step list `gkrSteps d` (`1` first when
  `d` is odd, then steps of `2`; `gkrLayers_eq`); one step from position `Q` (`gkrStep_run`): the
  combiner at `Q + 40`, an equality-mode sumcheck from the entry boundary `Q + 72`, the children,
  the check, the next challenges.
* **The gadget** `busG`: the challenges `α`, `β` (loads), the two root scalars, `countNZ` on the
  count root, one step gadget `stepG` per GKR step (combiner load, `hornerG` claim, QA2's
  equality-mode rounds `scRunQ3`/`scRunQ5` with the point as two affine pieces `PD`: the step's
  new challenges (consecutive loads) and the previous sumcheck's challenge cells, the children's
  loads, `gkrFinals`), then the leaf-decomposition scalar, asserted zero.
* **`busG_replays`**: `Replays … (busPh p) (busG …)`: wherever the gadget's rows hold and assert
  (gate on), `F` keeps `ok`, ends at `busEnd`, and its outputs are the output cells' values, with
  `leafdec = [0]` and three tree values (so `busFinalR`'s flag holds).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-! ## `F`'s GKR as a list of steps -/

/-- The steps of `gkrLayers d`: `1` first when `d` is odd, then steps of `2`. -/
def gkrSteps : Nat → List Nat
  | 0 => []
  | 1 => [1]
  | n + 2 => if n % 2 = 1 then 1 :: gkrSteps (n + 1) else 2 :: gkrSteps n

/-- The steps in order. -/
def runSteps : List Nat → GkrState → DM GkrState
  | [], s => pure s
  | k :: ks, s => do
    let s ← gkrStep k s
    runSteps ks s

theorem gkrLayers_eq : ∀ (d : Nat) (st : GkrState), gkrLayers d st = runSteps (gkrSteps d) st
  | 0, _ => rfl
  | 1, st => by
    show gkrStep 1 st = (gkrStep 1 st >>= fun s => runSteps [] s)
    simp [runSteps]
  | n + 2, st => by
    by_cases h : n % 2 = 1
    · simp only [gkrLayers, gkrSteps, h, ite_true, runSteps]
      exact congrArg _ (funext fun s => gkrLayers_eq (n + 1) s)
    · simp only [gkrLayers, gkrSteps, h, ite_false, runSteps]
      exact congrArg _ (funext fun s => gkrLayers_eq n s)

theorem gkrSteps_mem : ∀ (d : Nat), ∀ k ∈ gkrSteps d, k = 1 ∨ k = 2
  | 0 => by simp [gkrSteps]
  | 1 => by simp [gkrSteps]
  | n + 2 => by
    by_cases h : n % 2 = 1
    · simp only [gkrSteps, h, ite_true, List.mem_cons]
      rintro k (rfl | hk)
      · left; rfl
      · exact gkrSteps_mem (n + 1) k hk
    · simp only [gkrSteps, h, ite_false, List.mem_cons]
      rintro k (rfl | hk)
      · right; rfl
      · exact gkrSteps_mem n k hk

/-! ## One step from a position -/

/-- The bytes of one round of a step of `st` levels (`count − 1 = 2^st` scalars). -/
def rndB (st : Nat) : Nat := 72 + 24 * 2 ^ st

/-- Where a step's children start: after the combiner and `n` rounds. -/
def chB (st n Q : Nat) : Nat := Q + 72 + rndB st * n

/-- The position after a step of `st` levels on a point of `n` coordinates, from position `Q`. -/
def stepEnd (st n Q : Nat) : Nat := chB st n Q + 72 * 2 ^ st + 72 * st

/-- The children `F` reads at `B`. -/
def childrenAt (v : Nat → FE) (st B : Nat) : List (List FE) :=
  (List.range 3).map fun k => Q1.scalarsAt v (B + 40 + 24 * (2 ^ st * k)) (2 ^ st)

theorem require_run (c : Bool) (sig : ByteArray) (s : RS) :
    require c sig s = ((), { s with ok := c && s.ok }) := rfl

/-- **One GKR step from position `Q`** (any `msg`). -/
theorem gkrStep_run (sig : ByteArray) (st : Nat) (hst : 1 ≤ st) (vals pt : List FE) (s : RS) :
    gkrStep st ⟨vals, pt⟩ sig s =
      let γ := feAt sig (pos s + 40)
      let sc := sumcheck (polyEval vals γ) (2 ^ st + 1) (pt.map some) sig ⟨pos s + 72, 0, s.ok⟩
      let B := chB st pt.length (pos s)
      let ch := childrenAt (feAt sig) st B
      let y := Q1.samplesAt (feAt sig) (B + 72 * 2 ^ st) st
      (⟨ch.map (multilinearEval · y), y ++ sc.1.1⟩,
        ⟨stepEnd st pt.length (pos s), 0, (sc.1.2 == polyEval (ch.map prodE) γ) && s.ok⟩) := by
  have hsc := QB.sumcheck_run (2 ^ st + 1) (by have := Nat.one_le_two_pow (n := st); omega) sig
    (pt.map some) (polyEval vals (feAt sig (pos s + 40))) ⟨pos s + 72, 0, s.ok⟩ rfl
  have e1 : s.ent + 40 + s.msg = pos s + 40 := by simp [pos]; omega
  have e2 : s.ent + 72 + s.msg = pos s + 72 := by simp [pos]; omega
  unfold gkrStep
  simp only [Q1.bind_run, Q1.sampleE_run, Q1.pure_run, e1, e2]
  rw [hsc]
  simp only [Q1.readEs_run, require_run, Q1.samples_run sig st _ hst, List.length_map,
    Nat.add_sub_cancel]
  simp only [childrenAt, chB, stepEnd, rndB, QB.entB, List.map_cons, List.map_nil, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, Q1.samplesAt, Nat.mul_zero, Nat.add_zero]
  generalize pos s + 72 + (72 + 24 * 2 ^ st) * pt.length = B
  generalize 2 ^ st = N
  ring_nf

/-! ## Soundness specs of gadgets -/

/-- **A gadget's soundness spec**: wherever its rows hold and its assertions hold, `Φ` of its
output (the frame form of QL's specs, soundness direction only). -/
def SoundG {α : Type} (c : Ctx) (M : Mem) (g : BM α) (Φ : α → Prop) : Prop :=
  ∀ p, SegsHold c M p (g p).2 → SegsAssert M p (g p).2 → Φ (g p).1

section
variable {c : Ctx} {M : Mem}

theorem soundG_bind {α β : Type} {m : BM α} {f : α → BM β} {Φ : α → Prop} {Ψ : β → Prop}
    (hm : SoundG c M m Φ) (hf : ∀ x, Φ x → SoundG c M (f x) Ψ) : SoundG c M (m >>= f) Ψ := by
  intro p hH hA
  rw [hold_bind] at hH
  rw [assert_bind] at hA
  rw [bind_apply]
  exact hf _ (hm p hH.1 hA.1) _ hH.2 hA.2

theorem soundG_pure {α : Type} {x : α} {Φ : α → Prop} (h : Φ x) : SoundG c M (pure x) Φ :=
  fun _ _ _ => h

theorem soundG_mono {α : Type} {g : BM α} {Φ Ψ : α → Prop} (h : SoundG c M g Φ)
    (hΦ : ∀ x, Φ x → Ψ x) : SoundG c M g Ψ := fun p hH hA => hΦ _ (h p hH hA)

theorem soundG_aspec {α : Type} {g : BM α} {P : α → Prop} {A : Prop} (h : QB.ASpec c M g P A) :
    SoundG c M g (fun x => P x ∧ A) := fun p hH hA => ⟨(h p hH).1, (h p hH).2.mp hA⟩

theorem soundG_ok {α : Type} {g : BM α} {Φ : α → Prop} (h : SoundG c M g Φ) {p : Ptr}
    (hok : Lvm.QSig.Ok c M g p) : Φ (g p).1 := h p hok.1 hok.2

end

/-! ## Loads from the stream -/

/-- The `E` scalar in stream lanes `a, a + 1, a + 2` (`F`'s scalar at byte `8a`). -/
def ldE (a : Nat) : BM Cell := loadE (kc a) (kc (a + 1)) (kc (a + 2))

/-- `n` scalars at lanes `a + st·i`, in consecutive `E` cells. -/
def ldEs (a st : Nat) : Nat → BM (List Cell)
  | 0 => pure []
  | n + 1 => do
    let x ← ldE a
    let xs ← ldEs (a + st) st n
    pure (x :: xs)

/-- `ldEs` with the first cell's index. -/
def ldEsP (a st n : Nat) : BM (Nat × List Cell) := do
  let q ← getPtr
  let xs ← ldEs a st n
  pure (q.e, xs)

theorem ldE_apply (a : Nat) (p : Ptr) : (ldE a p).1 = ec p.e := rfl

theorem ldE_adv (a : Nat) (p : Ptr) : p.adv (ldE a p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [ldE, loadE, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem ldE_val (hS : Q1.Streamed M sig T) {a : Nat} (ha : a + 2 < T) {p : Ptr}
    (h : SegsHold c M p (ldE a p).2) : M.e p.e = feAt sig (8 * a) := by
  have := loadE_spec h
  rw [← Q1.load_feAt hS ha]
  exact this

theorem ldE_sound (hS : Q1.Streamed M sig T) {a : Nat} (ha : a + 2 < T) :
    SoundG c M (ldE a) fun x => x.val M = feAt sig (8 * a) := fun p hH _ => by
  show M.e p.e = _
  exact ldE_val hS ha hH

theorem ldEs_sound_at (hS : Q1.Streamed M sig T) (st : Nat) : ∀ (n a : Nat) (p : Ptr),
    (∀ i < n, a + st * i + 2 < T) → SegsHold c M p (ldEs a st n p).2 →
      (ldEs a st n p).1 = (List.range n).map (fun i => ec (p.e + i)) ∧
        (∀ i < n, M.e (p.e + i) = feAt sig (8 * (a + st * i))) ∧
        p.adv (ldEs a st n p).2 = ⟨p.k, p.e + n⟩
  | 0, a, p, _, _ => ⟨rfl, fun i hi => absurd hi (by omega), by simp [ldEs, pure_apply]⟩
  | n + 1, a, p, ha, h => by
    have happ : ldEs a st (n + 1) = (ldE a >>= fun x => ldEs (a + st) st n >>= fun xs => pure (x :: xs)) :=
      rfl
    rw [happ, hold_bind, ldE_adv, hold_bind] at h
    have h0 := ldE_val hS (ha 0 (by omega)) h.1
    obtain ⟨ih1, ih2, ih3⟩ := ldEs_sound_at hS st n (a + st) ⟨p.k, p.e + 1⟩
      (fun i hi => by have := ha (i + 1) (by omega); rw [Nat.mul_succ] at this; omega) h.2.1
    have hseg : (ldEs a st (n + 1) p).2 =
        (ldE a p).2 ++ ((ldEs (a + st) st n ⟨p.k, p.e + 1⟩).2 ++ []) := by
      rw [happ, bind_apply, ldE_adv, bind_apply, pure_apply]
    have hout : (ldEs a st (n + 1) p).1 = ec p.e :: (ldEs (a + st) st n ⟨p.k, p.e + 1⟩).1 := by
      rw [happ, bind_apply, ldE_adv, bind_apply, pure_apply]; rfl
    refine ⟨?_, fun i hi => ?_, ?_⟩
    · rw [hout, ih1, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply]; congr 1; omega
    · rcases i with _ | i
      · simpa using h0
      · have := ih2 i (by omega)
        rw [show p.e + 1 + i = p.e + (i + 1) by omega,
          show a + st + st * i = a + st * (i + 1) by rw [Nat.mul_succ]; omega] at this
        exact this
    · rw [hseg, List.append_nil, Ptr.adv_append, ldE_adv, ih3]
      simp only [Ptr.mk.injEq, true_and]; omega

theorem ldEs_noassert (st : Nat) : ∀ (n a : Nat) (p : Ptr), SegsAssert M p (ldEs a st n p).2
  | 0, _, _ => trivial
  | n + 1, a, p => by
    have happ : ldEs a st (n + 1) = (ldE a >>= fun x => ldEs (a + st) st n >>= fun xs => pure (x :: xs)) :=
      rfl
    rw [happ, assert_bind, assert_bind]
    refine ⟨?_, ldEs_noassert st n _ _, trivial⟩
    simp [ldE, loadE, rowRes, SegsAssert, Program.RowAssert, rowInst]

/-- **Loads**: consecutive `E` cells holding `F`'s scalars at bytes `8(a + st·i)`. -/
theorem ldEsP_sound (hS : Q1.Streamed M sig T) (a st n : Nat) (ha : ∀ i < n, a + st * i + 2 < T) :
    SoundG c M (ldEsP a st n) fun r =>
      r.2 = (List.range n).map (fun i => ec (r.1 + i)) ∧ ∀ i < n, M.e (r.1 + i) = feAt sig (8 * (a + st * i)) :=
  fun p hH _ => by
    simp only [ldEsP, getPtr, bind_apply, pure_apply, Ptr.adv_nil, List.nil_append,
      List.append_nil] at hH ⊢
    obtain ⟨h1, h2, -⟩ := ldEs_sound_at hS st n a p ha hH
    exact ⟨h1, h2⟩

theorem ldEs_sound (hS : Q1.Streamed M sig T) (a st n : Nat) (ha : ∀ i < n, a + st * i + 2 < T) :
    SoundG c M (ldEs a st n) fun xs =>
      vs M xs = (List.range n).map (fun i => feAt sig (8 * (a + st * i))) := fun p hH _ => by
  obtain ⟨h1, h2, -⟩ := ldEs_sound_at hS st n a p ha hH
  rw [h1, vs, List.map_map]
  exact List.map_congr_left fun i hi => by simpa using h2 i (List.mem_range.mp hi)

end

/-! ## The GKR point as cells -/

/-- **A GKR point as cells**: `ny` consecutive cells from `yb` (a step's new challenges), then `nx`
cells at stride `L` from `xb` (the step's sumcheck challenge cells). -/
structure PD where
  /-- The first new challenge's cell. -/
  yb : Nat
  /-- The new challenges. -/
  ny : Nat
  /-- The first sumcheck challenge's cell. -/
  xb : Nat
  /-- The sumcheck challenges' stride. -/
  L : Nat
  /-- The sumcheck challenges. -/
  nx : Nat

namespace PD

variable (d : PD)

/-- The coordinates. -/
def len : Nat := d.ny + d.nx

/-- Coordinate `i`'s cell. -/
def eb (i : Nat) : Nat := if i < d.ny then d.yb + i else d.xb + d.L * (i - d.ny)

/-- The stride of a chunk of rounds starting at coordinate `i`. -/
def es (i : Nat) : Nat := if i < d.ny then 1 else d.L

/-- The cells. -/
def cells : List Cell := (List.range d.len).map fun i => ec (d.eb i)

/-- Chunks of rounds that do not straddle the two pieces. -/
def ds : List Nat := binParts d.ny ++ binParts d.nx

end PD

theorem chunkStarts_append : ∀ (A B : List Nat) (i₀ : Nat),
    QB.chunkStarts (A ++ B) i₀ = QB.chunkStarts A i₀ ++ QB.chunkStarts B (i₀ + QB.nRounds A)
  | [], B, i₀ => by simp [QB.chunkStarts, QB.nRounds]
  | a :: A, B, i₀ => by
    simp only [List.cons_append, QB.chunkStarts, chunkStarts_append A B, QB.nRounds, List.map_cons,
      List.sum_cons, List.cons_append]
    congr 3
    omega

theorem chunk_ge : ∀ (ds : List Nat) (i₀ i k : Nat), (i, k) ∈ QB.chunkStarts ds i₀ → i₀ ≤ i
  | [], _, _, _, h => by simp [QB.chunkStarts] at h
  | d' :: ds, i₀, i, k, h => by
    simp only [QB.chunkStarts, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact le_rfl
    · have := chunk_ge ds _ i k h
      have := Nat.zero_le (2 ^ d')
      generalize 2 ^ d' = m at *
      omega

theorem nRounds_binParts (n : Nat) : QB.nRounds (binParts n) = n := binParts_sum n

theorem PD.nRounds_ds (d : PD) : QB.nRounds d.ds = d.len := by
  simp only [PD.ds, PD.len, QB.nRounds, List.map_append, List.sum_append]
  rw [binParts_sum, binParts_sum]

theorem PD.length_cells (M : Mem) (d : PD) : (vs M d.cells).length = d.len := by
  simp [vs, PD.cells]

theorem PD.getD_cells (M : Mem) (d : PD) {i : Nat} (hi : i < d.len) :
    (vs M d.cells).getD i 0 = M.e (d.eb i) := by
  simp [vs, PD.cells, List.getD_eq_getElem?_getD, hi]

theorem pointCells_pd (M : Mem) (d : PD) : QB.PointCells M d.ds d.eb d.es (vs M d.cells) := by
  intro i₀ k hm jf hjf
  have hlt := QB.chunk_lt d.ds 0 i₀ k hm jf hjf
  rw [PD.nRounds_ds, Nat.zero_add] at hlt
  rw [PD.getD_cells M d hlt]
  unfold PD.ds at hm
  rw [chunkStarts_append, List.mem_append] at hm
  rcases hm with hm | hm
  · have h1 := QB.chunk_lt _ 0 i₀ k hm jf hjf
    rw [nRounds_binParts, Nat.zero_add] at h1
    simp only [PD.eb, PD.es, if_pos (show i₀ < d.ny by omega), if_pos h1]
    congr 1; omega
  · have h0 := chunk_ge _ _ i₀ k hm
    rw [nRounds_binParts, Nat.zero_add] at h0
    simp only [PD.eb, PD.es, if_neg (show ¬ i₀ < d.ny by omega), if_neg (show ¬ i₀ + jf < d.ny by omega)]
    rw [show i₀ + jf - d.ny = (i₀ - d.ny) + jf by omega, Nat.mul_add, Nat.add_assoc]

/-! ## A step's rounds -/

/-- The equality-mode rounds of a step of `st` levels on the point `d` (none when `d` is empty). -/
def runG (st L₀ : Nat) (d : PD) (c0 : Cell) : BM Cell :=
  if d.len = 0 then pure c0
  else if st = 1 then QB.scRunQ3 d.ds L₀ d.eb d.es c0 else QB.scRunQ5 d.ds L₀ d.eb d.es c0

/-- The rounds, with the cell of the first challenge (round `i`'s at `+ stL st · i`). -/
def runP (st L₀ : Nat) (d : PD) (c0 : Cell) : BM (Cell × Nat) := do
  let q ← getPtr
  let fin ← runG st L₀ d c0
  pure (fin, q.e + 1 + 2 ^ st)

/-- The round template's width (`tplQ3`, `tplQ5`). -/
def stL (st : Nat) : Nat := if st = 1 then 7 else 13

theorem sumcheck_len (claim : FE) (count : Nat) (hc : 2 ≤ count) (eqs : List (Option FE))
    (sig : ByteArray) (s : RS) (hs : s.msg = 0) : (sumcheck claim count eqs sig s).1.1.length = eqs.length := by
  rw [QB.sumcheck_run count hc sig eqs claim s hs]
  simp [QB.scRounds]

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem runP_sound (hS : Q1.Streamed M sig T) {st L₀ : Nat} (hst : st = 1 ∨ st = 2) (d : PD)
    (c0 : Cell) (hT : L₀ + (9 + 3 * 2 ^ st) * d.len ≤ T) :
    SoundG c M (runP st L₀ d c0) fun r => ∀ s : RS, s.msg = 0 → s.ent = 8 * L₀ →
      r.1.val M = (sumcheck (c0.val M) (2 ^ st + 1) ((vs M d.cells).map some) sig s).1.2 ∧
      ∀ i < d.len, M.e (r.2 + stL st * i) =
        (sumcheck (c0.val M) (2 ^ st + 1) ((vs M d.cells).map some) sig s).1.1.getD i 0 := by
  intro p hH _
  simp only [runP, getPtr, bind_apply, pure_apply, Ptr.adv_nil, List.nil_append,
    List.append_nil] at hH ⊢
  intro s hs hent
  have hlanes : ∀ (m : Nat), m = 9 + 3 * 2 ^ st → ∀ j, L₀ ≤ j → j < L₀ + m * QB.nRounds d.ds →
      M.k j = lane sig j := by
    intro m hm j _ hj
    rw [PD.nRounds_ds, hm] at hj
    exact hS j (by omega)
  by_cases h0 : d.len = 0
  · have hc : vs M d.cells = [] := by simp [vs, PD.cells, h0]
    simp only [runG, h0, ite_true, pure_apply, hc, List.map_nil]
    exact ⟨rfl, fun i hi => absurd hi (by omega)⟩
  · rcases hst with rfl | rfl
    · simp only [runG, h0, ite_false, ite_true] at hH ⊢
      have := QB.scRunQ3_eq d.ds L₀ d.eb d.es c0 p hH sig s hs hent (vs M d.cells)
        (by rw [PD.length_cells, PD.nRounds_ds]) (pointCells_pd M d) (hlanes _ rfl)
      rw [PD.nRounds_ds] at this
      rw [show (2 : Nat) ^ 1 + 1 = 3 from rfl]
      refine ⟨this.1, fun i hi => ?_⟩
      rw [← this.2 i hi]
      simp only [stL, ite_true]; congr 1; simp only [pow_one]; omega
    · simp only [runG, h0, ite_false, show ¬ (2 = 1) from by decide] at hH ⊢
      have := QB.scRunQ5_eq d.ds L₀ d.eb d.es c0 p hH sig s hs hent (vs M d.cells)
        (by rw [PD.length_cells, PD.nRounds_ds]) (pointCells_pd M d) (hlanes _ rfl)
      rw [PD.nRounds_ds] at this
      rw [show (2 : Nat) ^ 2 + 1 = 5 from rfl]
      refine ⟨this.1, fun i hi => ?_⟩
      rw [← this.2 i hi]
      simp only [stL, show ¬ (2 = 1) from by decide, ite_false]; congr 1; norm_num; omega

end

/-! ## A GKR step -/

/-- **One GKR step** of `st` levels from position `Q`: the combiner `γ`, the claim
`polyEval values γ` (`hornerG`), the equality-mode rounds, the children, the next challenges, the
finals (`gkrFinals`: products, the gated check, the children's values at the challenges). The next
point is the new challenges, then this step's sumcheck challenges. -/
def stepG (z o g : Cell) (st Q : Nat) (vals : List Cell) (d : PD) : BM (List Cell × PD) := do
  let γ ← ldE ((Q + 40) / 8)
  let c0 ← QB.hornerG z γ vals
  let r ← runP st ((Q + 72) / 8) d c0
  let c₀ ← ldEs ((chB st d.len Q + 40) / 8) 3 (2 ^ st)
  let c₁ ← ldEs ((chB st d.len Q + 40) / 8 + 3 * 2 ^ st) 3 (2 ^ st)
  let c₂ ← ldEs ((chB st d.len Q + 40) / 8 + 6 * 2 ^ st) 3 (2 ^ st)
  let y ← ldEsP ((chB st d.len Q + 72 * 2 ^ st + 40) / 8) 9 st
  let out ← QB.gkrFinals z o g γ r.1 c₀ c₁ c₂ y.2
  pure (out, ⟨y.1, st, r.2, stL st, d.len⟩)

theorem vals_eq_vs (M : Mem) (l : List Cell) : QB.vals M l = vs M l := rfl

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem stepG_sound (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hg : g.val M = 1) {st Q : Nat} (hst : st = 1 ∨ st = 2) (hQ : Q % 8 = 0) (vals : List Cell)
    (d : PD) (hT : stepEnd st d.len Q ≤ 8 * T) :
    SoundG c M (stepG z o g st Q vals d) fun out => ∀ s : RS, pos s = Q → s.ok = true →
      (gkrStep st ⟨vs M vals, vs M d.cells⟩ sig s).2 = ⟨stepEnd st d.len Q, 0, true⟩ ∧
      vs M out.1 = (gkrStep st ⟨vs M vals, vs M d.cells⟩ sig s).1.values ∧
      vs M out.2.cells = (gkrStep st ⟨vs M vals, vs M d.cells⟩ sig s).1.point ∧
      out.2.len = st + d.len := by
  have hst1 : 1 ≤ st := by omega
  have hX : 2 ≤ 2 ^ st := by rcases hst with rfl | rfl <;> norm_num
  have e40 : 8 * ((Q + 40) / 8) = Q + 40 := by omega
  have e72 : 8 * ((Q + 72) / 8) = Q + 72 := by omega
  have hK : chB st d.len Q = Q + 72 + 8 * ((9 + 3 * 2 ^ st) * d.len) := by simp only [chB, rndB]; ring
  have hB8 : chB st d.len Q % 8 = 0 := by
    rw [hK]; generalize (9 + 3 * 2 ^ st) * d.len = K; omega
  have eB : 8 * ((chB st d.len Q + 40) / 8) = chB st d.len Q + 40 := by omega
  have eY : 8 * ((chB st d.len Q + 72 * 2 ^ st + 40) / 8) = chB st d.len Q + 72 * 2 ^ st + 40 := by
    omega
  have hE : stepEnd st d.len Q = chB st d.len Q + 72 * 2 ^ st + 72 * st := rfl
  have hBQ : Q + 72 + (72 + 24 * 2 ^ st) * d.len = chB st d.len Q := by simp [chB, rndB]
  unfold stepG
  refine soundG_bind (ldE_sound hS (a := (Q + 40) / 8) (by omega)) fun γ hγ => ?_
  refine soundG_bind (soundG_aspec (QB.hornerG_spec (c := c) (M := M) (γ := γ) hz vals))
    fun c0 hc0 => ?_
  refine soundG_bind (runP_sound hS hst d c0 (L₀ := (Q + 72) / 8) (by
    generalize (9 + 3 * 2 ^ st) * d.len = K at hK ⊢
    omega)) fun r hr => ?_
  have hch : ∀ k ≤ 2, ∀ i < 2 ^ st,
      (chB st d.len Q + 40) / 8 + 3 * 2 ^ st * k + 3 * i + 2 < T := by
    intro k hk i hi
    have : 8 * ((chB st d.len Q + 40) / 8 + 3 * 2 ^ st * k + 3 * i + 3) ≤
        chB st d.len Q + 40 + 72 * 2 ^ st := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, eB]
      have h1 : 8 * (3 * 2 ^ st * k) ≤ 48 * 2 ^ st := by
        rw [show 8 * (3 * 2 ^ st * k) = 24 * 2 ^ st * k by ring]
        exact (Nat.mul_le_mul_left _ hk).trans (by rw [show 24 * 2 ^ st * 2 = 48 * 2 ^ st by ring])
      omega
    omega
  refine soundG_bind (ldEs_sound hS _ 3 _ fun i hi => by
    have := hch 0 (by omega) i hi; simpa using this) fun c₀ h₀ => ?_
  refine soundG_bind (ldEs_sound hS _ 3 _ fun i hi => by
    have := hch 1 (by omega) i hi; simpa using this) fun c₁ h₁ => ?_
  refine soundG_bind (ldEs_sound hS _ 3 _ fun i hi => by
    have := hch 2 (by omega) i hi; rw [show 3 * 2 ^ st * 2 = 6 * 2 ^ st by ring] at this
    exact this) fun c₂ h₂ => ?_
  refine soundG_bind (ldEsP_sound hS _ 9 st fun i hi => by
    have : 8 * ((chB st d.len Q + 72 * 2 ^ st + 40) / 8 + 9 * i + 3) ≤
        chB st d.len Q + 72 * 2 ^ st + 72 * (st - 1) + 64 := by
      rw [Nat.mul_add, Nat.mul_add, eY]
      have : 9 * i ≤ 9 * (st - 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have : 72 * (st - 1) + 72 = 72 * st := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega) fun y hy => ?_
  refine soundG_bind (soundG_aspec (QB.gkrFinals_spec (c := c) (M := M) (gate := g) (γ := γ)
    (claim := r.1) hz ho c₀ c₁ c₂ y.2)) fun out hout => ?_
  refine soundG_pure ?_
  intro s hs hok
  have hlen : (vs M d.cells).length = d.len := PD.length_cells M d
  rw [gkrStep_run sig st hst1]
  simp only [hs, hlen, hok]
  have hγv : feAt sig (Q + 40) = γ.val M := by rw [hγ, e40]
  have hc0v : polyEval (vs M vals) (feAt sig (Q + 40)) = c0.val M := by rw [hγv, hc0.1]; rfl
  obtain ⟨hr1, hr2⟩ := hr ⟨Q + 72, 0, true⟩ rfl e72.symm
  rw [hc0v]
  have hchv : childrenAt (feAt sig) st (chB st d.len Q) = [vs M c₀, vs M c₁, vs M c₂] := by
    simp only [childrenAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.map_append, List.cons_append, h₀, h₁, h₂, Q1.scalarsAt, List.cons.injEq,
      and_true]
    refine ⟨?_, ?_, ?_⟩ <;> refine List.map_congr_left fun i _ => congrArg _ ?_ <;> omega
  have hyv : Q1.samplesAt (feAt sig) (chB st d.len Q + 72 * 2 ^ st) st = vs M y.2 := by
    rw [hy.1, Q1.samplesAt, vs, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply, Cell.val_E]
    rw [hy.2 i (List.mem_range.mp hi)]
    congr 1; omega
  rw [hchv, hyv]
  have hsl : (sumcheck (Cell.val M c0) (2 ^ st + 1) (List.map some (vs M d.cells)) sig
      ⟨Q + 72, 0, true⟩).1.1.length = d.len := by
    rw [sumcheck_len _ _ (by omega) _ _ _ rfl, List.length_map, hlen]
  refine ⟨?_, ?_, ?_, rfl⟩
  · have hc : (Cell.val M r.1 == polyEval ([vs M c₀, vs M c₁, vs M c₂].map prodE) (Cell.val M γ)) = true := by
      rw [QB.FE.beq_iff]
      have := hout.2
      rw [hg, one_mul, QB.add_eq_zero_iff'] at this
      rw [← this]; rfl
    rw [← hr1, hγv, hc]; rfl
  · rw [← vals_eq_vs, hout.1]; rfl
  · apply List.ext_getElem
    · rw [PD.length_cells, List.length_append, hsl]; simp [PD.len, vs, hy.1]
    · intro i h1 h2
      have hi : i < st + d.len := by rw [PD.length_cells] at h1; exact h1
      rw [← List.getD_eq_getElem _ 0 h1, PD.getD_cells M _ hi]
      by_cases hi1 : i < st
      · rw [List.getElem_append_left (by simp [vs, hy.1]; exact hi1)]
        simp [PD.eb, hi1, vs, hy.1]
      · rw [List.getElem_append_right (by simp [vs, hy.1]; omega)]
        simp only [PD.eb, hi1, if_false]
        rw [hr2 _ (by omega), List.getD_eq_getElem _ 0 (by rw [hsl]; omega)]
        congr 1; simp [vs, hy.1]

end

/-! ## The GKR layers -/

/-- **The GKR's steps** from position `Q`. -/
def layersG (z o g : Cell) : List Nat → Nat → List Cell → PD → BM (List Cell × PD)
  | [], _, vals, d => pure (vals, d)
  | st :: sts, Q, vals, d => do
    let r ← stepG z o g st Q vals d
    layersG z o g sts (stepEnd st d.len Q) r.1 r.2

/-- The position after the steps `sts` from position `Q` on a point of `n` coordinates. -/
def layersEnd : List Nat → Nat → Nat → Nat
  | [], _, Q => Q
  | st :: sts, n, Q => layersEnd sts (st + n) (stepEnd st n Q)

theorem le_stepEnd (st n Q : Nat) : Q ≤ stepEnd st n Q := by simp only [stepEnd, chB]; omega

theorem le_layersEnd : ∀ (sts : List Nat) (n Q : Nat), Q ≤ layersEnd sts n Q
  | [], _, _ => le_rfl
  | st :: sts, n, Q => (le_stepEnd st n Q).trans (le_layersEnd sts _ _)

theorem stepEnd_mod (st n Q : Nat) (hQ : Q % 8 = 0) : stepEnd st n Q % 8 = 0 := by
  have : stepEnd st n Q = Q + 8 * (9 + (9 + 3 * 2 ^ st) * n + 9 * 2 ^ st + 9 * st) := by
    simp only [stepEnd, chB, rndB]; ring
  rw [this]; omega

theorem gkrStep_len (sig : ByteArray) (st : Nat) (hst : 1 ≤ st) (x : GkrState) (s : RS) :
    (gkrStep st x sig s).1.values.length = 3 := by
  rcases x with ⟨vals, pt⟩
  rw [gkrStep_run sig st hst]
  simp [childrenAt]

theorem runSteps_cons (st : Nat) (sts : List Nat) (x : GkrState) (sig : ByteArray) (s : RS) :
    runSteps (st :: sts) x sig s = runSteps sts (gkrStep st x sig s).1 sig (gkrStep st x sig s).2 := rfl

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem layersG_sound (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0)
    (ho : o.val M = 1) (hg : g.val M = 1) : ∀ (sts : List Nat) (Q : Nat) (vals : List Cell) (d : PD),
    (∀ st ∈ sts, st = 1 ∨ st = 2) → Q % 8 = 0 → layersEnd sts d.len Q ≤ 8 * T → vals.length = 3 →
    SoundG c M (layersG z o g sts Q vals d) fun out => ∀ s : RS, pos s = Q → s.ok = true →
      pos (runSteps sts ⟨vs M vals, vs M d.cells⟩ sig s).2 = layersEnd sts d.len Q ∧
      (runSteps sts ⟨vs M vals, vs M d.cells⟩ sig s).2.ok = true ∧
      vs M out.1 = (runSteps sts ⟨vs M vals, vs M d.cells⟩ sig s).1.values ∧
      vs M out.2.cells = (runSteps sts ⟨vs M vals, vs M d.cells⟩ sig s).1.point ∧
      (runSteps sts ⟨vs M vals, vs M d.cells⟩ sig s).1.values.length = 3
  | [], Q, vals, d, _, _, _, hl => soundG_pure fun s hs hok =>
      ⟨hs, hok, rfl, rfl, by simp [runSteps, Q1.pure_run, vs, hl]⟩
  | st :: sts, Q, vals, d, hsts, hQ, hT, _ => by
    have hst := hsts st List.mem_cons_self
    refine soundG_bind (stepG_sound hS hz ho hg hst hQ vals d
      ((le_layersEnd sts _ _).trans hT)) fun r hr => ?_
    have hrl : r.1.length = 3 := by
      have := congrArg List.length (hr ⟨Q, 0, true⟩ (by simp [pos]) rfl).2.1
      rw [gkrStep_len sig st (by omega)] at this
      simpa [vs] using this
    refine soundG_mono (layersG_sound hS hz ho hg sts (stepEnd st d.len Q) r.1 r.2
      (fun x hx => hsts x (List.mem_cons_of_mem _ hx)) (stepEnd_mod st d.len Q hQ) ?_ hrl) ?_
    · have := (hr ⟨Q, 0, true⟩ (by simp [pos]) rfl).2.2.2
      rw [this]; exact hT
    · intro out hout s hs hok
      obtain ⟨h1, h2, h3, h4⟩ := hr s hs hok
      rw [runSteps_cons, h1]
      have hx : (gkrStep st ⟨vs M vals, vs M d.cells⟩ sig s).1 = ⟨vs M r.1, vs M r.2.cells⟩ := by
        rw [h2, h3]
      rw [hx]
      have := hout ⟨stepEnd st d.len Q, 0, true⟩ (by simp [pos]) rfl
      rw [h4] at this
      exact this

end

/-! ## The bus phase -/

/-- The bus phase's output cells. -/
structure BusC where
  /-- The batching challenges `α`. -/
  al : List Cell
  /-- `β`. -/
  be : Cell
  /-- The count root. -/
  cnt : Cell
  /-- The GKR point. -/
  pt : List Cell
  /-- The three trees' values at the point. -/
  vals : List Cell

/-- The position of the GKR's two root scalars (after `α`, `β`). -/
def busP1 (P : Nat) : Nat := P + 72 * (busBits + 1)

/-- The position after the bus phase. -/
def busEnd (p : Params) (P : Nat) : Nat := layersEnd (gkrSteps p.busDepth) 0 (busP1 P + 48) + 24

/-- **Phase 2's gadget** from position `P`. -/
def busG (p : Params) (z o g : Cell) (P : Nat) : BM BusC := do
  let al ← ldEs ((P + 40) / 8) 9 busBits
  let be ← ldE ((P + 40) / 8 + 9 * busBits)
  let sh ← ldE ((busP1 P + 40) / 8)
  let cnt ← ldE ((busP1 P + 40) / 8 + 3)
  QB.countNZ z o g cnt
  let r ← layersG z o g (gkrSteps p.busDepth) (busP1 P + 48) [sh, sh, cnt] ⟨0, 0, 0, 0, 0⟩
  let ld ← ldE ((busEnd p P + 16) / 8)
  assert0 ld g
  pure ⟨al, be, cnt, r.2.cells, r.1⟩

/-- What phase 2 hands on: `F`'s outputs are the cells' values; one leaf-decomposition scalar,
zero; three tree values. -/
def BusR (M : Mem) (res : List FE × FE × FE × List FE × List FE × List FE) (out : BusC) : Prop :=
  res.1 = vs M out.al ∧ res.2.1 = out.be.val M ∧ res.2.2.1 = out.cnt.val M ∧
    res.2.2.2.1 = vs M out.pt ∧ res.2.2.2.2.1 = vs M out.vals ∧ res.2.2.2.2.2 = [0] ∧
    res.2.2.2.2.1.length = 3

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem countNZ_sound {z o g x : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hg : g.val M = 1) :
    SoundG c M (QB.countNZ z o g x) fun _ => (x.val M != 0) = true :=
  fun p hH hA => (QB.countNZ_spec hz ho hg p hH).mp hA

theorem assert0_sound (a g : Cell) : SoundG c M (assert0 a g) fun _ => g.val M * a.val M = 0 :=
  soundG_mono (soundG_aspec (QB.aspec_assert0 a g)) fun _ h => h.2

end

/-- **`F`'s bus phase from position `pos s`**. -/
theorem busPh_run (p : Params) (sig : ByteArray) (s : RS) :
    busPh p sig s =
      let st0 : GkrState := ⟨[feAt sig (busP1 (pos s) + 40), feAt sig (busP1 (pos s) + 40),
        feAt sig (busP1 (pos s) + 64)], []⟩
      let r := runSteps (gkrSteps p.busDepth) st0 sig ⟨busP1 (pos s), 48, s.ok⟩
      ((Q1.samplesAt (feAt sig) (pos s) busBits, feAt sig (pos s + 72 * busBits + 40),
        feAt sig (busP1 (pos s) + 64), r.1.point, r.1.values,
        Q1.scalarsAt (feAt sig) (r.2.ent + r.2.msg + 40) p.leafdecReads),
       { r.2 with ok := (feAt sig (busP1 (pos s) + 64) != 0) && r.2.ok,
                  msg := r.2.msg + 24 * p.leafdecReads }) := by
  simp only [busPh, verifyGkrGrandProducts, Q1.bind_run, Q1.samples_run sig busBits s (by decide),
    Q1.sampleE_run, Q1.readE_run, gkrLayers_eq, require_run, Q1.readEs_run, Q1.pure_run]
  simp only [Q1.samplesAt, busP1, pos, busBits]

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem busG_sound (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hg : g.val M = 1) (p : Params) (hl : p.leafdecReads = 1) {P : Nat} (hP : P % 8 = 0)
    (hT : busEnd p P + 40 ≤ 8 * T) :
    SoundG c M (busG p z o g P) fun out => ∀ s : RS, pos s = P → s.ok = true →
      (busPh p sig s).2.ok = true ∧ pos (busPh p sig s).2 = busEnd p P ∧ BusR M (busPh p sig s).1 out := by
  have hP1 : busP1 P = P + 360 := by simp [busP1, busBits]
  have hLE := le_layersEnd (gkrSteps p.busDepth) 0 (busP1 P + 48)
  have hE : busEnd p P = layersEnd (gkrSteps p.busDepth) 0 (busP1 P + 48) + 24 := rfl
  have hE8 : layersEnd (gkrSteps p.busDepth) 0 (busP1 P + 48) % 8 = 0 := by
    clear hE hLE hT
    have : ∀ (sts : List Nat) (n Q : Nat), Q % 8 = 0 → layersEnd sts n Q % 8 = 0 := by
      intro sts
      induction sts with
      | nil => intro n Q hQ; exact hQ
      | cons st sts ih => intro n Q hQ; exact ih _ _ (stepEnd_mod st n Q hQ)
    exact this _ _ _ (by rw [hP1]; omega)
  unfold busG
  refine soundG_bind (ldEs_sound hS _ 9 busBits fun i hi => by
    simp only [busBits] at hi; omega) fun al hal => ?_
  refine soundG_bind (ldE_sound hS (a := (P + 40) / 8 + 9 * busBits) (by
    simp only [busBits]; omega)) fun be hbe => ?_
  refine soundG_bind (ldE_sound hS (a := (busP1 P + 40) / 8) (by omega)) fun sh hsh => ?_
  refine soundG_bind (ldE_sound hS (a := (busP1 P + 40) / 8 + 3) (by omega)) fun cnt hcnt => ?_
  refine soundG_bind (countNZ_sound (c := c) hz ho hg) fun _ hnz => ?_
  refine soundG_bind (layersG_sound hS hz ho hg _ _ _ _ (gkrSteps_mem _) (by rw [hP1]; omega)
    (by simp only [PD.len, Nat.add_zero]; omega) rfl) fun r hr => ?_
  refine soundG_bind (ldE_sound hS (a := (busEnd p P + 16) / 8) (by omega)) fun ld hld => ?_
  refine soundG_bind (assert0_sound ld g) fun _ hA => ?_
  refine soundG_pure ?_
  intro s hs hok
  rw [busPh_run, hs, hok]
  have e40 : 8 * ((busP1 P + 40) / 8) = busP1 P + 40 := by omega
  have e64 : 8 * ((busP1 P + 40) / 8 + 3) = busP1 P + 64 := by omega
  have hst0 : (⟨[feAt sig (busP1 P + 40), feAt sig (busP1 P + 40), feAt sig (busP1 P + 64)], []⟩ :
      GkrState) = ⟨vs M [sh, sh, cnt], vs M (⟨0, 0, 0, 0, 0⟩ : PD).cells⟩ := by
    simp only [vs, List.map_cons, List.map_nil, hsh, hcnt, e40, e64]; rfl
  rw [hst0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hr ⟨busP1 P, 48, true⟩ (by simp [pos]) rfl
  simp only [PD.len, Nat.add_zero] at h1
  dsimp only
  generalize runSteps (gkrSteps p.busDepth) ⟨vs M [sh, sh, cnt], vs M (⟨0, 0, 0, 0, 0⟩ : PD).cells⟩
    sig ⟨busP1 P, 48, true⟩ = R at h1 h2 h3 h4 h5
  have hnz' : (feAt sig (busP1 P + 64) != 0) = true := by rw [← e64, ← hcnt]; exact hnz
  rw [hl]
  have hld0 : feAt sig (R.2.ent + R.2.msg + 40) = 0 := by
    have := hA
    rw [hg, one_mul] at this
    rw [← this, hld]
    have : R.2.ent + R.2.msg = layersEnd (gkrSteps p.busDepth) 0 (busP1 P + 48) := h1
    exact congrArg (feAt sig) (by omega)
  refine ⟨by simp [h2, hnz'], by simp only [pos] at h1 ⊢; omega, ?_, ?_, ?_, h4.symm, h3.symm, ?_, h5⟩
  · rw [hal, Q1.samplesAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    omega
  · rw [hbe]; exact congrArg (feAt sig) (by simp only [busBits]; omega)
  · rw [hcnt, e64]
  · simp [Q1.scalarsAt, hld0]

end

/-! ## The headline -/

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **Phase 2 replayed** (soundness direction): wherever `busG`'s rows hold and assert (gate on),
`F`'s bus phase from any state at position `P` with `ok` keeps `ok`, ends at `busEnd p P`, and its
outputs are the output cells' values, with `leafdec = [0]` and three tree values. -/
theorem busG_replays (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0)
    (ho : o.val M = 1) (hg : g.val M = 1) (p : Params) (hl : p.leafdecReads = 1) {P : Nat}
    (hP : P % 8 = 0) (hT : busEnd p P + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig (busPh p) (busG p z o g P) ptr P (busEnd p P) (BusR M) :=
  fun hok s hs hsok => soundG_ok (busG_sound hS hz ho hg p hl hP hT) hok s hs hsok

end

/-- Phase 2's start: after `q₀`, the seed and the two cap skips. -/
def busPos (p : Params) : Nat :=
  RS.start.ent + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap + nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap

theorem busPos_mod_P20 : busPos P20 % 8 = 0 := by decide
theorem busPos_mod_P8 : busPos P8 % 8 = 0 := by decide

/-- **Phase 2 at `P20`.** -/
theorem busG_replays_P20 {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} (hS : Q1.Streamed M sig T)
    {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hg : g.val M = 1)
    (hT : busEnd P20 (busPos P20) + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig (busPh P20) (busG P20 z o g (busPos P20)) ptr (busPos P20) (busEnd P20 (busPos P20))
      (BusR M) :=
  busG_replays hS hz ho hg P20 rfl busPos_mod_P20 hT ptr

/-- **Phase 2 at `P8`.** -/
theorem busG_replays_P8 {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} (hS : Q1.Streamed M sig T)
    {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hg : g.val M = 1)
    (hT : busEnd P8 (busPos P8) + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig (busPh P8) (busG P8 z o g (busPos P8)) ptr (busPos P8) (busEnd P8 (busPos P8))
      (BusR M) :=
  busG_replays hS hz ho hg P8 rfl busPos_mod_P8 hT ptr

end Lvm.Har
