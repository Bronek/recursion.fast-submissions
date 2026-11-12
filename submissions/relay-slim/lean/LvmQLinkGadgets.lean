-- New for lvm (WP-11b-QL): Q_link's LoopIR gadgets, written with LvmQBuild.
import LvmQBuildLemmas

/-!
# Q_link's gadgets

* **`checkLoop dims gate chks`**: one loop block; per iteration and per check `⟨A, B, k, k'⟩` (affine
  `K` operands) a `lin` row `A + k·B + k'` and an `assert0` of it under `gate`. `checkLoop_spec`: when
  the gate is `1`, `A = k·B + k'` at every iteration (characteristic 2). Length lanes (`A = len`:
  `k = 0`, `k' = len`), FS state copies (`A = B`: `k = 1`) and constant lanes are checks.
* **`nodeLoop`**: per iteration a node query's selection: per lane `S = L + R`, `c = β·S + L`,
  `c = P`. `nodeLoop_spec`: with `β` a bit, `P = (β = 1 ? R : L)` on each of the four lanes.
* **`capLoop`**: per iteration the cap check of a path: the address `g^(lo + 4 · Σ_z β_z 2^z)` from
  the cap bits, its three successors, four `readd` and four equality checks. `capLoop_spec`: with
  bits and `GInj`, the four answer lanes are the cap node's.
* **`split`**: a family of `n` iterations as loops of `2^a` iterations at the binary digits of `n`
  (`chunks`); `split_cover`: every `k < n` lies in one chunk.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-! ## Chunks -/

/-- The binary chunks of `[s, s + rem)`: `(start, log size)`, largest first (greedy, at most
`fuel` of them). -/
def chunksG : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | fuel + 1, s, rem => if rem = 0 then [] else
      (s, rem.log2) :: chunksG fuel (s + 2 ^ rem.log2) (rem - 2 ^ rem.log2)

/-- The chunks of `[0, n)`: one per binary digit of `n`. -/
def chunks (n : Nat) : List (Nat × Nat) := chunksG n 0 n

theorem chunksG_cover : ∀ (fuel s rem k : Nat), rem ≤ fuel → s ≤ k → k < s + rem →
    ∃ c ∈ chunksG fuel s rem, c.1 ≤ k ∧ k < c.1 + 2 ^ c.2
  | 0, _, _, _, h, h1, h2 => by omega
  | fuel + 1, s, rem, k, h, h1, h2 => by
    have hr : rem ≠ 0 := by omega
    have hle := Nat.log2_self_le hr
    simp only [chunksG, hr, ite_false]
    by_cases hk : k < s + 2 ^ rem.log2
    · exact ⟨(s, rem.log2), by simp, h1, hk⟩
    · have hpos := Nat.two_pow_pos rem.log2
      obtain ⟨c, hc, hc1, hc2⟩ := chunksG_cover fuel (s + 2 ^ rem.log2) (rem - 2 ^ rem.log2) k (by omega)
        (by omega) (by omega)
      exact ⟨c, by simp [hc], hc1, hc2⟩

/-- **Every `k < n` lies in a chunk.** -/
theorem chunks_cover {n k : Nat} (hk : k < n) : ∃ c ∈ chunks n, c.1 ≤ k ∧ k < c.1 + 2 ^ c.2 :=
  chunksG_cover n 0 n k le_rfl (by omega) (by omega)

/-- Run `f s a` for every chunk `(s, a)`. -/
def splitRun (cs : List (Nat × Nat)) (f : Nat → Nat → BM Unit) : BM Unit := do
  let _ ← seqAll (cs.map fun c => f c.1 c.2)
  pure ()

theorem seqAll_hold {c : Ctx} {M : Mem} {α : Type} :
    ∀ (ms : List (BM α)) (p : Ptr), SegsHold c M p (seqAll ms p).2 →
      ∀ m ∈ ms, ∃ q, SegsHold c M q (m q).2
  | [], _, _, _, h => by simp at h
  | m :: ms, p, h, m', hm => by
    simp only [seqAll] at h
    rw [hold_bind] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨p, h.1⟩
    · rw [hold_bind] at h
      exact seqAll_hold ms _ h.2.1 m' hm

/-! ## Check loops -/

/-- An equality check `A = k·B + k'` on affine `K` operands. -/
structure Chk where
  /-- The checked operand. -/
  A : Addr
  /-- The other operand. -/
  B : Addr
  /-- The factor. -/
  k : FK
  /-- The constant. -/
  k' : FK

/-- The rows of checks `c₀, c₀ + 1, …`: per check a `lin` and an `assert0` of it. -/
def chkRows (gate : Cell) : Nat → List Chk → List LRow
  | _, [] => []
  | c, ch :: rest => ⟨.lin ch.k ch.k', .K, [.abs ch.A, .abs ch.B]⟩ ::
      ⟨.assert0, .K, [.cur (2 * c), gate.opd]⟩ :: chkRows gate (c + 1) rest

/-- **A check loop**: the checks at every loop index of `dims`. -/
def checkLoop (dims : List Nat) (gate : Cell) (chks : List Chk) : BM Unit := do
  let _ ← loop dims (chkRows gate 0 chks)
  pure ()

theorem chkRows_getD (gate : Cell) : ∀ (chks : List Chk) (c₀ i : Nat), i < chks.length →
    (chkRows gate c₀ chks).getD (2 * i) default =
        ⟨.lin (chks.getD i ⟨default, default, 0, 0⟩).k (chks.getD i ⟨default, default, 0, 0⟩).k', .K,
          [.abs (chks.getD i ⟨default, default, 0, 0⟩).A, .abs (chks.getD i ⟨default, default, 0, 0⟩).B]⟩ ∧
      (chkRows gate c₀ chks).getD (2 * i + 1) default = ⟨.assert0, .K, [.cur (2 * (c₀ + i)), gate.opd]⟩
  | [], _, _, h => absurd h (by simp)
  | ch :: rest, c₀, 0, _ => by simp [chkRows]
  | ch :: rest, c₀, i + 1, h => by
    have ih := chkRows_getD gate rest (c₀ + 1) i (by simpa using h)
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl,
      show 2 * (c₀ + (i + 1)) = 2 * (c₀ + 1 + i) by ring]
    simp only [chkRows, List.getD_cons_succ]
    exact ih

theorem chkRows_length (gate : Cell) : ∀ (chks : List Chk) (c₀ : Nat), (chkRows gate c₀ chks).length = 2 * chks.length
  | [], _ => rfl
  | _ :: rest, c₀ => by simp [chkRows, chkRows_length gate rest]; ring

/-- **A check loop's checks hold** at every loop index when the gate is `1`. -/
theorem checkLoop_spec {c : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {gate : Cell} {chks : List Chk}
    (h : SegsHold c M p (checkLoop dims gate chks p).2) (hA : SegsAssert M p (checkLoop dims gate chks p).2)
    (hK : ∀ ch ∈ chks, ch.A.ty = .K ∧ ch.B.ty = .K) (hg : gate.ty = .K) (hg1 : M.k gate.n = 1) :
    ∀ jf < 2 ^ dims.sum, ∀ ch ∈ chks,
      M.k (ch.A.at (unflat dims jf)) = ch.k * M.k (ch.B.at (unflat dims jf)) + ch.k' := by
  intro jf hjf ch hch
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hch
  simp only [checkLoop, hold_bind, assert_bind] at h hA
  have hr := chkRows_getD gate chks 0 i hi
  have hgd : chks.getD i ⟨default, default, 0, 0⟩ = chks[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hgd] at hr
  have hl := lrel_lin hr.1 (loop_rel h.1 hjf (by rw [chkRows_length]; omega))
  have ha := lassert_of hr.2 (loop_assert hA.1 hjf (by rw [chkRows_length]; omega))
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add] at hl ha
  rw [Cell.val_opd, Opd.val_cur _ _ hjf, hl] at ha
  obtain ⟨hAK, hBK⟩ := hK _ hch
  obtain ⟨gn, rfl⟩ : ∃ n, gate = kc n := ⟨gate.n, by cases gate; simp_all [kc]⟩
  generalize chks[i] = ch at *
  obtain ⟨⟨τA, bA, sA⟩, ⟨τB, bB, sB⟩, k, k'⟩ := ch
  simp only at hAK hBK
  subst hAK hBK
  simp only [Opd.val_absK, Cell.val_K, hg1, ofK_one, one_mul, loop_apply] at ha
  rw [← ofK_mul, ← ofK_add, ← ofK_add, ← ofK_zero] at ha
  have := ofK_inj ha
  simp only [Addr.at]
  have e := congrArg (· + (k * M.k (bB + dot sB (unflat dims jf)) + k')) this
  simp only [zero_add] at e
  rw [← e]
  generalize M.k (bA + dot sA (unflat dims jf)) = A
  generalize k * M.k (bB + dot sB (unflat dims jf)) = X
  have : A + X + k' + (X + k') = A + ((X + X) + (k' + k')) := by ring
  rw [this, FK.add_self, FK.add_self, add_zero, add_zero]

/-! ## The table-driven lane checks (QLT) -/

/-- The template of the QLT loop: per iteration `k`, from the table cells `qt + 3k + {0, 1, 2}`
(`α = g^e₁`, `β = g^e₂`, `v`): the addresses `g^l·α` (`l = 1…4`) and `g^l·β` (`l = 1…3`), nine
`readd`s (region `[lo, lo + 2^m)`), and the checks `mem[e₁] = v`, `mem[e₁ + 1 + l] = mem[e₂ + l]`. -/
def qltTpl (qt lo m : Nat) (gate : Cell) : List LRow :=
  let α : Opd := .abs ⟨.K, qt, [3]⟩
  let β : Opd := .abs ⟨.K, qt + 1, [3]⟩
  let v : Opd := .abs ⟨.K, qt + 2, [3]⟩
  [⟨.lin (gpow 1 + 1) 0, .K, [α, α]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [α, α]⟩,
   ⟨.lin (gpow 3 + 1) 0, .K, [α, α]⟩, ⟨.lin (gpow 4 + 1) 0, .K, [α, α]⟩,
   ⟨.lin (gpow 1 + 1) 0, .K, [β, β]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [β, β]⟩,
   ⟨.lin (gpow 3 + 1) 0, .K, [β, β]⟩,
   ⟨.readd lo m, .K, [α]⟩, ⟨.readd lo m, .K, [.cur 0]⟩, ⟨.readd lo m, .K, [.cur 1]⟩,
   ⟨.readd lo m, .K, [.cur 2]⟩, ⟨.readd lo m, .K, [.cur 3]⟩,
   ⟨.readd lo m, .K, [β]⟩, ⟨.readd lo m, .K, [.cur 4]⟩, ⟨.readd lo m, .K, [.cur 5]⟩,
   ⟨.readd lo m, .K, [.cur 6]⟩,
   ⟨.lin 1 0, .K, [.cur 7, v]⟩, ⟨.assert0, .K, [.cur 16, gate.opd]⟩,
   ⟨.lin 1 0, .K, [.cur 8, .cur 12]⟩, ⟨.assert0, .K, [.cur 18, gate.opd]⟩,
   ⟨.lin 1 0, .K, [.cur 9, .cur 13]⟩, ⟨.assert0, .K, [.cur 20, gate.opd]⟩,
   ⟨.lin 1 0, .K, [.cur 10, .cur 14]⟩, ⟨.assert0, .K, [.cur 22, gate.opd]⟩,
   ⟨.lin 1 0, .K, [.cur 11, .cur 15]⟩, ⟨.assert0, .K, [.cur 24, gate.opd]⟩]

/-- **The QLT loop** over `2^a` table entries. -/
def qltLoop (a qt lo m : Nat) (gate : Cell) : BM Unit := do
  let _ ← loop [a] (qltTpl qt lo m gate)
  pure ()

theorem unflat_one' {a jf : Nat} (h : jf < 2 ^ [a].sum) : unflat [a] jf = [jf] := by
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h
  simp [unflat, Nat.mod_eq_of_lt h]

theorem gpow_scale (l x : Nat) : gpow x + (gpow l + 1) * gpow x + 0 = gpow (x + l) := by
  rw [gpow_add, add_zero]
  have : gpow x + (gpow l + 1) * gpow x = gpow l * gpow x + (gpow x + gpow x) := by ring
  rw [this, FK.add_self, add_zero, mul_comm]

/-- A loop `readd` whose address operand holds `g^e` reads cell `e`. -/
theorem lreadd_spec {c : Ctx} {M : Mem} {o : LoopOut} {jf t lo m : Nat} {args : List Opd}
    (hr : o.tpl.getD t default = ⟨.readd lo m, .K, args⟩) (h : LRel c M o jf t) {N e : Nat}
    (hinj : GInj N) (hN : c.cells .K ≤ N) (he : e < N)
    (hα : ((args.getD 0 default).val M o jf).c₀ = gpow e) : (o.cell t jf).val M = FE.ofK (M.k e) := by
  obtain ⟨e', he', hx, hres⟩ := lrel_readd hr h
  rw [hα] at hx
  have := hinj e' e (by omega) he hx
  subst this
  exact hres

/-- **The QLT loop's checks**: at every iteration whose table entry holds `α = g^e₁`, `β = g^e₂`
(addresses below `N`, `g`-powers injective below `N`), when the gate is `1`:
`mem[e₁] = v` and `mem[e₁ + 1 + l] = mem[e₂ + l]` for `l < 4`. -/
theorem qltLoop_spec {c : Ctx} {M : Mem} {p : Ptr} {a qt lo m : Nat} {g : Nat}
    (h : SegsHold c M p (qltLoop a qt lo m (kc g) p).2) (hA : SegsAssert M p (qltLoop a qt lo m (kc g) p).2)
    (hg1 : M.k g = 1) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    {jf e₁ e₂ : Nat} (hjf : jf < 2 ^ a) (he₁ : e₁ + 5 ≤ N) (he₂ : e₂ + 4 ≤ N)
    (hα : M.k (qt + 3 * jf) = gpow e₁) (hβ : M.k (qt + 1 + 3 * jf) = gpow e₂) :
    M.k e₁ = M.k (qt + 2 + 3 * jf) ∧ ∀ l < 4, M.k (e₁ + 1 + l) = M.k (e₂ + l) := by
  simp only [qltLoop, hold_bind, assert_bind] at h hA
  have hj : jf < 2 ^ [a].sum := by simpa using hjf
  set o := (loop [a] (qltTpl qt lo m (kc g)) p).1 with ho
  have hR := fun t (ht : t < 26) => loop_rel h.1 hj (t := t) (by simp [qltTpl]; omega)
  have hS := fun t (ht : t < 26) => loop_assert hA.1 hj (t := t) (by simp [qltTpl]; omega)
  have hu : unflat o.dims jf = [jf] := unflat_one' hj
  -- the operand values
  have vα : (Opd.abs ⟨.K, qt, [3]⟩).val M o jf = FE.ofK (gpow e₁) := by
    rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]; rw [hα]
  have vβ : (Opd.abs ⟨.K, qt + 1, [3]⟩).val M o jf = FE.ofK (gpow e₂) := by
    rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]; rw [hβ]
  have vv : (Opd.abs ⟨.K, qt + 2, [3]⟩).val M o jf = FE.ofK (M.k (qt + 2 + 3 * jf)) := by
    rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]
  -- the addresses g^l·α, g^l·β
  have hadr : ∀ (t l e : Nat) (x : Opd), o.tpl.getD t default = ⟨.lin (gpow l + 1) 0, .K, [x, x]⟩ →
      x.val M o jf = FE.ofK (gpow e) → t < 26 → (o.cell t jf).val M = FE.ofK (gpow (e + l)) := by
    intro t l e x hr hx ht
    rw [lrel_lin hr (hR t ht)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, hx, ofK_zero, add_zero]
    rw [← ofK_mul, ← ofK_add, ← gpow_scale l e, add_zero]
  have a1 := hadr 0 1 e₁ _ rfl vα (by omega)
  have a2 := hadr 1 2 e₁ _ rfl vα (by omega)
  have a3 := hadr 2 3 e₁ _ rfl vα (by omega)
  have a4 := hadr 3 4 e₁ _ rfl vα (by omega)
  have b1 := hadr 4 1 e₂ _ rfl vβ (by omega)
  have b2 := hadr 5 2 e₂ _ rfl vβ (by omega)
  have b3 := hadr 6 3 e₂ _ rfl vβ (by omega)
  -- the reads
  have hrd : ∀ (t : Nat) (x : Opd) (e : Nat), o.tpl.getD t default = ⟨.readd lo m, .K, [x]⟩ →
      x.val M o jf = FE.ofK (gpow e) → e < N → t < 26 → (o.cell t jf).val M = FE.ofK (M.k e) := by
    intro t x e hr hx he ht
    exact lreadd_spec hr (hR t ht) hinj hN he (by simp [hx]; rfl)
  have r0 := hrd 7 _ e₁ rfl vα (by omega) (by omega)
  have r1 := hrd 8 (.cur 0) (e₁ + 1) rfl (by rw [Opd.val_cur _ _ hj]; exact a1) (by omega) (by omega)
  have r2 := hrd 9 (.cur 1) (e₁ + 2) rfl (by rw [Opd.val_cur _ _ hj]; exact a2) (by omega) (by omega)
  have r3 := hrd 10 (.cur 2) (e₁ + 3) rfl (by rw [Opd.val_cur _ _ hj]; exact a3) (by omega) (by omega)
  have r4 := hrd 11 (.cur 3) (e₁ + 4) rfl (by rw [Opd.val_cur _ _ hj]; exact a4) (by omega) (by omega)
  have s0 := hrd 12 _ e₂ rfl vβ (by omega) (by omega)
  have s1 := hrd 13 (.cur 4) (e₂ + 1) rfl (by rw [Opd.val_cur _ _ hj]; exact b1) (by omega) (by omega)
  have s2 := hrd 14 (.cur 5) (e₂ + 2) rfl (by rw [Opd.val_cur _ _ hj]; exact b2) (by omega) (by omega)
  have s3 := hrd 15 (.cur 6) (e₂ + 3) rfl (by rw [Opd.val_cur _ _ hj]; exact b3) (by omega) (by omega)
  -- the checks
  have hchk : ∀ (t : Nat) (x y : Opd) (X Y : FK), o.tpl.getD t default = ⟨.lin 1 0, .K, [x, y]⟩ →
      o.tpl.getD (t + 1) default = ⟨.assert0, .K, [.cur t, (kc g).opd]⟩ →
      x.val M o jf = FE.ofK X → y.val M o jf = FE.ofK Y → t + 1 < 26 → X = Y := by
    intro t x y X Y hr hr2 hx hy ht
    have hl := lrel_lin hr (hR t (by omega))
    have ha := lassert_of hr2 (hS (t + 1) ht)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hl ha
    rw [Cell.val_opd, Opd.val_cur _ _ hj, hl, hx, hy, Cell.val_K, hg1, ofK_one, one_mul,
      ofK_zero, add_zero, one_mul, ← ofK_add] at ha
    have := ofK_inj (ha.trans ofK_zero.symm)
    have e := congrArg (· + Y) this
    simpa [add_assoc, FK.add_self] using e
  refine ⟨hchk 16 (.cur 7) _ _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r0) vv (by omega), fun l hl => ?_⟩
  interval_cases l
  · exact hchk 18 (.cur 8) (.cur 12) _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r1)
      (by rw [Opd.val_cur _ _ hj]; exact s0) (by omega)
  · exact hchk 20 (.cur 9) (.cur 13) _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r2)
      (by rw [Opd.val_cur _ _ hj]; exact s1) (by omega)
  · exact hchk 22 (.cur 10) (.cur 14) _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r3)
      (by rw [Opd.val_cur _ _ hj]; exact s2) (by omega)
  · exact hchk 24 (.cur 11) (.cur 15) _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r4)
      (by rw [Opd.val_cur _ _ hj]; exact s3) (by omega)

/-! ## Node queries -/

/-- A `K` word with the bits of `n` (not the field's `n`!). -/
def kOf (n : Nat) : FK := ⟨n.toUInt64⟩

/-- The rows of one lane `l` of a node check (rows `2 + 4l …`): `S = L + R`, `c = β·S + L`,
`d = c + P`, `z·d = 0`. -/
def nodeLane (L R P : Nat) (s : List Nat) (β g : Opd) (l : Nat) : List LRow :=
  [⟨.lin 1 0, .K, [.abs ⟨.K, L + l, s⟩, .abs ⟨.K, R + l, s⟩]⟩,
   ⟨.muladd, .K, [β, .cur (2 + 4 * l), .abs ⟨.K, L + l, s⟩]⟩,
   ⟨.lin 1 0, .K, [.cur (3 + 4 * l), .abs ⟨.K, P + l, s⟩]⟩,
   ⟨.assert0, .K, [.cur (4 + 4 * l), g]⟩]

/-- **The node template**: the length lane `len` is 64, and on each of the four lanes the previous
answer `P` is the half (`L` or `R`) the bit `β` selects; `z` gates every assertion. Lane operands move
with strides `s`, the bit with `sb`, the gate with `sz`. -/
def nodeTpl (len L R P : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (z : Nat) (sz : List Nat) : List LRow :=
  let β : Opd := .abs ⟨.K, bt, sb⟩
  let g : Opd := .abs ⟨.K, z, sz⟩
  [⟨.lin 0 (kOf 64), .K, [.abs ⟨.K, len, s⟩, .abs ⟨.K, len, s⟩]⟩, ⟨.assert0, .K, [.cur 0, g]⟩] ++
    nodeLane L R P s β g 0 ++ nodeLane L R P s β g 1 ++ nodeLane L R P s β g 2 ++ nodeLane L R P s β g 3

def nodeLoop (dims : List Nat) (len L R P : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (z : Nat)
    (sz : List Nat) : BM Unit := do
  let _ ← loop dims (nodeTpl len L R P s bt sb z sz)
  pure ()

theorem char2_eq {a b : FK} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h; simpa [add_assoc, FK.add_self] using this

/-- The value of an `assert0` row's gated check: `z·d = 0`, `z = 1` gives `d = 0`. -/
theorem gate_one {z d : FK} (h : FE.ofK z * FE.ofK d = 0) (hz : z = 1) : d = 0 := by
  rw [hz, ofK_one, one_mul, ← ofK_zero] at h; exact ofK_inj h

/-- **A node check**: with the gate `1` and the bit a bit, the length lane is 64 and each lane of the
previous answer is the selected half's. -/
theorem nodeLoop_spec {c : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {len L R P bt z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold c M p (nodeLoop dims len L R P s bt sb z sz p).2)
    (hA : SegsAssert M p (nodeLoop dims len L R P s bt sb z sz p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hz : M.k (z + dot sz (unflat dims jf)) = 1)
    (hb : M.k (bt + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + dot sb (unflat dims jf)) = 1) :
    M.k (len + dot s (unflat dims jf)) = kOf 64 ∧ ∀ l < 4, M.k (P + l + dot s (unflat dims jf)) =
      if M.k (bt + dot sb (unflat dims jf)) = 1 then M.k (R + l + dot s (unflat dims jf))
      else M.k (L + l + dot s (unflat dims jf)) := by
  simp only [nodeLoop, hold_bind, assert_bind] at h hA
  have hR := fun t (ht : t < 18) => loop_rel h.1 hjf (t := t) (by simp [nodeTpl, nodeLane]; omega)
  have hS := fun t (ht : t < 18) => loop_assert hA.1 hjf (t := t) (by simp [nodeTpl, nodeLane]; omega)
  have hd : (loop dims (nodeTpl len L R P s bt sb z sz) p).1.dims = dims := rfl
  have vK : ∀ (b : Nat) (st : List Nat), (Opd.abs ⟨.K, b, st⟩).val M (loop dims (nodeTpl len L R P s bt sb z sz) p).1 jf = FE.ofK (M.k (b + dot st (unflat dims jf))) :=
    fun b st => by rw [Opd.val_absK, hd]
  have vc : ∀ t, (Opd.cur t).val M (loop dims (nodeTpl len L R P s bt sb z sz) p).1 jf = ((loop dims (nodeTpl len L R P s bt sb z sz) p).1.cell t jf).val M := fun t => Opd.val_cur _ _ hjf t
  -- a gated zero
  have hzero : ∀ t, t + 1 < 18 → (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (t + 1) default = ⟨.assert0, .K, [.cur t, .abs ⟨.K, z, sz⟩]⟩ →
      ∀ X : FK, ((loop dims (nodeTpl len L R P s bt sb z sz) p).1.cell t jf).val M = FE.ofK X → X = 0 := by
    intro t ht hr X hX
    have := lassert_of hr (hS (t + 1) ht)
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, hX] at this
    exact gate_one this hz
  refine ⟨?_, fun l hl => ?_⟩
  · have h0 := lrel_lin (t := 0) rfl (hR 0 (by omega))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, ofK_zero, zero_mul, add_zero] at h0
    rw [← ofK_add] at h0
    exact char2_eq (hzero 0 (by omega) rfl _ h0)
  · have key : ∀ (lv : Nat), lv < 4 →
        (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (2 + 4 * lv) default = ⟨.lin 1 0, .K, [.abs ⟨.K, L + lv, s⟩, .abs ⟨.K, R + lv, s⟩]⟩ ∧
        (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (3 + 4 * lv) default = ⟨.muladd, .K, [.abs ⟨.K, bt, sb⟩, .cur (2 + 4 * lv), .abs ⟨.K, L + lv, s⟩]⟩ ∧
        (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (4 + 4 * lv) default = ⟨.lin 1 0, .K, [.cur (3 + 4 * lv), .abs ⟨.K, P + lv, s⟩]⟩ ∧
        (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (4 + 4 * lv + 1) default = ⟨.assert0, .K, [.cur (4 + 4 * lv), .abs ⟨.K, z, sz⟩]⟩ := by
      intro lv hlv; interval_cases lv <;> exact ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨k1, k2, k3, k4⟩ := key l hl
    have e1 := lrel_lin k1 (hR _ (by omega))
    have e2 := lrel_muladd k2 (hR _ (by omega))
    have e3 := lrel_lin k3 (hR _ (by omega))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, ofK_one, one_mul, ofK_zero, add_zero] at e1 e2 e3
    rw [e1] at e2; rw [e2] at e3
    rw [← ofK_add, ← ofK_mul, ← ofK_add, ← ofK_add] at e3
    have hd0 := hzero (4 + 4 * l) (by omega) k4 _ e3
    have hP := (char2_eq hd0).symm
    rw [hP]
    rcases hb with h0 | h1
    · rw [h0]; simp [show (0 : FK) ≠ 1 from by decide]
    · rw [h1, if_pos rfl, one_mul]
      generalize M.k (L + l + dot s (unflat dims jf)) = a
      have : a + M.k (R + l + dot s (unflat dims jf)) + a = M.k (R + l + dot s (unflat dims jf)) + (a + a) := by ring
      rw [this, FK.add_self, add_zero]

/-! ## Cap checks -/

/-- The address chain's rows for bits `1 … c − 1`: per bit `z` (rows `2z + 1`, `2z + 2`)
`u = (G + 1)·acc`, `acc' = β_z·u + acc` with `G = g^(4 · 2^z)`. -/
def capChain (bt : Nat) (sb : List Nat) (c : Nat) : List LRow :=
  (List.range (c - 1)).flatMap fun y =>
    [⟨.lin (gpow (4 * 2 ^ (y + 1))) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩,
     ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩]

/-- **The cap template** (per position): the leaf's length lane is the row length; the address
`α = g^(lo + 4 · Σ_z β_z 2^z)` from the `c` cap bits (row `2c`), `g^l·α`, four `readd`s, and the four
answer lanes `A + l` equal to them. Lane operands move with `s`, bits with `sb`, the gate with `sz`. -/
def capTpl (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat) (sz : List Nat) :
    List LRow :=
  let g : Opd := .abs ⟨.K, z, sz⟩
  let e := 2 * c
  [⟨.lin 0 (kOf row), .K, [.abs ⟨.K, lenL, s⟩, .abs ⟨.K, lenL, s⟩]⟩, ⟨.assert0, .K, [.cur 0, g]⟩,
   ⟨.lin (gpow lo * (gpow 4 + 1) + 1) (gpow lo), .K, [.abs ⟨.K, bt, sb⟩, .abs ⟨.K, bt, sb⟩]⟩] ++
  capChain bt sb c ++
  [⟨.lin (gpow 1 + 1) 0, .K, [.cur e, .cur e]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [.cur e, .cur e]⟩,
   ⟨.lin (gpow 3 + 1) 0, .K, [.cur e, .cur e]⟩,
   ⟨.readd rlo m, .K, [.cur e]⟩, ⟨.readd rlo m, .K, [.cur (e + 1)]⟩, ⟨.readd rlo m, .K, [.cur (e + 2)]⟩,
   ⟨.readd rlo m, .K, [.cur (e + 3)]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 4), .abs ⟨.K, A, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 8), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 5), .abs ⟨.K, A + 1, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 10), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 6), .abs ⟨.K, A + 2, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 12), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 7), .abs ⟨.K, A + 3, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 14), g]⟩]

def capLoop (dims : List Nat) (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) : BM Unit := do
  let _ ← loop dims (capTpl lenL row A lo rlo m s bt sb c z sz)
  pure ()

theorem capChain_length (bt : Nat) (sb : List Nat) (c : Nat) : (capChain bt sb c).length = 2 * (c - 1) := by
  simp [capChain, List.length_flatMap]; ring

theorem capChain_getD (bt : Nat) (sb : List Nat) (c y : Nat) (hy : y + 1 < c) :
    (capChain bt sb c).getD (2 * y) default =
      ⟨.lin (gpow (4 * 2 ^ (y + 1))) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩ ∧
    (capChain bt sb c).getD (2 * y + 1) default =
      ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩ := by
  suffices h : ∀ (n k y : Nat), y < n →
      ((List.range' k n).flatMap fun y : Nat =>
        [(⟨.lin (gpow (4 * 2 ^ (y + 1))) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩ : LRow),
         ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩]).getD (2 * y) default =
        ⟨.lin (gpow (4 * 2 ^ (k + y + 1))) 0, .K, [.cur (2 * (k + y + 1)), .cur (2 * (k + y + 1))]⟩ ∧
      ((List.range' k n).flatMap fun y : Nat =>
        [(⟨.lin (gpow (4 * 2 ^ (y + 1))) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩ : LRow),
         ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩]).getD (2 * y + 1) default =
        ⟨.muladd, .K, [.abs ⟨.K, bt + (k + y + 1), sb⟩, .cur (2 * (k + y + 1) + 1), .cur (2 * (k + y + 1))]⟩ by
    have := h (c - 1) 0 y (by omega)
    simpa [capChain, List.range_eq_range'] using this
  intro n
  induction n with
  | zero => intro k y hy; omega
  | succ n ih =>
    intro k y hy
    rw [List.range'_succ, List.flatMap_cons]
    rcases y with _ | y
    · simp
    · have := ih (k + 1) y (by omega)
      rw [show 2 * (y + 1) = 2 * y + 1 + 1 by ring, show 2 * y + 1 + 1 + 1 = 2 * y + 1 + 1 + 1 from rfl]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      rw [show k + (y + 1) = k + 1 + y by omega]
      exact this

/-- The number whose bit `y < n` is `1` iff cell `bt + y` (moved by `st` at `J`) holds `1`. -/
def bitSum (M : Mem) (bt : Nat) (st J : List Nat) (n : Nat) : Nat :=
  ((List.range n).map fun y => if M.k (bt + y + dot st J) = 1 then 2 ^ y else 0).sum

theorem bitSum_succ (M : Mem) (bt : Nat) (st J : List Nat) (n : Nat) :
    bitSum M bt st J (n + 1) = bitSum M bt st J n + (if M.k (bt + n + dot st J) = 1 then 2 ^ n else 0) := by
  simp [bitSum, List.range_succ]

theorem bitSum_lt (M : Mem) (bt : Nat) (st J : List Nat) : ∀ n, bitSum M bt st J n < 2 ^ n
  | 0 => by simp [bitSum]
  | n + 1 => by
    rw [bitSum_succ, Nat.pow_succ]; have := bitSum_lt M bt st J n
    split <;> omega

theorem getD_app3 {l₁ l₂ l₃ : List LRow} {i : Nat} :
    (l₁ ++ l₂ ++ l₃).getD (l₁.length + l₂.length + i) default = l₃.getD i default := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
    show l₁.length + l₂.length + i - l₁.length = l₂.length + i by omega,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem getD_app2 {l₁ l₂ l₃ : List LRow} {i : Nat} (hi : i < l₂.length) :
    (l₁ ++ l₂ ++ l₃).getD (l₁.length + i) default = l₂.getD i default := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hi]

theorem capTpl_chain (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) {i : Nat} (hi : i < 2 * (c - 1)) :
    (capTpl lenL row A lo rlo m s bt sb c z sz).getD (3 + i) default = (capChain bt sb c).getD i default := by
  simp only [capTpl]
  exact getD_app2 (l₁ := [_, _, _]) (by rw [capChain_length]; exact hi)

/-- **A cap check**: with the gate `1`, Boolean cap bits and `GInj`, the leaf's length lane is the row
length and the four answer lanes are the cap node's lanes `lo + 4 · idx + l`, `idx` the bits' number. -/
theorem capLoop_spec {cx : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {lenL row A lo rlo m bt c z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold cx M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2)
    (hA : SegsAssert M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hc : 1 ≤ c) (hz : M.k (z + dot sz (unflat dims jf)) = 1)
    (hb : ∀ y < c, M.k (bt + y + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + y + dot sb (unflat dims jf)) = 1)
    {N : Nat} (hinj : GInj N) (hN : cx.cells .K ≤ N) (hlo : lo + 4 * 2 ^ c ≤ N) :
    M.k (lenL + dot s (unflat dims jf)) = kOf row ∧ ∀ l < 4, M.k (A + l + dot s (unflat dims jf)) =
      M.k (lo + 4 * bitSum M bt sb (unflat dims jf) c + l) := by
  simp only [capLoop, hold_bind, assert_bind] at h hA
  have hlen : (capTpl lenL row A lo rlo m s bt sb c z sz).length = 2 * c + 16 := by
    simp [capTpl, capChain_length]; omega
  have hR := fun t (ht : t < 2 * c + 16) => loop_rel h.1 hjf (t := t) (by rw [hlen]; exact ht)
  have hS := fun t (ht : t < 2 * c + 16) => loop_assert hA.1 hjf (t := t) (by rw [hlen]; exact ht)
  generalize hJ : unflat dims jf = J at *
  have vK : ∀ (b : Nat) (st : List Nat),
      (Opd.abs ⟨.K, b, st⟩).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
        FE.ofK (M.k (b + dot st J)) := fun b st => by rw [Opd.val_absK]; show _ = FE.ofK (M.k (b + dot st J)); rw [← hJ]; rfl
  have vc : ∀ t, (Opd.cur t).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
      ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell t jf).val M := fun t => Opd.val_cur _ _ hjf t
  have hzero : ∀ t, t + 1 < 2 * c + 16 →
      (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (t + 1) default =
        ⟨.assert0, .K, [.cur t, .abs ⟨.K, z, sz⟩]⟩ →
      ∀ X : FK, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell t jf).val M = FE.ofK X → X = 0 := by
    intro t ht hr X hX
    have := lassert_of hr (hS (t + 1) ht)
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, hX] at this
    exact gate_one this hz
  refine ⟨?_, ?_⟩
  · have h0 := lrel_lin (t := 0) rfl (hR 0 (by omega))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, ofK_zero, zero_mul, add_zero] at h0
    rw [← ofK_add] at h0
    exact char2_eq (hzero 0 (by omega) rfl _ h0)
  · -- the rows past the chain
    have hpost : ∀ i, (capTpl lenL row A lo rlo m s bt sb c z sz).getD (2 * c + 1 + i) default =
        ([⟨.lin (gpow 1 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
         ⟨.lin (gpow 3 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
         ⟨.readd rlo m, .K, [.cur (2 * c)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 1)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 2)]⟩,
         ⟨.readd rlo m, .K, [.cur (2 * c + 3)]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 4), .abs ⟨.K, A, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 8), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 5), .abs ⟨.K, A + 1, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 10), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 6), .abs ⟨.K, A + 2, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 12), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 7), .abs ⟨.K, A + 3, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 14), .abs ⟨.K, z, sz⟩]⟩] :
          List LRow).getD i default := by
      intro i
      have e : 2 * c + 1 + i = [(default : LRow), default, default].length + (capChain bt sb c).length + i := by
        simp [capChain_length]; omega
      rw [e]; exact getD_app3
    -- the address chain
    have chain : ∀ y < c, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * y + 2) jf).val M =
        FE.ofK (gpow (lo + 4 * bitSum M bt sb J (y + 1))) := by
      intro y
      induction y with
      | zero =>
        intro _
        have h2 := lrel_lin (t := 2) rfl (hR 2 (by omega))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vK] at h2
        rw [h2, ← ofK_mul, ← ofK_add, ← ofK_add]
        congr 1
        rw [bitSum_succ, show bitSum M bt sb J 0 = 0 from rfl, Nat.zero_add, Nat.add_zero]
        rcases hb 0 hc with h0 | h1
        · simp only [Nat.add_zero] at h0; rw [h0]; simp [show (0 : FK) ≠ 1 from by decide, gpow]
        · simp only [Nat.add_zero] at h1
          rw [h1, if_pos rfl, mul_one]
          have e : (1 : FK) + (gpow lo * (gpow 4 + 1) + 1) + gpow lo =
              gpow lo * gpow 4 + ((1 + 1) + (gpow lo + gpow lo)) := by ring
          rw [e, FK.add_self, FK.add_self, add_zero, add_zero, ← gpow_add]
          simp
      | succ y ih =>
        intro hy
        have ihv := ih (by omega)
        obtain ⟨k1, k2⟩ := capChain_getD bt sb c y hy
        have r1 := capTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y) (by omega)
        have r2 := capTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y + 1) (by omega)
        rw [k1] at r1; rw [k2] at r2
        rw [show 3 + 2 * y = 2 * y + 3 by omega] at r1
        rw [show 3 + (2 * y + 1) = 2 * (y + 1) + 2 by omega] at r2
        have e1 := lrel_lin r1 (hR _ (by omega))
        have e2 := lrel_muladd r2 (hR _ (by omega))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, ofK_zero, add_zero] at e1 e2
        rw [show 2 * (y + 1) = 2 * y + 2 by ring] at e1 e2
        rw [show 2 * y + 2 + 1 = 2 * y + 3 by ring] at e2
        rw [show 2 * (y + 1) + 2 = 2 * y + 2 + 2 by ring, e2, e1, ihv]
        simp only [← ofK_mul, ← ofK_add]
        congr 1
        have hsel := bit_select (gpow (lo + 4 * bitSum M bt sb J (y + 1))) (gpow (4 * 2 ^ (y + 1)))
          (M.k (bt + (y + 1) + dot sb J)) (hb (y + 1) hy)
        rw [add_zero] at hsel
        rw [hsel, bitSum_succ (n := y + 1)]
        split_ifs with hβ
        · rw [← gpow_add]; congr 1; ring
        · simp
    have hα0 := chain (c - 1) (by omega)
    rw [show 2 * (c - 1) + 2 = 2 * c by omega, show c - 1 + 1 = c by omega] at hα0
    have hidx := bitSum_lt M bt sb J c
    generalize bitSum M bt sb J c = idx at hα0 hidx ⊢
    have hfour : lo + 4 * idx + 4 ≤ N := by
      have : 4 * idx + 4 ≤ 4 * 2 ^ c := by omega
      omega
    -- g^l·α
    have sc : ∀ i < 3, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M = FE.ofK (gpow (lo + 4 * idx + (i + 1))) := by
      intro i hi
      have key : ∀ l, (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 1 + i) default = ⟨.lin (gpow l + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩ →
          l = i + 1 → ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M = FE.ofK (gpow (lo + 4 * idx + (i + 1))) := by
        intro l hr hl
        have e := lrel_lin hr (hR _ (by omega))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vc, hα0, ofK_zero, add_zero] at e
        rw [e, ← ofK_mul, ← ofK_add, ← hl, ← gpow_scale l, add_zero]
      interval_cases i
      · exact key 1 (hpost 0) rfl
      · exact key 2 (hpost 1) rfl
      · exact key 3 (hpost 2) rfl
    have vcur : ∀ i < 4, (Opd.cur (2 * c + i)).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf = FE.ofK (gpow (lo + 4 * idx + i)) := by
      intro i hi
      rw [vc]
      rcases i with _ | i
      · simpa using hα0
      · have := sc i (by omega); rw [show 2 * c + (i + 1) = 2 * c + 1 + i by omega, this]
    -- the reads
    have rd : ∀ i < 4, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 4 + i) jf).val M = FE.ofK (M.k (lo + 4 * idx + i)) := by
      intro i hi
      have hr : (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 4 + i) default = ⟨.readd rlo m, .K, [.cur (2 * c + i)]⟩ := by
        rw [show 2 * c + 4 + i = 2 * c + 1 + (3 + i) by omega]
        interval_cases i
        · exact hpost 3
        · exact hpost 4
        · exact hpost 5
        · exact hpost 6
      exact lreadd_spec hr (hR _ (by omega)) hinj hN (by omega)
        (by rw [List.getD_cons_zero, vcur i hi]; rfl)
    intro l hl
    have hr1 : (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 8 + 2 * l) default = ⟨.lin 1 0, .K, [.cur (2 * c + 4 + l), .abs ⟨.K, A + l, s⟩]⟩ := by
      rw [show 2 * c + 8 + 2 * l = 2 * c + 1 + (7 + 2 * l) by omega]
      interval_cases l
      · exact hpost 7
      · exact hpost 9
      · exact hpost 11
      · exact hpost 13
    have hr2 : (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 8 + 2 * l + 1) default = ⟨.assert0, .K, [.cur (2 * c + 8 + 2 * l), .abs ⟨.K, z, sz⟩]⟩ := by
      rw [show 2 * c + 8 + 2 * l + 1 = 2 * c + 1 + (8 + 2 * l) by omega]
      interval_cases l
      · exact hpost 8
      · exact hpost 10
      · exact hpost 12
      · exact hpost 14
    have e := lrel_lin hr1 (hR _ (by omega))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vc, vK, rd l hl, ofK_one, one_mul, ofK_zero, add_zero] at e
    rw [← ofK_add] at e
    exact (char2_eq (hzero _ (by omega) hr2 _ e)).symm

end Lvm.Loop.Build
