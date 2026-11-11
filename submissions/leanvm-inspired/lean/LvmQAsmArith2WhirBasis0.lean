-- New for lvm (HAR-WH): the claim batching of a stacked opening, part 1: pointer-free gadget specs
-- (`Hs`), the binary trie over static selector keys (`trieG`), memoised `eq` chains (`chainG`), the
-- batched target (`targetG`), `F`'s `dot (powers s n)` as a running sum (`bsum`).
import LvmQAsmArith2WhirG

/-!
# Claim batching, part 1: trie, chains, target

* **`Hs c M m P`**: wherever the gadget `m` is placed, if its rows hold its output satisfies `P`
  (`hs_bind`, `hs_pure`, `hs_mono`, `hs_mulAdd`, `hs_lin`): the specs below need no pointer.
* **Terms** `TC = (scale cell, key, leaf cell)`, value `scale · Π_j f(key_j, x_{n−1−j}) · leaf`
  (`tval`, `kprod`), `f(0, y) = 1 + y`, `f(1, y) = y` (`fb`): a key fixes the top coordinates of the
  point bit by bit. **`trieG xb z n ts`**: `Σ_t tval t` by a binary trie over the keys from the top
  coordinate `n − 1` (coordinate `i` in the `E` cell `xb + i`): a node is
  `Σ_here scale·leaf + (1 + x) V₀ + x V₁` (two rows; one row with one child; none when empty).
  Rows: one per term, one per one-child node, two per two-child node. `trieG_spec`.
* **`chainG`**: `Π_{i<n} (1 + z_i + x_i)` for a cell list `z`, memoised by prefix (a hit costs
  nothing, a new prefix two rows; invariant `MemoOk`). `chainG_spec`.
* **`targetG`**: `Σ_i s^i v_i`, one `mulAdd` per claim. `targetG_spec`; `dot_powers_bsum`:
  `F`'s `dot (powers s |w|) w` is `bsum s 0 w`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Pointer-free specs -/

/-- Wherever `m` is placed, if its rows hold, its output satisfies `P`. -/
def Hs (c : Ctx) (M : Mem) {α : Type} (m : BM α) (P : α → Prop) : Prop :=
  ∀ p : Ptr, SegsHold c M p (m p).2 → P (m p).1

variable {c : Ctx} {M : Mem}

theorem hs_bind {α β : Type} {m : BM α} {f : α → BM β} {P : α → Prop} {Q : β → Prop}
    (hm : Hs c M m P) (hf : ∀ a, P a → Hs c M (f a) Q) : Hs c M (m >>= f) Q := by
  intro p h
  rw [hold_bind] at h
  exact hf _ (hm p h.1) _ h.2

theorem hs_pure {α : Type} {a : α} {P : α → Prop} (h : P a) : Hs c M (pure a) P := fun _ _ => h

theorem hs_mono {α : Type} {m : BM α} {P Q : α → Prop} (h : Hs c M m P) (hPQ : ∀ a, P a → Q a) :
    Hs c M m Q := fun p hp => hPQ _ (h p hp)

theorem hs_mulAdd (τ : Ty) (a b d : Cell) :
    Hs c M (mulAdd τ a b d) (fun r => r.val M = a.val M * b.val M + d.val M) := fun _ h => mulAdd_spec h

theorem hs_lin (τ : Ty) (k k' : FK) (a b : Cell) :
    Hs c M (lin τ k k' a b) (fun r => r.val M = a.val M + FE.ofK k * b.val M + FE.ofK k') :=
  fun _ h => lin_spec h

/-! ## Terms and the trie -/

/-- A term: scale cell, key (top coordinate first), leaf cell. -/
structure TC where
  /-- The scale. -/
  sc : Cell
  /-- The fixed top coordinates' bits, the top one first. -/
  key : List Bool
  /-- The leaf (the weight over the coordinates below the key). -/
  lf : Cell

/-- The factor of a fixed coordinate: `y` for bit 1, `1 + y` for bit 0. -/
def fb (b : Bool) (y : FE) : FE := if b then y else 1 + y

/-- The product of a key's factors, the first bit at coordinate `n − 1`. -/
def kprod (X : Nat → FE) : Nat → List Bool → FE
  | _, [] => 1
  | 0, _ :: _ => 1
  | n + 1, b :: bs => fb b (X n) * kprod X n bs

/-- A term's value below coordinate `n`. -/
def tval (M : Mem) (X : Nat → FE) (n : Nat) (t : TC) : FE := t.sc.val M * kprod X n t.key * t.lf.val M

/-- The terms whose key ends here. -/
def here (ts : List TC) : List TC := ts.filter fun t => t.key.isEmpty

/-- The terms whose key continues with bit `b`, the bit removed. -/
def sub (b : Bool) (ts : List TC) : List TC := ts.filterMap fun t => match t.key with
  | b' :: r => if b' = b then some ⟨t.sc, r, t.lf⟩ else none
  | [] => none

/-- `w + Σ_t scale·leaf`, one row per term. -/
def hereG : Cell → List TC → BM Cell
  | w, [] => pure w
  | w, t :: ts => do
    let w' ← mulAdd .E t.sc t.lf w
    hereG w' ts

/-- A trie node: `(1 + x) V₀ + x V₁` from the children (`b₀`/`b₁`: the child is empty). -/
def node (xc z : Cell) : Bool → Bool → BM Cell → BM Cell → BM Cell
  | true, true, _, _ => pure z
  | false, true, m0, _ => do
    let v ← m0
    mulAdd .E xc v v
  | true, false, _, m1 => do
    let v ← m1
    mulAdd .E xc v z
  | false, false, m0, m1 => do
    let v0 ← m0
    let v1 ← m1
    let u ← add v0 v1
    mulAdd .E xc u v0

/-- **The trie** of the terms below coordinate `n` (coordinate `i` in the `E` cell `xb + i`). -/
def trieG (xb : Nat) (z : Cell) : Nat → List TC → BM Cell
  | 0, ts => hereG z ts
  | n + 1, ts => do
    let w ← node (ec (xb + n)) z (sub false ts).isEmpty (sub true ts).isEmpty
      (trieG xb z n (sub false ts)) (trieG xb z n (sub true ts))
    hereG w (here ts)

theorem hereG_spec : ∀ (ts : List TC) (w : Cell), Hs c M (hereG w ts)
    (fun r => r.val M = w.val M + (ts.map fun t => t.sc.val M * t.lf.val M).sum)
  | [], w => hs_pure (by simp)
  | t :: ts, w => by
    show Hs c M (mulAdd .E t.sc t.lf w >>= fun w' => hereG w' ts) _
    refine hs_bind (hs_mulAdd _ _ _ _) fun w' hw' => hs_mono (hereG_spec ts w') fun r hr => ?_
    rw [hr, hw', List.map_cons, List.sum_cons]
    ring

theorem node_spec {xc z : Cell} (hz : z.val M = 0) {b0 b1 : Bool} {m0 m1 : BM Cell} {A0 A1 : FE}
    (h0 : Hs c M m0 (fun v => v.val M = A0)) (h1 : Hs c M m1 (fun v => v.val M = A1))
    (e0 : b0 = true → A0 = 0) (e1 : b1 = true → A1 = 0) :
    Hs c M (node xc z b0 b1 m0 m1) (fun w => w.val M = (1 + xc.val M) * A0 + xc.val M * A1) := by
  cases b0 <;> cases b1
  · refine hs_bind h0 fun v hv => hs_bind h1 fun v1 hv1 => hs_bind (hs_lin _ _ _ _ _) fun u hu =>
      hs_mono (hs_mulAdd _ _ _ _) fun w hw => ?_
    rw [hw, hu, hv, hv1, ofK_one, ofK_zero]
    ring
  · refine hs_bind h0 fun v hv => hs_mono (hs_mulAdd _ _ _ _) fun w hw => ?_
    rw [hw, hv, e1 rfl]
    ring
  · refine hs_bind h1 fun v hv => hs_mono (hs_mulAdd _ _ _ _) fun w hw => ?_
    rw [hw, hv, hz, e0 rfl]
    ring
  · exact hs_pure (by rw [hz, e0 rfl, e1 rfl]; ring)

theorem here_nil (sc lf : Cell) (ts : List TC) : here (⟨sc, [], lf⟩ :: ts) = ⟨sc, [], lf⟩ :: here ts := rfl
theorem here_cons (sc lf : Cell) (b : Bool) (r : List Bool) (ts : List TC) :
    here (⟨sc, b :: r, lf⟩ :: ts) = here ts := rfl
theorem sub_nil (b : Bool) (sc lf : Cell) (ts : List TC) : sub b (⟨sc, [], lf⟩ :: ts) = sub b ts := rfl
theorem sub_same (b : Bool) (sc lf : Cell) (r : List Bool) (ts : List TC) :
    sub b (⟨sc, b :: r, lf⟩ :: ts) = ⟨sc, r, lf⟩ :: sub b ts := by cases b <;> rfl
theorem sub_ft (sc lf : Cell) (r : List Bool) (ts : List TC) :
    sub true (⟨sc, false :: r, lf⟩ :: ts) = sub true ts := rfl
theorem sub_tf (sc lf : Cell) (r : List Bool) (ts : List TC) :
    sub false (⟨sc, true :: r, lf⟩ :: ts) = sub false ts := rfl

theorem sum_split (X : Nat → FE) (n : Nat) : ∀ ts : List TC,
    (ts.map (tval M X (n + 1))).sum = ((here ts).map fun t => t.sc.val M * t.lf.val M).sum +
      (1 + X n) * ((sub false ts).map (tval M X n)).sum + X n * ((sub true ts).map (tval M X n)).sum
  | [] => by simp [here, sub]
  | ⟨sc, key, lf⟩ :: ts => by
    have ih := sum_split X n ts
    rcases key with _ | ⟨b, r⟩
    · rw [here_nil, sub_nil, sub_nil, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
      simp only [tval, kprod]
      ring
    · cases b
      · rw [here_cons, sub_same, sub_ft, List.map_cons, List.map_cons,
          List.sum_cons, List.sum_cons, ih]
        simp only [tval, kprod, fb, Bool.false_eq_true, if_false]
        ring
      · rw [here_cons, sub_same, sub_tf, List.map_cons, List.map_cons,
          List.sum_cons, List.sum_cons, ih]
        simp only [tval, kprod, fb, if_true]
        ring

theorem sum_nil_of_isEmpty {ts : List TC} {g : TC → FE} (h : ts.isEmpty = true) : (ts.map g).sum = 0 := by
  rw [List.isEmpty_iff] at h; subst h; rfl

/-- **The trie**: its cell is `Σ_t tval t` (coordinate `i` in the `E` cell `xb + i`). -/
theorem trieG_spec {xb : Nat} {z : Cell} (hz : z.val M = 0) : ∀ (n : Nat) (ts : List TC),
    Hs c M (trieG xb z n ts) (fun r => r.val M = (ts.map (tval M (fun i => M.e (xb + i)) n)).sum)
  | 0, ts => by
    refine hs_mono (hereG_spec ts z) fun r hr => ?_
    rw [hr, hz, zero_add]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    rcases t with ⟨sc, key, lf⟩
    rcases key with _ | ⟨b, r⟩ <;> simp only [tval, kprod, mul_one]
  | n + 1, ts => by
    show Hs c M (node (ec (xb + n)) z (sub false ts).isEmpty (sub true ts).isEmpty
      (trieG xb z n (sub false ts)) (trieG xb z n (sub true ts)) >>= fun w => hereG w (here ts)) _
    refine hs_bind (node_spec hz (trieG_spec hz n _) (trieG_spec hz n _) sum_nil_of_isEmpty sum_nil_of_isEmpty)
      fun w hw => hs_mono (hereG_spec _ w) fun r hr => ?_
    rw [hr, hw, sum_split]
    simp only [Cell.val_E]
    ring

/-! ## Memoised `eq` chains -/

/-- The memo: prefixes and their chain cells. -/
abbrev Memo := List (List Cell × Cell)

/-- `Π_{i<n} (1 + z_i + x_i)`. -/
def cv (M : Mem) (X : Nat → FE) (l : List Cell) (n : Nat) : FE :=
  ∏ i ∈ Finset.range n, (1 + (l.getD i default).val M + X i)

/-- Every memo entry holds its prefix's chain. -/
def MemoOk (M : Mem) (X : Nat → FE) (memo : Memo) : Prop := ∀ e ∈ memo, e.2.val M = cv M X e.1 e.1.length

/-- **The chain of the first `n` cells of `zl`**, from the memo or extended from the chain of
the first `n − 1` (`o` holds `1`, `z` holds `0`). -/
def chainG (xb : Nat) (z o : Cell) (zl : List Cell) : Nat → Memo → BM (Memo × Cell)
  | 0, memo => pure (memo, o)
  | n + 1, memo =>
    match memo.find? (fun e => e.1 == zl.take (n + 1)) with
    | some e => pure (memo, e.2)
    | none => do
      let r ← chainG xb z o zl n memo
      let f ← lin .E 1 1 (zl.getD n default) (ec (xb + n))
      let c' ← mulAdd .E r.2 f z
      pure ((zl.take (n + 1), c') :: r.1, c')

theorem cv_take (X : Nat → FE) (l : List Cell) {m n : Nat} (h : n ≤ m) :
    cv M X (l.take m) n = cv M X l n := by
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < m := lt_of_lt_of_le (Finset.mem_range.mp hi) h
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi']

theorem chainG_spec {xb : Nat} {z o : Cell} {zl : List Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (n : Nat) (memo : Memo), n ≤ zl.length → MemoOk M (fun i => M.e (xb + i)) memo →
      Hs c M (chainG xb z o zl n memo)
        (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧ r.2.val M = cv M (fun i => M.e (xb + i)) zl n)
  | 0, memo, _, hm => hs_pure ⟨hm, by simp [cv, ho]⟩
  | n + 1, memo, hn, hm => by
    have hlen : (zl.take (n + 1)).length = n + 1 := by simp; omega
    rw [chainG]
    split
    · next e he =>
      refine hs_pure ⟨hm, ?_⟩
      have he1 : e.1 = zl.take (n + 1) := by simpa using List.find?_some he
      rw [hm e (List.mem_of_find?_eq_some he), he1, hlen, cv_take _ _ le_rfl]
    · refine hs_bind (chainG_spec hz ho n memo (by omega) hm) fun r ⟨hm', hv⟩ =>
        hs_bind (hs_lin _ _ _ _ _) fun f hf => hs_bind (hs_mulAdd _ _ _ _) fun c' hc' => hs_pure ⟨?_, ?_⟩
      · have hval : c'.val M = cv M (fun i => M.e (xb + i)) zl (n + 1) := by
          rw [hc', hf, hv, hz, cv, cv, Finset.prod_range_succ, ofK_one]
          simp only [Cell.val_E]
          ring
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rw [hlen, cv_take _ _ le_rfl, hval]
        · exact hm' e he
      · rw [hc', hf, hv, hz, cv, cv, Finset.prod_range_succ, ofK_one]
        simp only [Cell.val_E]
        ring

/-! ## The batched target -/

/-- `Σ_j s^(i+j) w_j`. -/
def bsum (s : FE) : Nat → List FE → FE
  | _, [] => 0
  | i, w :: ws => s ^ i * w + bsum s (i + 1) ws

theorem zip_powersFrom (s : FE) : ∀ (ws : List FE) (i : Nat) (a : FE),
    (List.zipWith (· * ·) (powersFrom (s ^ i) s ws.length) ws).foldl (· + ·) a = a + bsum s i ws
  | [], _, a => by simp [bsum, powersFrom]
  | w :: ws, i, a => by
    simp only [List.length_cons, powersFrom, List.zipWith_cons_cons, List.foldl_cons, bsum]
    rw [← pow_succ, zip_powersFrom s ws (i + 1)]
    ring

/-- **`F`'s batched sum**: `dot (powers s |w|) w = Σ_j s^j w_j`. -/
theorem dot_powers_bsum (s : FE) (ws : List FE) : Lvm.dot (powers s ws.length) ws = bsum s 0 ws := by
  have := zip_powersFrom s ws 0 0
  rw [pow_zero, zero_add] at this
  exact this

/-- The claim's value is its value cell's. -/
theorem cval_value (cc : CClaim) : (cc.val M).2.value = cc.value.val M := by
  rcases cc with ⟨com, cw, v⟩
  cases cw <;> rfl

/-- `acc + Σ_j s^(i+j) v_j` over the claims' value cells (`sp + i + j` holds `s^(i+j)`). -/
def targetGo (sp : Nat) : Nat → List CClaim → Cell → BM Cell
  | _, [], acc => pure acc
  | i, cc :: cl, acc => do
    let a ← mulAdd .E (ec (sp + i)) cc.value acc
    targetGo sp (i + 1) cl a

/-- `Σ_i s^i v_i` over the claims' value cells (`sp + i` holds `s^i`). -/
def targetG (cl : List CClaim) (sp : Nat) (z : Cell) : BM Cell := targetGo sp 0 cl z

theorem targetGo_spec {sp N : Nat} {s : FE} (hs : ∀ i < N, M.e (sp + i) = s ^ i) :
    ∀ (cl : List CClaim) (i : Nat) (acc : Cell), i + cl.length ≤ N →
      Hs c M (targetGo sp i cl acc)
        (fun r => r.val M = acc.val M + bsum s i (cl.map fun cc => cc.value.val M))
  | [], _, acc, _ => hs_pure (by simp [bsum])
  | cc :: cl, i, acc, hN => by
    simp only [List.length_cons] at hN
    show Hs c M (mulAdd .E (ec (sp + i)) cc.value acc >>= fun a => targetGo sp (i + 1) cl a) _
    refine hs_bind (hs_mulAdd _ _ _ _) fun a ha =>
      hs_mono (targetGo_spec hs cl (i + 1) a (by omega)) fun r hr => ?_
    rw [hr, ha, List.map_cons, bsum, Cell.val_E, hs i (by omega)]
    ring

theorem targetG_spec {cl : List CClaim} {sp : Nat} {z : Cell} {p : Ptr} (h : SegsHold c M p (targetG cl sp z p).2)
    (hz : z.val M = 0) (s : FE) (hs : ∀ i < cl.length, M.e (sp + i) = s ^ i) :
    (targetG cl sp z p).1.val M = Lvm.dot (powers s cl.length) (cl.map fun cc => (cc.val M).2.value) := by
  have e := targetGo_spec (c := c) hs cl 0 z (by omega) p h
  rw [show (targetG cl sp z p).1 = (targetGo sp 0 cl z p).1 from rfl, e, hz, zero_add]
  have hl : cl.length = (cl.map fun cc => (cc.val M).2.value).length := by simp
  rw [hl, dot_powers_bsum]
  exact congrArg (bsum s 0) (List.map_congr_left fun cc _ => (cval_value cc).symm)

end Lvm.Har
