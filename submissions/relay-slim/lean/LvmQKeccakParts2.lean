import LvmQKeccakParts

/-!
# QA1: the Keccak layer's weight gadgets (structured forms of `LvmQKeccakSpec`)

* `gLowTab`, `gHighTab`, `gShift`: `lowTab`, `highTab`, `shiftLH` from `eq` tables of the two
  six-coordinate points (split three and three);
* `gLaneForm`, `gFlip`: `laneForm` and `flipForm`;
* `gKForm`: `kForm` (the final check's weight, the guest's `keccak_form`);
* `gLaneW`: `F`'s next lane weights `eq_L(ℓ) + β(eq_L(x+4) + β eq_L(x+3))` (`laneWF`);
* `gIndex`: `indexMle` (`Π (1 + r_t (1 + g^{2^t}))`, constants in `K`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- A list of sources as values. -/
abbrev vals (xv : Src → FE) (V : Nat → FE) (l : List Src) : List FE := l.map (Src.valF xv V)

theorem getD_vals {xv : Src → FE} {V : Nat → FE} (l : List Src) {i : Nat} (hi : i < l.length) :
    (l.getD i default).valF xv V = (vals xv V l).getD i 0 := getD_valF l hi

/-! ## The shift tables -/

/-- `L_c(r_l)` from the `eq` tables `ta` (of `a_lo`) and `tb` (of `b_lo`). -/
def gLowTab (z : Src) (ta tb : List Src) (c rl : Nat) : TB Src :=
  gSumMap z 8 fun zz => if (zz + rl) / 8 = c then gMul (tb.getD zz default) (ta.getD ((zz + rl) % 8) default) z
    else pure z

/-- `H(k)` from the `eq` tables of `a_hi`, `b_hi`. -/
def gHighTab (z : Src) (ta tb : List Src) (k : Nat) : TB Src :=
  gSumMap z 8 fun zz => gMul (tb.getD zz default) (ta.getD ((zz + k) % 8) default) z

theorem eqKernel_len (pt : List FE) : (eqKernel pt).length = 2 ^ pt.length := by
  unfold eqKernel
  suffices h : ∀ (l : List FE) (acc : List FE), (l.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) acc).length =
      acc.length * 2 ^ l.length by simpa using h pt [1]
  intro l
  induction l with
  | nil => simp
  | cons r rs ih => intro acc; rw [List.foldl_cons, ih]; simp [pow_succ]; ring

theorem gLowTab_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {ta tb : List Src}
    {a b : List FE} (hta : vals xv V ta = eqKernel (a.take 3)) (htb : vals xv V tb = eqKernel (b.take 3))
    (ha : 3 ≤ a.length) (hb : 3 ≤ b.length) (c rl : Nat) (n : Nat) (h : THold xv V n (gLowTab z ta tb c rl n).2) :
    (gLowTab z ta tb c rl n).1.valF xv V = lowTab a b c rl := by
  have la : ta.length = 8 := by
    have := congrArg List.length hta; rw [List.length_map, eqKernel_len] at this; simp [this, ha]
  have lb : tb.length = 8 := by
    have := congrArg List.length htb; rw [List.length_map, eqKernel_len] at this; simp [this, hb]
  rw [lowTab, sumE_eq_sum]
  refine gSumMap_spec' hz (fun zz hzz m hm => ?_) n h
  by_cases hc : (zz + rl) / 8 = c
  · simp only [hc, if_true] at hm ⊢
    rw [gMul_spec hm, hz, add_zero, getD_vals _ (by omega), getD_vals _ (by rw [la]; exact Nat.mod_lt _ (by omega)),
      hta, htb]
    rfl
  · simp only [hc, if_false] at hm ⊢
    exact hz

theorem gHighTab_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {ta tb : List Src}
    {a b : List FE} (hta : vals xv V ta = eqKernel (a.drop 3)) (htb : vals xv V tb = eqKernel (b.drop 3))
    (ha : a.length = 6) (hb : b.length = 6) (k : Nat) (n : Nat) (h : THold xv V n (gHighTab z ta tb k n).2) :
    (gHighTab z ta tb k n).1.valF xv V = highTab a b k := by
  have la : ta.length = 8 := by
    have := congrArg List.length hta; rw [List.length_map, eqKernel_len] at this; simp [this, ha]
  have lb : tb.length = 8 := by
    have := congrArg List.length htb; rw [List.length_map, eqKernel_len] at this; simp [this, hb]
  rw [highTab, sumE_eq_sum]
  refine gSumMap_spec' hz (fun zz hzz m hm => ?_) n h
  rw [gMul_spec hm, hz, add_zero, getD_vals _ (by omega), getD_vals _ (by rw [la]; exact Nat.mod_lt _ (by omega)),
    hta, htb]
  rfl

/-- `shift(r) = L₀·H + L₁·H'` from the three tables. -/
def gShift (z : Src) (L0 L1 H : List Src) (r : Nat) : TB Src :=
  gMul (L1.getD (r % 8) default) (H.getD ((r / 8 + 1) % 8) default) z >>= fun t =>
    gMul (L0.getD (r % 8) default) (H.getD (r / 8) default) t

theorem gShift_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {L0 L1 H : List Src}
    {a b : List FE} (h0 : vals xv V L0 = (List.range 8).map (lowTab a b 0))
    (h1 : vals xv V L1 = (List.range 8).map (lowTab a b 1)) (hH : vals xv V H = (List.range 8).map (highTab a b))
    {r : Nat} (hr : r < 64) (n : Nat) (h : THold xv V n (gShift z L0 L1 H r n).2) :
    (gShift z L0 L1 H r n).1.valF xv V = shiftLH a b r := by
  have l0 : L0.length = 8 := by simpa using congrArg List.length h0
  have l1 : L1.length = 8 := by simpa using congrArg List.length h1
  have lH : H.length = 8 := by simpa using congrArg List.length hH
  obtain ⟨g1, g2⟩ := (thold_bind _ _).mp h
  rw [gShift, tb_bind, gMul_spec g2, gMul_spec g1, hz, add_zero,
    getD_vals _ (by rw [l0]; exact Nat.mod_lt _ (by omega)), getD_vals _ (by rw [lH]; omega),
    getD_vals _ (by rw [l1]; exact Nat.mod_lt _ (by omega)), getD_vals _ (by rw [lH]; exact Nat.mod_lt _ (by omega)),
    h0, h1, hH]
  simp [List.getD_eq_getElem?_getD, Nat.mod_lt _ (show 0 < 8 by omega), show r / 8 < 8 by omega,
    Nat.mod_lt _ (show 0 < 8 by omega), shiftLH]

theorem kPi_lt : ∀ l < 25, keccakPi l < 25 := by decide

/-- `laneForm B R ℓ`: the lane, then the two columns. -/
def gLaneForm (z : Src) (B : List Src) (R : Nat → Src) (l : Nat) : TB Src :=
  gMul (B.getD (keccakPi l) default) (R (rho l)) z >>= fun t1 =>
  gDot t1 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 1) % 5 + 5 * y)) default, R (rho ((l % 5 + 1) % 5 + 5 * y)))) >>= fun t2 =>
  gDot t2 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 4) % 5 + 5 * y)) default, R ((rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64)))

theorem gLaneForm_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {B : List Src}
    (hB : 25 ≤ B.length) (R : Nat → Src) {l : Nat} (hl : l < 25) (n : Nat)
    (h : THold xv V n (gLaneForm z B R l n).2) :
    (gLaneForm z B R l n).1.valF xv V = laneForm (vals xv V B) (fun s => (R s).valF xv V) l := by
  obtain ⟨g1, h'⟩ := (thold_bind _ _).mp h
  obtain ⟨g2, g3⟩ := (thold_bind _ _).mp h'
  have hp : ∀ x y, x < 5 → y < 5 → keccakPi (x + 5 * y) < B.length := fun x y hx hy =>
    lt_of_lt_of_le (kPi_lt _ (by omega)) hB
  rw [gLaneForm, tb_bind, tb_bind, gDot_spec _ _ _ g3, gDot_spec _ _ _ g2, gMul_spec g1, hz, add_zero,
    laneForm, sumE_eq_sum, sumE_eq_sum, getD_vals _ (lt_of_lt_of_le (kPi_lt _ hl) hB)]
  simp only [List.map_map, Function.comp_def]
  congr 2
  · congr 1
    apply List.map_congr_left
    intro y hy
    rw [getD_vals _ (hp _ _ (Nat.mod_lt _ (by omega)) (List.mem_range.mp hy))]
  · apply List.map_congr_left
    intro y hy
    rw [getD_vals _ (hp _ _ (Nat.mod_lt _ (by omega)) (List.mem_range.mp hy))]

/-- `flip_i = flipForm B A i`, `A` given as an `eq` table of 64 sources. -/
def gFlip (z : Src) (B A : List Src) (i : Nat) : TB Src :=
  gLaneForm z B (fun s => A.getD ((iotaPos i + s) % 64) default) 0

theorem gFlip_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {B A : List Src}
    (hB : 25 ≤ B.length) (hA : A.length = 64) (i n : Nat) (h : THold xv V n (gFlip z B A i n).2) :
    (gFlip z B A i n).1.valF xv V = flipForm (vals xv V B) (fun s => (vals xv V A).getD s 0) i := by
  rw [gFlip, gLaneForm_spec hz hB _ (by omega) n h, flipForm]
  congr 1
  funext s
  rw [getD_vals _ (by rw [hA]; exact Nat.mod_lt _ (by omega))]

/-- `F`'s next lane weights from the `eq` table `eL` of the lane challenges. -/
def gLaneW (eL : List Src) (beta : Src) : TB (List Src) :=
  mapTB (fun l => gMul beta (eL.getD (keccakAlong (64 * l) 3 / 64) default)
    (eL.getD (keccakAlong (64 * l) 4 / 64) default) >>= fun u => gMul beta u (eL.getD l default)) (List.range 25)

theorem along_lt : ∀ l < 25, keccakAlong (64 * l) 3 / 64 < 25 ∧ keccakAlong (64 * l) 4 / 64 < 25 := by decide

theorem gLaneW_spec {xv : Src → FE} {V : Nat → FE} {eL : List Src} (hL : 25 ≤ eL.length) (beta : Src) (n : Nat)
    (h : THold xv V n (gLaneW eL beta n).2) :
    vals xv V (gLaneW eL beta n).1 = (List.range 25).map fun l => (vals xv V eL).getD l 0 + beta.valF xv V *
      ((vals xv V eL).getD (keccakAlong (64 * l) 4 / 64) 0 + beta.valF xv V *
        (vals xv V eL).getD (keccakAlong (64 * l) 3 / 64) 0) := by
  refine forall₂_map_eq (mapTB_spec_mem (P := fun l v => v = _) _ (fun l hl m hm => ?_) n h)
  have hl' := List.mem_range.mp hl
  obtain ⟨g1, g2⟩ := (thold_bind _ _).mp hm
  rw [tb_bind, gMul_spec g2, gMul_spec g1, getD_vals (i := l) eL (by omega),
    getD_vals (i := keccakAlong (64 * l) 3 / 64) eL (lt_of_lt_of_le (along_lt l hl').1 hL),
    getD_vals (i := keccakAlong (64 * l) 4 / 64) eL (lt_of_lt_of_le (along_lt l hl').2 hL)]
  ring

/-- One coordinate of `indexMle`: `acc·(1 + r·(1 + g^{2^k}))`, the constant in `K`. -/
def gIndexStep (z : Src) (k : Nat) (acc r : Src) : TB Src :=
  gScale (1 + FK.x ^ (2 ^ k)) r >>= fun u => gOne u >>= fun w => gMul acc w z

theorem gIndexStep_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) (k : Nat) (acc r : Src)
    (n : Nat) (h : THold xv V n (gIndexStep z k acc r n).2) :
    (gIndexStep z k acc r n).1.valF xv V = acc.valF xv V * (1 + r.valF xv V * (1 + gen ^ (2 ^ k))) := by
  obtain ⟨g1, h⟩ := (thold_bind _ _).mp h
  obtain ⟨g2, g3⟩ := (thold_bind _ _).mp h
  rw [gIndexStep, tb_bind, tb_bind, gMul_spec g3, gOne_spec g2, gScale_spec g1, hz, add_zero,
    show FE.ofK (1 + FK.x ^ 2 ^ k) = 1 + gen ^ 2 ^ k by
      show FE.ofKRingHom (1 + FK.x ^ 2 ^ k) = _
      rw [map_add, map_pow, map_one]; rfl]
  ring

/-- `indexMleFrom (g^{2^k})` over the coordinates `rs`. -/
def gIndex (z : Src) : Nat → Src → List Src → TB Src
  | _, acc, [] => pure acc
  | k, acc, r :: rs => gIndexStep z k acc r >>= fun acc' => gIndex z (k + 1) acc' rs

theorem gIndex_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) :
    ∀ (rs : List Src) (k : Nat) (acc : Src) (n : Nat), THold xv V n (gIndex z k acc rs n).2 →
      (gIndex z k acc rs n).1.valF xv V = indexMleFrom (gen ^ (2 ^ k)) (vals xv V rs) (acc.valF xv V)
  | [], k, acc, n, _ => rfl
  | r :: rs, k, acc, n, h => by
    obtain ⟨g1, g2⟩ := (thold_bind _ _).mp h
    have e1 := gIndexStep_spec hz k acc r n g1
    have e2 := gIndex_spec hz rs (k + 1) _ _ g2
    rw [e1] at e2
    have hp : (gen ^ (2 ^ k)) ^ 2 = gen ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]
    show (gIndex z (k + 1) (gIndexStep z k acc r n).1 rs (n + (gIndexStep z k acc r n).2.length)).1.valF xv V = _
    rw [e2]
    simp only [vals, List.map_cons, indexMleFrom, hp]

end Lvm.Q1
