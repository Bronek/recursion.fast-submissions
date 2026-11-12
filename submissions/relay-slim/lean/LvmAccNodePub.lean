-- New for lvm (AC-N, A23): the header's 702 `PUB` lanes read from the statement bytes
-- (`LvmNodeSoundIn.hdrLanes`) are AC-V's `Pub.hdrLanes` of the statement's public values (`pubX`),
-- the order of the `PUB` input array (QAsm's `hdrOfPub`); the incoming accumulator's lanes among them.
import LvmNodeSoundIn
import LvmVEqParse

/-!
# The `PUB` lanes are the public values' header lanes

* `hdrLane_eq_kAt`: lane `k` of the statement's header (from byte `8`) is V_S's `kAt` of the
  stream byte `headerAt 8 + 8k` (`sigOfX`);
* **`hdrLanes_eq_pubX`**: `hdrLanes x = (pubX x).hdrLanes` (all 702 lanes: `b`, `vk`, `c_L`, `s`,
  `n`, `h`, `σ_leaf`, then `acc_in`'s 29 scalars, three lanes each);
* **`accIn_pt_lanes`**, `accIn_y_lanes`: `acc_in`'s scalar `i` is header lanes `615 + 3i …` (the `PUB`
  cells); **`pubOf_accIn_pt`**, `pubOf_accIn_y`: a child's `acc_in'` as V_S reads it is the `E` scalar
  of stream lanes `626 + 3i …` (`feAt Σ (8q)`, Q_acc's `ldE_feAt` form).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.VEq

/-! ## Bytes -/

theorem get!_hdrBytesX (x : List UInt8) (t : ℕ) : (hdrBytesX x).get! (8 + t) = x.getD t 0 := by
  rw [hdrBytesX, get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

theorem get!_sigOfX_x (x : List UInt8) (t : ℕ) : (sigOfX x).get! (headerAt 8 + t) = x.getD t 0 := by
  rw [sigOfX, get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

theorem laneAt_shift {b b' : ByteArray} {o o' : ℕ} (h : ∀ i < 8, b.get! (o + i) = b'.get! (o' + i)) :
    laneAt b o = laneAt b' o' := by
  unfold laneAt
  simp only [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega)]

theorem kAt_sigOfX (x : List UInt8) (t : ℕ) :
    kAt (sigOfX x) (headerAt 8 + t) = ⟨laneAt (hdrBytesX x) (8 + t)⟩ := by
  unfold kAt
  rw [laneAt_shift (b' := hdrBytesX x) (o' := 8 + t) fun i _ ↦ by
    rw [Nat.add_assoc, get!_sigOfX_x, Nat.add_assoc, get!_hdrBytesX]]

theorem u64At_eq_laneAt (b : ByteArray) (o : ℕ) : u64At b o = (laneAt b o).toNat := rfl

/-- **Header lane `k`** is V_S's word at stream byte `headerAt 8 + 8k`. -/
theorem hdrLane_eq_kAt (x : List UInt8) (k : ℕ) : hdrLane x k = kAt (sigOfX x) (headerAt 8 + 8 * k) := by
  rw [kAt_sigOfX, hdrLane, u64At_eq_laneAt, UInt64.ofNat_toNat]

/-- A digest's four lanes, read at `o`, are the four words there. -/
theorem digestLanes_digestAt (b : ByteArray) (o : ℕ) :
    digestLanes (digestAt b o) = (List.range 4).map fun i ↦ kAt b (o + 8 * i) := by
  have e : ∀ i < 4, ∀ j < 8, ((digestAt b o).toArray.getD (8 * i + j) 0) = b.get! (o + 8 * i + j) := by
    intro i hi j hj
    rw [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray, Vector.getElem?_eq_getElem (by omega)]
    simp only [digestAt, Vector.getElem_ofFn, Option.getD_some]
    rw [Nat.add_assoc]
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  have e0 := e i hi' 0 (by omega)
  simp only [Nat.add_zero] at e0
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e i hi' 1 (by omega), e i hi' 2 (by omega), e i hi' 3 (by omega),
    e i hi' 4 (by omega), e i hi' 5 (by omega), e i hi' 6 (by omega), e i hi' 7 (by omega), kAt, laneAt,
    UInt64.zero_or, Nat.add_zero]

/-! ## The lanes -/

theorem map_range_add (f : ℕ → FK) (a b : ℕ) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map fun i ↦ f (a + i) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem lanes_feAt (b : ByteArray) (o : ℕ) :
    FE.lanes (feAt b o) = (List.range 3).map fun l ↦ kAt b (o + 8 * l) := by
  simp [FE.lanes, feAt, List.range_succ]

theorem flatMap_lanes (b : ByteArray) (o : ℕ) :
    ∀ n, ((List.range n).map fun i ↦ feAt b (o + 24 * i)).flatMap FE.lanes =
      (List.range (3 * n)).map fun j ↦ kAt b (o + 8 * j)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_lanes b o n,
      show 3 * (n + 1) = 3 * n + 3 by ring, map_range_add, List.map_singleton, List.flatMap_singleton,
      lanes_feAt]
    exact congrArg₂ (· ++ ·) rfl (List.map_congr_left fun l _ ↦ congrArg (kAt b) (by ring))

/-- `n` header words from header byte `o = 8 + 8a` are header lanes `a, …, a + n − 1`. -/
theorem seg (sig : ByteArray) (o a n : ℕ) (ho : o = 8 + 8 * a) :
    (List.range n).map (fun i ↦ kAt sig (headerAt o + 8 * i)) =
      (List.range n).map fun i ↦ kAt sig (headerAt 8 + 8 * (a + i)) :=
  List.map_congr_left fun i _ ↦ by subst ho; exact congrArg (kAt sig) (by simp only [headerAt]; omega)

/-- **The public values' header lanes, as words of the stream**. -/
theorem pubX_hdrLanes (x : List UInt8) :
    (pubX x).hdrLanes = (List.range pubLanes).map fun k ↦ kAt (sigOfX x) (headerAt 8 + 8 * k) := by
  have hp : pubLanes = 1 + 4 + 4 + 4 + 1 + 4 + 597 + 3 * (accVars + 1) := rfl
  rw [hp]
  simp only [map_range_add]
  have hd : (hdX x).vk = digestAt (hdrBytesX x) 16 := rfl
  have hacc : ((List.range accVars).map fun i ↦ feAt (sigOfX x) (headerAt (offAcc + eBytes * i))) ++
      [feAt (sigOfX x) (headerAt (offAcc + eBytes * accVars))] =
      (List.range (accVars + 1)).map fun i ↦ feAt (sigOfX x) (headerAt offAcc + 24 * i) := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun i _ ↦ ?_) ?_
    · exact congrArg (feAt (sigOfX x)) (by simp only [headerAt, offAcc, eBytes]; omega)
    · exact congrArg (fun o ↦ [feAt (sigOfX x) o]) (by simp only [headerAt, offAcc, eBytes]; omega)
  unfold Pub.hdrLanes pubX pubOf
  simp only [hd, digestLanes_digestAt, List.append_assoc, hacc, flatMap_lanes]
  refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_
    (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ ?_))))))
  · simp [kAt]
  · refine List.map_congr_left fun i _ ↦ ?_
    rw [kAt_sigOfX, show 8 + 8 * (1 + i) = 16 + 8 * i by omega]
    rfl
  · exact seg _ 48 5 4 rfl
  · exact seg _ 80 9 4 rfl
  · simp [kAt, headerAt]
  · exact seg _ 120 14 4 rfl
  · rw [show sigBytes / 8 = 597 from rfl]; exact seg _ 152 18 597 rfl
  · exact List.map_congr_left fun j _ ↦
      congrArg (kAt (sigOfX x)) (by simp only [headerAt, offAcc, sigBytes]; omega)

/-- **The statement's `PUB` lanes are its public values' header lanes.** -/
theorem hdrLanes_eq_pubX (x : List UInt8) : hdrLanes x = (pubX x).hdrLanes := by
  rw [pubX_hdrLanes, hdrLanes]
  exact List.map_congr_left fun k _ ↦ hdrLane_eq_kAt x k

/-! ## `acc_in` in the lanes -/

/-- **A child's incoming accumulator as V_S reads it**: point coordinate `i` is the `E` scalar of
stream lanes `626 + 3i …` (header lane `615 + 3i` of the seed, which starts at lane 11). -/
theorem pubOf_accIn_pt (vk c : RecursionFast.Digest) (sig : ByteArray) {i : ℕ} (hi : i < accVars) :
    (pubOf vk c sig).accIn.pt.getD i 0 = feAt sig (8 * (11 + 615 + 3 * i)) := by
  simp only [pubOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  exact congrArg (feAt sig) (by simp only [headerAt, offAcc, eBytes, sigBytes]; omega)

/-- A child's incoming claimed value as V_S reads it (stream lanes `626 + 3D …`). -/
theorem pubOf_accIn_y (vk c : RecursionFast.Digest) (sig : ByteArray) :
    (pubOf vk c sig).accIn.y = feAt sig (8 * (11 + 615 + 3 * accVars)) :=
  congrArg (feAt sig) (by simp only [headerAt, offAcc, eBytes, sigBytes, accVars])

/-- **The statement's incoming accumulator, point coordinate `i`**, from its header lanes `615 + 3i`,
`616 + 3i`, `617 + 3i` (the `PUB` cells, `InMapN.pub`). -/
theorem accIn_pt_lanes (x : List UInt8) {i : ℕ} (hi : i < accVars) :
    (pubX x).accIn.pt.getD i 0 = ⟨hdrLane x (615 + 3 * i), hdrLane x (616 + 3 * i), hdrLane x (617 + 3 * i)⟩ := by
  have e1 : headerAt 8 + 8 * (615 + 3 * i) = 8 * (11 + 615 + 3 * i) := by simp only [headerAt]; omega
  have e2 : headerAt 8 + 8 * (616 + 3 * i) = 8 * (11 + 615 + 3 * i) + 8 := by simp only [headerAt]; omega
  have e3 : headerAt 8 + 8 * (617 + 3 * i) = 8 * (11 + 615 + 3 * i) + 16 := by simp only [headerAt]; omega
  rw [pubX, pubOf_accIn_pt _ _ _ hi, feAt, hdrLane_eq_kAt, hdrLane_eq_kAt, hdrLane_eq_kAt, e1, e2, e3]

/-- **The statement's incoming claimed value**, from its header lanes `615 + 3D`, …. -/
theorem accIn_y_lanes (x : List UInt8) :
    (pubX x).accIn.y = ⟨hdrLane x (615 + 3 * accVars), hdrLane x (616 + 3 * accVars),
      hdrLane x (617 + 3 * accVars)⟩ := by
  have e1 : headerAt 8 + 8 * (615 + 3 * accVars) = 8 * (11 + 615 + 3 * accVars) := by
    simp only [headerAt]; omega
  have e2 : headerAt 8 + 8 * (616 + 3 * accVars) = 8 * (11 + 615 + 3 * accVars) + 8 := by
    simp only [headerAt]; omega
  have e3 : headerAt 8 + 8 * (617 + 3 * accVars) = 8 * (11 + 615 + 3 * accVars) + 16 := by
    simp only [headerAt]; omega
  rw [pubX, pubOf_accIn_y, feAt, hdrLane_eq_kAt, hdrLane_eq_kAt, hdrLane_eq_kAt, e1, e2, e3]

end Lvm.NS
