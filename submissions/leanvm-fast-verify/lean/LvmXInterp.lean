-- adapted from rf-k/submissions/flock-recursive/lean/FRXBaryDefs.lean@8bff272b (section
-- G6_FRXBaryDefs) for lvm (WP-13b): FR's two-word field `F` re-targeted to lvm's one-word
-- `K = BF64`; namespace `FR.X` → `Lvm.X`; FR's `djIR`/`alphaIR` phases dropped (`ptK j` is the word `j`).

import LvmXDec
import LvmXLoop

/-!
# The barycentric interpolation over `K`: the pure form and the program

`interpF ptK J y s` (`LvmXEnc`) is the Lagrange interpolation of `y` on the points `ptK J` at
`ptK s`. The machine computes it in barycentric form (FR's `FRXBaryDefs`):

* off `J`: `interpF ptK J y s = ℓ(s) · Σ_{i ∈ J} y i · w_i · (ptK s − ptK i)⁻¹`, with
  `ℓ(s) = Π_{m ∈ J} (ptK s − ptK m)` and `w_i = (Π_{m ∈ J∖i} (ptK i − ptK m))⁻¹`
  (`interpF_bary`);
* on `J`: `interpF ptK J y s = y s` (`interpF_self`).

The machine tells the two apart by `ℓ(s) = 0` (`ptK` is injective below `2^15`). With `J` the list
`Jl = J₀ … J_{k−1}`, the machine's value is `baryValK` and **`baryValK_eq`** proves it is
`interpF ptK Jl.toFinset y s` for `s < 2^15`.

## The port from FR

FR's `F = GF(2^128)` takes two words; lvm's `K` element is one word (`rdK`), so FR's `ldF`/`stF`
are `.load`/`.store`, `addF` is one `xor`, `mulF`/`invF` are `mulK`/`invK`, and every table has
stride 1. The domain point of position `j` is the word `j` itself (`ptK j = wK (toWord j)`), so
FR's table `DJ` (`djIR`, the `alphaIR` call on the basis table) and the `alphaIR` call computing
`D(s)` in `sBody` disappear: `J_t` is read from `jb + t` as the `K` element, and the target index
word `s` is `ptK s`. FR's registers `216 …` are kept (each `F` pair's first word).

## The program (`baryIR k C jb wb eb cb cs ob`)

A coordinate `c < C` of position `j` is the `K` element at `cb + cs·j + c`. Phases:

1. `wtIR`: `W[t] := (Π_{m ≠ t} (J_t + J_m))⁻¹` at `wb + t`;
2. per target `s < k` (`sBody`): `E[t] := W[t] · (ptK s + J_t)⁻¹` at `eb + t` and
   `ℓ := Π_t (ptK s + J_t)`; per coordinate `c`: `acc := Σ_t y_c(J_t) E[t]` (registers only),
   then `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · acc)` at `ob + k·c + s`.

`cost_baryIR`: `25 + 1106 k + 49 k C + 1118 k² + 44 k² C` (FR: `38 + 2487 k + 108 k C +
1363 k² + 106 k² C`); at lvm's `k = 2^13`, `C = 64`: `264 041 021 465 ≈ 2^37.94`
(`cost_baryIR_lvm`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

/-! ## The machine's value over `K`, against `interpF` -/

/-- The domain point `ptK J_t` of the list `Jl`. -/
def djK (Jl : List ℕ) (t : ℕ) : BF64 := ptK (Jl.getD t 0)

/-- **The weight** `W[t] = (Π_{m < k, m ≠ t} (J_t + J_m))⁻¹`, as the machine's product
(`m = t` contributes `1`). -/
def wgtK (Jl : List ℕ) (k t : ℕ) : BF64 :=
  (∏ m ∈ range k, if m = t then 1 else djK Jl t + djK Jl m)⁻¹

/-- `ℓ(s) = Π_{t < k} (ptK s + J_t)`. -/
def ellK (Jl : List ℕ) (k s : ℕ) : BF64 := ∏ t ∈ range k, (ptK s + djK Jl t)

/-- `E[t] = W[t] · (ptK s + J_t)⁻¹`. -/
def eAtK (Jl : List ℕ) (k s t : ℕ) : BF64 := wgtK Jl k t * (ptK s + djK Jl t)⁻¹

/-- **The machine's value** at target `s` for the values `y`: `y s` when `ℓ(s) = 0`, else
`ℓ(s) · Σ_t y(J_t) E[t]`. -/
def baryValK (Jl : List ℕ) (k s : ℕ) (y : ℕ → BF64) : BF64 :=
  if ellK Jl k s = 0 then y s else ellK Jl k s * ∑ t ∈ range k, y (Jl.getD t 0) * eAtK Jl k s t

theorem toFinset_eq_imageB (Jl : List ℕ) :
    Jl.toFinset = (range Jl.length).image (fun t => Jl.getD t 0) := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_range, List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [List.getD_eq_getElem]⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [List.getD_eq_getElem]⟩

theorem getD_injOnB {Jl : List ℕ} (hnd : Jl.Nodup) :
    Set.InjOn (fun t => Jl.getD t 0) (range Jl.length : Set ℕ) := fun a ha b hb h => by
  simp only [coe_range, Set.mem_Iio] at ha hb
  simp only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
  exact (hnd.getElem_inj_iff).1 h

theorem prod_toFinsetB {Jl : List ℕ} (hnd : Jl.Nodup) (f : ℕ → BF64) :
    ∏ m ∈ Jl.toFinset, f m = ∏ t ∈ range Jl.length, f (Jl.getD t 0) := by
  rw [toFinset_eq_imageB, Finset.prod_image (getD_injOnB hnd)]

theorem sum_toFinsetB {Jl : List ℕ} (hnd : Jl.Nodup) (f : ℕ → BF64) :
    ∑ m ∈ Jl.toFinset, f m = ∑ t ∈ range Jl.length, f (Jl.getD t 0) := by
  rw [toFinset_eq_imageB, Finset.sum_image (getD_injOnB hnd)]

theorem prod_erase_iteB {J : Finset ℕ} {i : ℕ} (hi : i ∈ J) (f : ℕ → BF64) :
    ∏ m ∈ J.erase i, f m = ∏ m ∈ J, if m = i then 1 else f m := by
  rw [← Finset.mul_prod_erase J _ hi, if_pos rfl, one_mul]
  exact Finset.prod_congr rfl fun m hm => by rw [if_neg (Finset.mem_erase.1 hm).1]

/-- **The machine's value is the interpolation** (`J ⊆ [0, 2^15)` listed without repeats,
`s < 2^15`). -/
theorem baryValK_eq {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < 2 ^ 15) {s : ℕ}
    (hs : s < 2 ^ 15) (y : ℕ → BF64) :
    baryValK Jl Jl.length s y = interpF ptK Jl.toFinset y s := by
  have hinj : Set.InjOn ptK (Jl.toFinset : Set ℕ) := fun a ha b hb h =>
    ptK_injOn15 (Set.mem_Iio.2 (hJ a (List.mem_toFinset.1 ha)))
      (Set.mem_Iio.2 (hJ b (List.mem_toFinset.1 hb))) h
  have hget : ∀ t < Jl.length, Jl.getD t 0 ∈ Jl := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
  by_cases hsJ : s ∈ Jl
  · obtain ⟨t, ht, hts⟩ := List.mem_iff_getElem.1 hsJ
    have h0 : ellK Jl Jl.length s = 0 := by
      refine Finset.prod_eq_zero (i := t) (Finset.mem_range.2 ht) ?_
      rw [djK, List.getD_eq_getElem _ _ ht, hts, ← CharTwo.sub_eq_add, sub_self]
    rw [baryValK, if_pos h0, interpF_self hinj y (List.mem_toFinset.2 hsJ)]
  · have hne : ∀ m ∈ Jl.toFinset, ptK s ≠ ptK m := fun m hm h => hsJ (by
      have := ptK_injOn15 (Set.mem_Iio.2 hs)
        (Set.mem_Iio.2 (hJ m (List.mem_toFinset.1 hm))) h
      rw [this]; exact List.mem_toFinset.1 hm)
    have h0 : ellK Jl Jl.length s ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
      rw [djK, ← CharTwo.sub_eq_add, sub_ne_zero]
      exact hne _ (List.mem_toFinset.2 (hget t (Finset.mem_range.1 ht)))
    rw [baryValK, if_neg h0, interpF_bary hne, Algebra.algebraMap_self]
    simp only [RingHom.id_apply]
    rw [prod_toFinsetB hnd, sum_toFinsetB hnd]
    refine congrArg₂ _ (Finset.prod_congr rfl fun t _ => by rw [djK, CharTwo.sub_eq_add])
      (Finset.sum_congr rfl fun t ht => ?_)
    have ht' := Finset.mem_range.1 ht
    have hP : (∏ m ∈ range Jl.length, if m = t then 1 else djK Jl t + djK Jl m) =
        ∏ m ∈ range Jl.length, if Jl.getD m 0 = Jl.getD t 0 then 1
          else ptK (Jl.getD t 0) - ptK (Jl.getD m 0) := by
      refine Finset.prod_congr rfl fun m hm => ?_
      have hm' := Finset.mem_range.1 hm
      by_cases hmt : m = t
      · rw [if_pos hmt, if_pos (by rw [hmt])]
      · rw [if_neg hmt, if_neg (fun h => hmt ((hnd.getElem_inj_iff).1 (by
          rwa [List.getD_eq_getElem _ _ hm', List.getD_eq_getElem _ _ ht'] at h))), djK, djK,
          CharTwo.sub_eq_add]
    rw [eAtK, wgtK, prod_erase_iteB (List.mem_toFinset.2 (hget t ht')), prod_toFinsetB hnd, hP,
      djK, CharTwo.sub_eq_add (ptK s)]

/-! ## Registers (`216 …`, FR's numbers) -/

/-- `ptK s` or `J_t`. -/ def fDs : ℕ := 216
/-- `ℓ`. -/ def fLp : ℕ := 218
/-- `ptK s + J_t`. -/ def fDd : ℕ := 220
/-- Its inverse. -/ def fIv : ℕ := 222
/-- `E[t]`. -/ def fEt : ℕ := 224
/-- A product. -/ def fPr : ℕ := 226
/-- A column value. -/ def fY : ℕ := 228
/-- The accumulator. -/ def fAc : ℕ := 230
/-- A loaded element. -/ def fX : ℕ := 232
/-- `t`. -/ def bT : ℕ := 236
/-- `m`. -/ def bM : ℕ := 237
/-- `s`. -/ def bS : ℕ := 238
/-- `c`. -/ def bCi : ℕ := 239
/-- An address. -/ def bA : ℕ := 240
/-- A column address. -/ def bJ : ℕ := 242
/-- Constant scratch. -/ def bK : ℕ := 243
/-- A flag. -/ def bZ : ℕ := 244
/-- The outer loop's counter. -/ def bC1 : ℕ := 245
/-- Its count. -/ def bN1 : ℕ := 246
/-- The middle loop's counter. -/ def bC2 : ℕ := 247
/-- Its count. -/ def bN2 : ℕ := 248
/-- The inner loop's counter. -/ def bC3 : ℕ := 249
/-- Its count. -/ def bN3 : ℕ := 250

/-! ## The program -/

/-- `d := b + m · M[i]`. -/
def addrPs (d i b m : ℕ) : List Prim :=
  [.const bK (toWord m), .op .mul d i bK, .const bK (toWord b), .op .add d d bK]

/-- `d := b + M[i]` (stride 1). -/
def addr1Ps (d i b : ℕ) : List Prim := [.const bK (toWord b), .op .add d i bK]

/-- One factor of `W[t]`'s product: `fPr *= J_t + J_m` unless `m = t`. -/
def wInner (jb : ℕ) : XIR :=
  .seq (.blk (addr1Ps bA bM jb)) (.seq (.load fX bA)
    (.seq (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT])
      (.seq (.ite bZ (.blk []) (mulK fPr fPr fDd)) (.blk [.op .add bM bM cOne]))))

/-- **`W[t] := (Π_{m ≠ t} (J_t + J_m))⁻¹`** at `wb + t`. -/
def wtBody (k jb wb : ℕ) : XIR :=
  .seq (.blk (addr1Ps bA bT jb)) (.seq (.load fDs bA)
    (.seq (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)])
      (.seq (.loopK bC2 bN2 (toWord k) (wInner jb)) (.seq (invK fIv fPr)
        (.seq (.blk (addr1Ps bA bT wb)) (.seq (.store bA fIv) (.blk [.op .add bT bT cOne])))))))

/-- The table `W`. -/
def wtIR (k jb wb : ℕ) : XIR :=
  .seq (.blk [.const bT 0, .const bN1 (toWord k)]) (.loopK bC1 bN1 (toWord k) (wtBody k jb wb))

/-- **`E[t] := W[t] · (ptK s + J_t)⁻¹`** at `eb + t`, and `ℓ *= ptK s + J_t`. -/
def eBody (jb wb eb : ℕ) : XIR :=
  .seq (.blk (addr1Ps bA bT jb)) (.seq (.load fX bA) (.seq (.blk [.op .xor fDd fDs fX])
    (.seq (mulK fLp fLp fDd) (.seq (invK fIv fDd) (.seq (.blk (addr1Ps bA bT wb))
      (.seq (.load fX bA) (.seq (mulK fEt fX fIv) (.seq (.blk (addr1Ps bA bT eb))
        (.seq (.store bA fEt) (.blk [.op .add bT bT cOne]))))))))))

/-- **`acc += y_c(J_t) · E[t]`** (`y_c(j)` at `cb + cs·j + c`, `c` in `bCi`). -/
def aBody (jb eb cb cs : ℕ) : XIR :=
  .seq (.blk (addr1Ps bA bT jb)) (.seq (.load bJ bA)
    (.seq (.blk (addrPs bJ bJ cb cs ++ [.op .add bJ bJ bCi])) (.seq (.load fY bJ)
      (.seq (.blk (addr1Ps bA bT eb)) (.seq (.load fX bA) (.seq (mulK fPr fY fX)
        (.blk [.op .xor fAc fAc fPr, .op .add bT bT cOne])))))))

/-- `fAc := y_c(s)`. -/
def yIR (cb cs : ℕ) : XIR :=
  .seq (.blk (addrPs bA bS cb cs ++ [.op .add bA bA bCi])) (.load fAc bA)

/-- **One coordinate `c`**: `acc := Σ_t y_c(J_t) E[t]`, then `out[c][s] := (ℓ = 0 ? y_c(s) :
ℓ · acc)` at `ob + k·c + s`. -/
def cBody (k jb eb cb cs ob : ℕ) : XIR :=
  .seq (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)])
    (.seq (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs))
      (.seq (.ite bZ (yIR cb cs) (mulK fAc fLp fAc))
        (.seq (.blk (addrPs bA bCi ob k ++ [.op .add bA bA bS]))
          (.seq (.store bA fAc) (.blk [.op .add bCi bCi cOne])))))

/-- **One target `s`**: `ptK s`, the `E` row and `ℓ`, the flag `[ℓ = 0]`, the `C` coordinates. -/
def sBody (k C jb wb eb cb cs ob : ℕ) : XIR :=
  .seq (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0, .const bN2 (toWord k)])
    (.seq (.loopK bC2 bN2 (toWord k) (eBody jb wb eb))
      (.seq (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0, .const bN2 (toWord C)])
        (.seq (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob))
          (.blk [.op .add bS bS cOne]))))

/-- **The interpolation**: `out[c][s] = interpF ptK J y_c s` for `s < k`, `c < C`. -/
def baryIR (k C jb wb eb cb cs ob : ℕ) : XIR :=
  .seq (wtIR k jb wb) (.seq (.blk [.const bS 0, .const bN1 (toWord k)])
    (.loopK bC1 bN1 (toWord k) (sBody k C jb wb eb cb cs ob)))

/-! ## Well formed, no `loopT`, no output, cost -/

theorem bnw_mulK {d a b i : ℕ} (h1 : i ≠ d) (h3 : 9 ≤ i) : Writes (mulK d a b) i ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by have := mulKC_dst d a b p hp; omega, False.elim⟩

theorem bnw_invK {d a i : ℕ} (h1 : i ≠ d) (h3 : 12 ≤ i) : Writes (invK d a) i ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by have := invKC_dst d a p hp; omega, False.elim⟩

theorem wfK_mul {d a b : ℕ} (h : 4 ≤ d) : WF (mulK d a b) ↔ True := iff_true_intro (wf_mulK d a b h)
theorem wfK_inv {d a : ℕ} (h : 4 ≤ d) : WF (invK d a) ↔ True := iff_true_intro (wf_invK d a h)

theorem wf_baryIR (k C jb wb eb cb cs ob : ℕ) : WF (baryIR k C jb wb eb cb cs ob) := by
  simp [baryIR, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, addrPs, addr1Ps, WF,
    Writes, Prim.dst, bnw_mulK, bnw_invK, wfK_mul, wfK_inv, fDs, fLp, fDd, fIv, fEt, fPr, fY,
    fAc, fX, bT, bM, bS, bCi, bA, bJ, bK, bZ, bC1, bN1, bC2, bN2, bC3, bN3, cTmp, regs]

theorem noLoopT_baryIR (k C jb wb eb cb cs ob : ℕ) : NoLoopT (baryIR k C jb wb eb cb cs ob) := by
  simp [baryIR, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, mulK, invK, NoLoopT]

theorem outs_baryIR (k C jb wb eb cb cs ob t : ℕ) : outs (baryIR k C jb wb eb cb cs ob) t = 0 := by
  simp [baryIR, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, mulK, invK, outs]

/-- **The interpolation's cost** (`k, C < 2^64`). -/
theorem cost_baryIR (k C jb wb eb cb cs ob t : ℕ) (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) :
    cost (baryIR k C jb wb eb cb cs ob) t =
      25 + 1106 * k + 49 * k * C + 1118 * k ^ 2 + 44 * k ^ 2 * C := by
  have e1 : (toWord k).toNat = k := toNat_toWord hk
  have e2 : (toWord C).toNat = C := toNat_toWord hC
  simp only [baryIR, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, addrPs, addr1Ps,
    cost, cost_mulK, cost_invK, blkSteps, List.length_cons, List.length_nil, List.length_append,
    e1, e2]
  norm_num
  ring

/-- **The cost at lvm's sizes** (`k = 2^13`, `C = 64`): `≈ 2^37.94`. -/
theorem cost_baryIR_lvm (jb wb eb cb cs ob t : ℕ) :
    cost (baryIR (2 ^ 13) 64 jb wb eb cb cs ob) t = 264041021465 := by
  rw [cost_baryIR _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  norm_num

end Lvm.X
