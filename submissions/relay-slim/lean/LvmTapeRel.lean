-- New for lvm2 (WP T-W): the tape relation (BLUEPRINT2 §1.1) and the chain it proves. The chain
-- induction is v1's `chain_of_CH` (`LvmChainTable`, K2-LC's induction over K2-LS `BlockPerm`s through
-- `chainStep_pad43`) with the committed input replaced by the virtual one.
import LvmChainTable
import LvmSpongeTableLink

/-!
# The tape relation

The chain region of the tape has `2^w` rows (`w = 20`); row `x` is chain step `x + 1`. Only the
digest lanes `D x l` (`l < 4`) are committed; the input of a row is **virtual** (`chainIn`), an affine
function of the committed digests, the public start `s` and the public mask `[i < n]`:

| row | `in(i)` |
|---|---|
| `i = 0` | `Pad43(s)` |
| `1 ≤ i < n` | `Pad43(D[i − 1])` |
| `n ≤ i` | `0` |

* `ChainTapeRel`: what the tape's Keccak phases (T1, T2 and the wiring T3–T4) prove about `D`:
  (a) lanes `0 … 3` of `Keccak-f(in(x))` are `D x` on every row `x < 2^w`; (c) `D[n − 1] = hd`.
* **`chain_of_tape`**: `1 ≤ n ≤ 2^w` and `ChainTapeRel` give `chainEnd s n = hd`. Dead rows
  (`x ≥ n`) are forced to `Keccak-f(0)` and carry no statement.

**The sponge region (stage S3, optional, BLUEPRINT2 §11).** Rows `2^w + j`, `j < 2^hs`, are v1's `KS`
rows with a virtual input: lane `l` of row `j` is `cont_j·Y_l[j − 1] + [l < 17]·Msg_l[j]`, the
virtual column `ksVirt` read as `inState`; the rest of the tape (rows up to `2^(w+1)`) is void (zero
input). `Msg = msgOf hr M XM`: `C_rec`'s `M` below `2^hr`, `C_main`'s `XM` above (R-BP2's B2: `XM`'s
lower half is never read, so its value carries no statement).

* `TapeRel`: `ChainTapeRel` and (b): all 25 lanes of `Keccak-f(in(2^w + j))` are `Y j`.
* **`spongeRel_of_tape`**: with `cont 0 = false`, the sponge region is v1's `SpongeRel` on `ksVirt`
  (K2-LS's `spongeRel_of_KSRel` with the link now definitional), whence `traceDigest_of_KS`,
  `wotsLeaf_of_KS`, `wotsStep_of_KS`, `sigNode_of_KS` unchanged; `msgOf_eq_ksMsg` is v1's message
  map.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakGkr Lvm.KSponge

/-! ## The virtual input -/

/-- Bit `j` of row `x` of a lane table `F x l` (bit `j % 64` of lane `j / 64`). -/
def rowBits (F : ℕ → ℕ → K) (x j : ℕ) : Bool := (F x (j / 64)).toBitVec.getLsbD (j % 64)

/-- **The virtual input of a chain row** from the start `s`, the length `n` and the digest lanes `D`. -/
def chainIn (s : RecursionFast.Digest) (n : ℕ) (D : ℕ → ℕ → K) (i : ℕ) : RecursionFast.Keccak.State :=
  if i = 0 then pad43St (digestBits s)
  else if i < n then pad43St (rowBits D (i - 1))
  else zeroSt

/-- **The chain part of `TapeRel`** (BLUEPRINT2 §1.1 (a) and (c), stage S2). -/
structure ChainTapeRel (w : ℕ) (s : RecursionFast.Digest) (n : ℕ) (hd : RecursionFast.Digest)
    (D : ℕ → ℕ → K) : Prop where
  /-- (a) The digest lanes are the permutation's output on every row of the chain region. -/
  out : ∀ x < 2 ^ w, ∀ l < 4, D x l = laneWord (keccakF1600 (chainIn s n D x)) l
  /-- (c) The last live row is the claimed chain end. -/
  last : ∀ l < 4, D (n - 1) l = K.ofLane (RecursionFast.Keccak.blockLane hd.toArray l)

/-! ## The chain -/

/-- The digest bits of a row whose lanes `0 … 3` are those of `Keccak-f(a)`. -/
theorem rowBits_eq {D : ℕ → ℕ → K} {x : ℕ} {a : RecursionFast.Keccak.State}
    (hout : ∀ l < 4, D x l = laneWord (keccakF1600 a) l) {j : ℕ} (hj : j < 256) :
    rowBits D x j = digestBits (stDigest (RecursionFast.Keccak.keccakF a)) j := by
  rw [rowBits, hout _ (by omega), digestBits, dite_eq_left hj,
    stDigest_bit _ (by omega) (Nat.mod_lt _ (by decide)), keccakF1600_eq',
    show 8 * (j / 8) + j % 8 = j from Nat.div_add_mod j 8, stBit, dite_eq_left (by omega), laneWord,
    K.ofLane, lane_eq _ (by omega)]
  rfl

/-- **`chain_of_tape`**: the chain part of the tape relation proves the chain. -/
theorem chain_of_tape {w : ℕ} {s hd : RecursionFast.Digest} {n : ℕ} {D : ℕ → ℕ → K} (hn : 1 ≤ n)
    (hN : n ≤ 2 ^ w) (H : ChainTapeRel w s n hd D) : RecursionFast.chainEnd s n = hd := by
  let Yd : ℕ → RecursionFast.Digest :=
    fun x ↦ stDigest (RecursionFast.Keccak.keccakF (chainIn s n D x))
  have step : ∀ x < n, Yd x = RecursionFast.chainEnd s (x + 1) := by
    intro x
    induction x with
    | zero =>
      intro _
      show stDigest (RecursionFast.Keccak.keccakF (chainIn s n D 0)) = _
      rw [chainIn, if_pos rfl, ← chainStep_pad43]
      rfl
    | succ x ih =>
      intro hx
      have hy : pad43St (rowBits D x) = pad43St (digestBits (Yd x)) :=
        pad43St_congr fun j hj ↦ rowBits_eq (H.out x (by omega)) hj
      have ih' : Yd x = RecursionFast.chainEnd s (x + 1) := ih (by omega)
      show stDigest (RecursionFast.Keccak.keccakF (chainIn s n D (x + 1))) = _
      rw [chainIn, if_neg (by omega), if_pos hx, Nat.add_sub_cancel, hy, ← chainStep_pad43, ih',
        RecursionFast.chainEnd, RecursionFast.chainEnd, Function.iterate_succ_apply' _ (x + 1)]
  have hs := step (n - 1) (by omega)
  rw [Nat.sub_add_cancel hn] at hs
  rw [← hs]
  refine digest_ext fun e he t ht ↦ ?_
  have hlast := H.last (e / 8) (by omega)
  rw [H.out _ (by omega) _ (by omega), laneWord] at hlast
  have hw := congrArg (fun a : K ↦ a.toBitVec.getLsbD (8 * (e % 8) + t)) hlast
  simp only [K.ofLane, BF64.toBitVec_ofBitVec] at hw
  rw [stDigest_bit _ he ht, ← keccakF1600_eq', stBit_eq_sbit _ (by omega), sbit,
    show (8 * e + t) / 64 = e / 8 by omega, show (8 * e + t) % 64 = 8 * (e % 8) + t by omega,
    hw, blockLane_bit _ _ (by omega),
    show 8 * (e / 8) + (8 * (e % 8) + t) / 8 = e by omega,
    show (8 * (e % 8) + t) % 8 = t by omega]
  simp [Array.getD, he]

/-! ## The sponge region (S3) -/

/-- The virtual `KS` input column: word `j + 2^hs·l` is `cont_j·Y_l[j − 1] + [l < 17]·Msg_l[j]`. -/
def ksVirt (hs : ℕ) (Y Msg : ℕ → ℕ → K) (cont : ℕ → Bool) (k : ℕ) : K :=
  (if cont (k % 2 ^ hs) then Y (k % 2 ^ hs - 1) (k / 2 ^ hs) else 0) +
    (if k / 2 ^ hs < 17 then Msg (k % 2 ^ hs) (k / 2 ^ hs) else 0)

/-- The message lanes: `M` (from `C_rec`) below `2^hr`, `XM` (from `C_main`) above. -/
def msgOf (hr : ℕ) (M XM : ℕ → ℕ → K) (j l : ℕ) : K := if j < 2 ^ hr then M j l else XM j l

/-- **The virtual input of a tape row**: the chain region below `2^w`, the sponge region
`2^w + j` (`j < 2^hs`), zero above. -/
def tapeIn (w hs : ℕ) (s : RecursionFast.Digest) (n : ℕ) (D Y Msg : ℕ → ℕ → K) (cont : ℕ → Bool)
    (i : ℕ) : RecursionFast.Keccak.State :=
  if i < 2 ^ w then chainIn s n D i
  else if i - 2 ^ w < 2 ^ hs then inState hs (ksVirt hs Y Msg cont) 0 (i - 2 ^ w)
  else zeroSt

/-- **The tape relation** (BLUEPRINT2 §1.1, stage S3): (a), (c) on the chain region and (b). -/
structure TapeRel (w hs : ℕ) (s : RecursionFast.Digest) (n : ℕ) (hd : RecursionFast.Digest)
    (D Y Msg : ℕ → ℕ → K) (cont : ℕ → Bool) : Prop where
  /-- (a) and (c). -/
  chain : ChainTapeRel w s n hd D
  /-- (b) All 25 lanes of a sponge row's permutation output are `Y`. -/
  sponge : ∀ j < 2 ^ hs, ∀ l < 25,
    Y j l = laneWord (keccakF1600 (tapeIn w hs s n D Y Msg cont (2 ^ w + j))) l

/-- **`spongeRel_of_tape`**: the tape's sponge region is a sponge table (`SpongeRel`) on the
virtual input column, with the message lanes `Msg` and `cont` (`cont 0 = false`). -/
theorem spongeRel_of_tape {w hs : ℕ} {s hd : RecursionFast.Digest} {n : ℕ} {D Y Msg : ℕ → ℕ → K}
    {cont : ℕ → Bool} (H : TapeRel w hs s n hd D Y Msg cont) (h0 : cont 0 = false) :
    SpongeRel hs (ksVirt hs Y Msg cont) Y Msg cont where
  out i hi l hl := by
    rw [H.sponge i hi l hl, tapeIn, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  link i hi l hl := by
    rw [ksVirt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos hs), Nat.div_eq_of_lt hi, zero_add]
  cont0 := h0

/-- v1's message map (`ksMsg`, `X` indexed from `2^r`) is `msgOf` with `XM` indexed by the row. -/
theorem msgOf_eq_ksMsg (hr : ℕ) (M XM : ℕ → ℕ → K) :
    msgOf hr M XM = ksMsg hr M (fun i l ↦ XM (i + 2 ^ hr) l) := by
  funext j l
  unfold msgOf ksMsg
  split_ifs with h
  · rfl
  · show XM j l = XM (j - 2 ^ hr + 2 ^ hr) l
    rw [Nat.sub_add_cancel (by omega)]

end Lvm.KG
