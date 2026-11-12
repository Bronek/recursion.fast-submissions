-- Copied from flock-recursive `FRKeccakSponge.lean` (stage K2-LS) for lvm (WP-8) as `LvmKSponge`; namespace FR.KSponge → Lvm.KSponge.
import RecursionFast.Library.KeccakFast
import RecursionFast.Contract.Signature

/-!
# The Keccak-256 sponge over abstract permutation blocks (`absorb_pad`, `absorb_sound`)

The block circuit (stage K2-LC) proves, per block, that its output state is `keccakF` of its input
state. This module works **above** that fact: `BlockPerm sIn sOut` (`sOut = keccakF sIn`) is a
hypothesis per block, and the module proves what a chain of such blocks computes in terms of the
contract's `keccak256` / `keccakDigest` (`Contract/Hash/Keccak.lean`, `Contract/Relation.lean`).

* `xorMsg a m`: the 136 rate bytes `m 0 … m 135` XORed into the first 17 lanes of `a` (exactly the
  contract's `absorb` body, `blockLane`); `stDigest a`: the first 32 bytes of `a` (lanes 0–3,
  little-endian), the contract's output map.
* **`keccakDigest_sponge`**: `keccakDigest msg` is `stDigest` of the iterated block map
  `spongeSt (pad msg)` after `(pad msg).length / 136` blocks (`absorb` unfolded structurally).
* **`absorb_pad`**: blocks `i < N = |msg|/136 + 1`, block `i`'s rate bytes the bytes
  `136 i … 136 i + 135` of `pad msg`, starting from the zero state, linked `sIn (i+1) = sOut i`,
  each a `BlockPerm` of its input XOR its bytes: the last output's digest is `keccakDigest msg`.
* **`absorb_sound`** (the stream form, the shape of the BLAKE2s `stream_sound` / `chain_digest`):
  the message is *read* from the blocks, byte `p` at block `p / 136`, byte `p % 136`
  (`streamOf m L`), and the padding bytes `L … 136 N − 1` are pinned (`PadOk m L`, `padAt`).
* **`absorb_one`**: the one-block case (`L ≤ 135`); **`absorb_whole`**: `L = 136 q` whole blocks and
  a separate final pad block `0x01 ‖ 0^134 ‖ 0x80` (`padBlk`), the node's stream ending (K0-DES §3.3).
-/

namespace Lvm
namespace KSponge
open RecursionFast RecursionFast.Keccak

/-! ## The block interface -/

/-- The all-zero state, the sponge's start. -/
def zeroSt : State := Vector.replicate 25 0

/-- **The per-block fact** a Keccak block's constraints give (stage K2-LC): its output state is
`Keccak-f[1600]` of its input state. Everything below takes it as a hypothesis per block. -/
def BlockPerm (sIn sOut : State) : Prop := sOut = keccakF sIn

/-- The 136 rate bytes `m 0 … m 135` of a block as an array. -/
def rateArr (m : ℕ → UInt8) : Array UInt8 := Array.ofFn fun j : Fin rate => m j

/-- **Absorbing one block**: the rate bytes `m 0 … m 135` XORed into lanes `0 … 16` of `a`, little
endian (the contract's `absorb` body, `blockLane`; lanes `17 … 24`, the capacity, unchanged). -/
def xorMsg (a : State) (m : ℕ → UInt8) : State :=
  Vector.ofFn fun i => a[i] ^^^ blockLane (rateArr m) i

/-- **The digest of a state**: its first 32 bytes, lane by lane, each lane little-endian (the
contract's output map in `keccak256`). -/
def stDigest (a : State) : Digest :=
  ⟨((a.toList.flatMap fun w => (List.range 8).map fun k => (w >>> (8 * k).toUInt64).toUInt8).take
    32).toArray, by simp [List.map_const']⟩

/-! ## The sponge as an iterated block map -/

/-- The sponge's state after `j` blocks of the (padded) byte string `P`. -/
def spongeSt (P : List UInt8) : ℕ → State
  | 0 => zeroSt
  | j + 1 => keccakF (Vector.ofFn fun i =>
      (spongeSt P j)[i] ^^^ blockLane ((P.drop (rate * j)).take rate).toArray i)

theorem absorb_spongeSt (P : List UInt8) :
    ∀ n j, absorb (spongeSt P j) (P.drop (rate * j)) n = spongeSt P (j + n) := by
  intro n
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    rw [absorb, List.drop_drop, ← Nat.mul_succ]
    have : keccakF (Vector.ofFn fun i =>
        (spongeSt P j)[i] ^^^ blockLane ((P.drop (rate * j)).take rate).toArray i) =
        spongeSt P (j + 1) := rfl
    rw [this, ih (j + 1)]
    congr 1
    omega

/-- **The contract's Keccak-256 is the iterated block map.** -/
theorem keccakDigest_sponge (msg : List UInt8) :
    keccakDigest msg = stDigest (spongeSt (pad msg) ((pad msg).length / rate)) := by
  have h := absorb_spongeSt (pad msg) ((pad msg).length / rate) 0
  rw [Nat.mul_zero, List.drop_zero, Nat.zero_add] at h
  simp only [keccakDigest, keccak256, stDigest]
  rw [← h]
  rfl

/-! ## The padding, byte by byte -/

/-- The number of blocks of an `L`-byte message: `⌊L / 136⌋ + 1`. -/
def nBlk (L : ℕ) : ℕ := L / rate + 1

/-- **The padding byte** at offset `p` (`L ≤ p < 136 · nBlk L`) of a padded `L`-byte message:
`0x01` at `L` (`0x81` when it is also the last byte), `0x80` at the last byte, `0` between. -/
def padAt (L p : ℕ) : UInt8 :=
  if p = L then (if L % rate = rate - 1 then 0x81 else 0x01)
  else if p % rate = rate - 1 then 0x80 else 0

theorem pad_length_eq (msg : List UInt8) : (pad msg).length = rate * nBlk msg.length := by
  have h := Nat.mod_lt msg.length (show 0 < rate by decide)
  have hp : (pad msg).length = msg.length + (rate - msg.length % rate) := by
    simp only [pad]
    split <;> simp_all [rate]; omega
  have := Nat.div_add_mod msg.length rate
  rw [hp, nBlk, Nat.mul_succ]
  omega

theorem pad_div (msg : List UInt8) : (pad msg).length / rate = nBlk msg.length := by
  rw [pad_length_eq, Nat.mul_div_cancel_left _ (by decide)]

/-- The padded message's bytes: the message below its length. -/
theorem pad_getD_lt (msg : List UInt8) {p : ℕ} (hp : p < msg.length) :
    (pad msg).getD p 0 = msg.getD p 0 := by
  simp only [pad, List.getD_eq_getElem?_getD, List.getElem?_append_left hp]

/-- The padded message's bytes past the message: `padAt`. -/
theorem pad_getD_ge (msg : List UInt8) {p : ℕ} (h1 : msg.length ≤ p)
    (h2 : p < rate * nBlk msg.length) : (pad msg).getD p 0 = padAt msg.length p := by
  set L := msg.length with hL
  simp only [pad, List.getD_eq_getElem?_getD, List.getElem?_append_right h1, ← hL, padAt,
    List.cons_append]
  simp only [nBlk] at h2
  have r : rate = 136 := rfl
  generalize rate = R at *
  subst r
  have hm := Nat.mod_lt L (show 0 < 136 by decide)
  have hd := Nat.div_add_mod L 136
  by_cases hr : 136 - L % 136 = 1
  · -- one padding byte
    rw [ite_eq_left hr]
    have hp : p = L := by omega
    subst hp
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, ite_true]
    rw [ite_eq_left (by omega)]
  · rw [ite_eq_right hr]
    rcases Nat.eq_or_lt_of_le h1 with hp | hp
    · subst hp
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, ite_true]
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, p - L = k + 1 := ⟨p - L - 1, by omega⟩
      rw [hk, List.getElem?_cons_succ]
      by_cases hl : p % 136 = 136 - 1
      · rw [ite_eq_left hl, List.getElem?_append_right (by simp; omega),
          show k - (List.replicate (136 - L % 136 - 2) (0 : UInt8)).length = 0 by simp; omega]
        rfl
      · rw [ite_eq_right hl, List.getElem?_append_left (by simp; omega),
          List.getElem?_replicate, ite_eq_left (by omega)]
        rfl

/-! ## Blocks laid out from the padded message -/

theorem blockLane_congr {a b : Array UInt8} (h : ∀ q, a.getD q 0 = b.getD q 0) (i : ℕ) :
    blockLane a i = blockLane b i := by
  simp only [blockLane, h]

theorem rateArr_getD (m : ℕ → UInt8) (q : ℕ) :
    (rateArr m).getD q 0 = if q < rate then m q else 0 := by
  unfold rateArr
  rw [Array.getD_eq_getD_getElem?]
  by_cases hq : q < rate
  · rw [ite_eq_left hq, Array.getElem?_ofFn, dite_eq_left hq]; rfl
  · rw [ite_eq_right hq, Array.getElem?_ofFn, dite_eq_right hq]; rfl

/-- A block whose rate bytes are bytes `136 j …` of `P` absorbs as the sponge's block `j`. -/
theorem xorMsg_eq_block (a : State) (m : ℕ → UInt8) (P : List UInt8) (j : ℕ)
    (hm : ∀ q < rate, m q = P.getD (rate * j + q) 0) :
    xorMsg a m = Vector.ofFn fun i => a[i] ^^^ blockLane ((P.drop (rate * j)).take rate).toArray i := by
  have h : ∀ q, (rateArr m).getD q 0 = ((P.drop (rate * j)).take rate).toArray.getD q 0 := by
    intro q
    rw [rateArr_getD]
    by_cases hq : q < rate
    · rw [ite_eq_left hq, hm q hq]
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, hq]
    · rw [ite_eq_right hq]
      simp [Array.getD_eq_getD_getElem?, hq]
  simp only [xorMsg, blockLane_congr h]

/-- **The sponge over laid-out blocks.** `N = nBlk |msg|` blocks: block `i`'s rate bytes are the
bytes `136 i … 136 i + 135` of `pad msg`; block 0 starts from the zero state, block `i + 1` from
block `i`'s output; each block's output is `keccakF` of its input XOR its bytes. Then the digest of
the last block's output is the contract's `keccakDigest msg`. -/
theorem absorb_pad (msg : List UInt8) (m : ℕ → ℕ → UInt8) (sIn sOut : ℕ → State)
    (hstart : sIn 0 = zeroSt)
    (hperm : ∀ i < nBlk msg.length, BlockPerm (xorMsg (sIn i) (m i)) (sOut i))
    (hlink : ∀ i, i + 1 < nBlk msg.length → sIn (i + 1) = sOut i)
    (hm : ∀ i < nBlk msg.length, ∀ q < rate, m i q = (pad msg).getD (rate * i + q) 0) :
    stDigest (sOut (nBlk msg.length - 1)) = keccakDigest msg := by
  set N := nBlk msg.length with hN
  have key : ∀ i < N, sIn i = spongeSt (pad msg) i ∧ sOut i = spongeSt (pad msg) (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h0
      refine ⟨hstart, ?_⟩
      rw [show sOut 0 = _ from hperm 0 h0, hstart, xorMsg_eq_block _ _ _ 0 (hm 0 h0)]
      rfl
    | succ i ih =>
      intro hi
      have hin : sIn (i + 1) = spongeSt (pad msg) (i + 1) := by
        rw [hlink i hi, (ih (by omega)).2]
      refine ⟨hin, ?_⟩
      rw [show sOut (i + 1) = _ from hperm _ hi, hin, xorMsg_eq_block _ _ _ _ (hm _ hi)]
      rfl
  have hN1 : N - 1 + 1 = N := by simp [hN, nBlk]
  rw [(key _ (by omega)).2, hN1, keccakDigest_sponge, pad_div]

/-- **Non-vacuity of `absorb_pad`**: the honest blocks (the sponge's own states, the padded
message's bytes) meet every hypothesis. -/
theorem absorb_pad_complete (msg : List UInt8) :
    let m : ℕ → ℕ → UInt8 := fun i q => (pad msg).getD (rate * i + q) 0
    let sIn : ℕ → State := spongeSt (pad msg)
    let sOut : ℕ → State := fun i => spongeSt (pad msg) (i + 1)
    sIn 0 = zeroSt ∧ (∀ i, BlockPerm (xorMsg (sIn i) (m i)) (sOut i)) ∧
      (∀ i, sIn (i + 1) = sOut i) ∧ ∀ i, ∀ q < rate, m i q = (pad msg).getD (rate * i + q) 0 := by
  refine ⟨rfl, fun i => ?_, fun _ => rfl, fun _ _ _ => rfl⟩
  rw [BlockPerm, xorMsg_eq_block _ _ _ i (fun _ _ => rfl)]
  rfl

/-! ## The stream form: the message read from the blocks -/

/-- The `L` message bytes a sequence of blocks carries: byte `p` is byte `p % 136` of block
`p / 136`. -/
def streamOf (m : ℕ → ℕ → UInt8) (L : ℕ) : List UInt8 :=
  List.ofFn fun p : Fin L => m (p / rate) (p % rate)

theorem streamOf_length (m : ℕ → ℕ → UInt8) (L : ℕ) : (streamOf m L).length = L := by
  simp [streamOf]

theorem streamOf_getD (m : ℕ → ℕ → UInt8) (L : ℕ) {p : ℕ} (hp : p < L) :
    (streamOf m L).getD p 0 = m (p / rate) (p % rate) := by
  simp [streamOf, List.getD_eq_getElem?_getD, hp]

/-- **The padding is pinned**: the bytes `L … 136 · nBlk L − 1` of the blocks are `padAt L`. -/
def PadOk (m : ℕ → ℕ → UInt8) (L : ℕ) : Prop :=
  ∀ p, L ≤ p → p < rate * nBlk L → m (p / rate) (p % rate) = padAt L p

/-- **A stream of blocks** (the Keccak `stream_sound`): `nBlk L` blocks from the zero state,
linked, each a `BlockPerm` of its input XOR its rate bytes, and with the padding bytes pinned,
carry at the last block's output the contract's Keccak-256 of the `L` bytes they hold. -/
theorem absorb_sound (L : ℕ) (m : ℕ → ℕ → UInt8) (sIn sOut : ℕ → State)
    (hstart : sIn 0 = zeroSt)
    (hperm : ∀ i < nBlk L, BlockPerm (xorMsg (sIn i) (m i)) (sOut i))
    (hlink : ∀ i, i + 1 < nBlk L → sIn (i + 1) = sOut i)
    (hpad : PadOk m L) :
    stDigest (sOut (nBlk L - 1)) = keccakDigest (streamOf m L) := by
  have hl := streamOf_length m L
  have h := absorb_pad (streamOf m L) m sIn sOut hstart (by rw [hl]; exact hperm)
    (by rw [hl]; exact hlink) ?_
  · rwa [hl] at h
  rw [hl]
  intro i hi q hq
  have hpq : (rate * i + q) / rate = i ∧ (rate * i + q) % rate = q := by
    simp only [rate] at hq ⊢; omega
  rcases Nat.lt_or_ge (rate * i + q) L with hlt | hge
  · rw [pad_getD_lt _ (by rw [hl]; exact hlt), streamOf_getD _ _ hlt, hpq.1, hpq.2]
  · rw [pad_getD_ge _ (by rw [hl]; exact hge) (by rw [hl]; simp only [nBlk, rate] at *; omega), hl,
      ← hpad _ hge (by simp only [nBlk, rate] at *; omega), hpq.1, hpq.2]

/-! ## One block -/

/-- **One block** (`L ≤ 135`: `chainStep` 33 B, `leafStmt` 41 B, `wotsStep` 43 B, `nodeStmt` and
`sigNode` 65 B): a block from the zero state whose rate bytes are the message, then `padAt`, outputs
the message's digest. -/
theorem absorb_one (msg : List UInt8) (hL : msg.length < rate) (m : ℕ → UInt8) (sOut : State)
    (hmsg : ∀ q < msg.length, m q = msg.getD q 0)
    (hpad : ∀ q, msg.length ≤ q → q < rate → m q = padAt msg.length q)
    (hperm : BlockPerm (xorMsg zeroSt m) sOut) :
    stDigest sOut = keccakDigest msg := by
  have hN : nBlk msg.length = 1 := by simp only [nBlk, rate] at hL ⊢; omega
  have := absorb_pad msg (fun _ => m) (fun _ => zeroSt) (fun _ => sOut) rfl
    (fun _ _ => hperm) (fun i hi => by omega) (fun i hi q hq => by
      obtain rfl : i = 0 := by omega
      rw [Nat.mul_zero, Nat.zero_add]
      rcases Nat.lt_or_ge q msg.length with h | h
      · rw [pad_getD_lt _ h, hmsg q h]
      · rw [pad_getD_ge _ h (by rw [hN]; simpa using hq), hpad q h hq])
  exact this

/-! ## Whole blocks and the final pad block -/

/-- The rate bytes of the pad block `0x01 ‖ 0^134 ‖ 0x80` (the padding of a message of a length
`≡ 0 mod 136`). -/
def padBlk (j : ℕ) : UInt8 := if j = 0 then 0x01 else if j = rate - 1 then 0x80 else 0

/-- **Whole blocks and a final pad block** (K0-DES §3.3: every node stream has `136 q` bytes and
ends in a full pad block, linked from the last main block, possibly muxed): `q > 0` main blocks
carrying the stream, then a final block `(fIn, fOut)` with input `sOut (q − 1)` and rate bytes
`padBlk`, give at `fOut` the digest of the `136 q` streamed bytes. -/
theorem absorb_whole (q : ℕ) (hq : 0 < q) (m : ℕ → ℕ → UInt8) (sIn sOut : ℕ → State)
    (fIn fOut : State) (mF : ℕ → UInt8)
    (hstart : sIn 0 = zeroSt)
    (hperm : ∀ i < q, BlockPerm (xorMsg (sIn i) (m i)) (sOut i))
    (hlink : ∀ i, i + 1 < q → sIn (i + 1) = sOut i)
    (hfin : fIn = sOut (q - 1)) (hmF : ∀ j < rate, mF j = padBlk j)
    (hpermF : BlockPerm (xorMsg fIn mF) fOut) :
    stDigest fOut = keccakDigest (streamOf m (rate * q)) := by
  have hN : nBlk (rate * q) = q + 1 := by
    simp only [nBlk]; rw [Nat.mul_div_cancel_left _ (by decide)]
  let m' : ℕ → ℕ → UInt8 := fun i => if i < q then m i else mF
  let sIn' : ℕ → State := fun i => if i < q then sIn i else fIn
  let sOut' : ℕ → State := fun i => if i < q then sOut i else fOut
  have hs : streamOf m' (rate * q) = streamOf m (rate * q) := by
    simp only [streamOf, m']
    congr 1
    funext p
    rw [ite_eq_left (by have := p.isLt; simp only [rate] at *; omega)]
  have h := absorb_sound (rate * q) m' sIn' sOut' (by simp [sIn', hq, hstart])
    (fun i hi => by
      rw [hN] at hi
      by_cases hiq : i < q
      · simpa [m', sIn', sOut', hiq] using hperm i hiq
      · simpa [m', sIn', sOut', hiq] using hpermF)
    (fun i hi => by
      rw [hN] at hi
      by_cases hiq : i + 1 < q
      · simp [sIn', sOut', hiq, show i < q by omega, hlink i hiq]
      · have : i + 1 = q := by omega
        simp [sIn', sOut', hfin, ← this])
    (fun p h1 h2 => by
      rw [hN] at h2
      have hpq : p / rate = q := by simp only [rate] at *; omega
      simp only [m', hpq, lt_irrefl, ite_false]
      rw [hmF _ (Nat.mod_lt _ (by decide)), padBlk, padAt]
      by_cases h0 : p = rate * q
      · subst h0
        simp [rate]
      · rw [ite_eq_right h0, ite_eq_right (by simp only [rate] at *; omega)])
  rw [hN, Nat.add_sub_cancel] at h
  simpa [sOut', hs] using h

end KSponge
end Lvm
