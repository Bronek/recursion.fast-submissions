-- New for lvm (WP-13b): controls of `LvmXReadDefs` (the pure first-preimage reading of `C_rec`),
-- kept off `Solution`'s import closure. FR's `ReadControls` (rf-k/submissions/flock-recursive/
-- lean/FRXRead.lean@8bff272b) are the pattern.
import LvmXReadDefs

/-!
# Controls of the reading `readRow`

A toy log with one node query `dA ‖ dB` answered `dA`: every level's first preimage of `dA` is
that 64-byte query, so position `0` (all bits `0`) descends through `dA` 8 times and reads the
query itself as its leaf (the row's `64 − crOcc` zero words, then 8 words, then zeros), while a
position whose bit 7 or bit 0 is `1` reaches `dB`, which has no preimage (an erasure). A 65-byte
first preimage is not a node.
-/

namespace Lvm.X.ReadControls

open RecursionFast Lvm.X

/-- A digest with bytes `1 … 32`. -/
def dA : Digest := xDg ((List.range 32).map fun i => (i + 1).toUInt8)

/-- A digest with bytes `101 … 132`. -/
def dB : Digest := xDg ((List.range 32).map fun i => (i + 101).toUInt8)

/-- The node query `dA ‖ dB`. -/
def qAB : ByteArray := ⟨(dA.toList ++ dB.toList).toArray⟩

/-- The toy log: `qAB` answered `dA`. -/
def toyL : Log := [(qAB, dA)]

/-- The cap: `dA`, then `dB` 127 times. -/
def toyCap : List Digest := dA :: List.replicate 127 dB

/-- **Positive control**: position `0` reads `qAB` as its leaf: row words `0 … 28` are zero,
word `29` is bytes `1 … 8`, word `33` is bytes `101 … 108` (the right half), word `37` is past
the query (`0`). -/
theorem readRow_toy :
    (∀ t < 64 - crOcc, (readRow toyL toyCap 0).getD t 0 = 0) ∧
    (readRow toyL toyCap 0).getD 29 0 = decLE [1, 2, 3, 4, 5, 6, 7, 8] ∧
    (readRow toyL toyCap 0).getD 33 0 = decLE [101, 102, 103, 104, 105, 106, 107, 108] ∧
    (readRow toyL toyCap 0).getD 37 0 = 0 := by decide +kernel

/-- **Negative control**: the leaf's first word is not the row's first word; an unshifted
reading of the leaf would fail here. -/
theorem readRow_toy_shifted :
    (readRow toyL toyCap 0).getD 0 0 ≠ decLE [1, 2, 3, 4, 5, 6, 7, 8] := by decide +kernel

/-- **Negative controls**: bit 7 (the first step) or bit 0 (the last) set leads to `dB`, which
has no preimage; position `256` starts at cap node `dB`; a 65-byte first preimage stops the
descent. Each is an erasure. -/
theorem readRow_toy_erasure :
    xLeafBytes toyL toyCap 128 = none ∧ xLeafBytes toyL toyCap 1 = none ∧
    xLeafBytes toyL toyCap 256 = none ∧
    xLeafBytes [(⟨(dA.toList ++ dA.toList ++ [0]).toArray⟩, dA)] toyCap 0 = none := by
  decide +kernel

/-- The erasures read as zeros. -/
theorem readRow_toy_zero : readRow toyL toyCap 128 = List.replicate 64 0 :=
  readRow_erasure readRow_toy_erasure.1

end Lvm.X.ReadControls
