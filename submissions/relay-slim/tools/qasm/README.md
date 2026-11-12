# qasm: placement records and program blobs from Lean

The node program `Q = Q_link ++ Q_sig ++ Q_arith` exists as Lean definitions and as data embedded
by the Rust prover. This tool generates that data from the definitions used by the certificate.
It reproduces all four shipped files byte for byte at this entry's stage S4, with shared position
tables, grinding, OOD openings on `C_main` and two opening levels on `C_rec`:

- `lean/LvmQAsmData8.lean` and `lean/LvmQAsmData20.lean`: `data8`, `data20 : QData`, the groups
  and committed-column placements used by the Lean program and its checks.
- `prover/src/lvm/q-p8.blob` and `prover/src/lvm/q-p20.blob`: the program and its tables' inputs
  in `LOOPIR1` format, embedded by `prover/src/lvm/stream.rs`.

`QAsmTool.lean` is the importable generator and dumper; `QAsmMain.lean` is its executable.
`qasm.py` builds and runs them outside the entry's root. `header.txt` supplies the comment at the
top of each generated Lean record. It preserves the shipped header's reference to an unpublished
assembler so that the bytes match; these tools are sufficient to regenerate the files.

## Running

You need Python 3, `elan`, and a built checkout of the pinned core repository, including its
package tree (`harness/org-setup.sh ORG`). The tool requires that checkout by path and reuses its
`lake-manifest.json`; it does not run `lake update` or fetch package caches.

From the entry's root:

```sh
python3 -I tools/qasm/qasm.py --org ORG --build /tmp/qasm --check
```

Options:

- `--build DIR`: the Lake tree, outside the entry's root. The driver writes its Lake files and
  links `entry` to `lean/` and `tool` to this directory, so builds read the current sources.
- `--out DIR`: generated files, default `BUILD/out`; this must also be outside the entry's root.
- `--sets P8,P20`: parameter sets in execution order; the default runs P8 first.
- `--header FILE`: record-module comment text, default `header.txt`.
- `--start shipped|empty`: the initial record, default `shipped`.
- `--max-iter N`: maximum iterations, default 8.
- `--check`: compare generated files with shipped files and report the first differing byte.

Exit status is 0 only when every requested set reaches a fixed point with the frozen numbers
and, with `--check`, every generated file matches. Otherwise it is 1, with a `FAILED` line for
each generation or comparison failure. Files can be written before a frozen-number mismatch is
reported; a run that does not reach a fixed point writes no files for that set.

To check convergence from an empty record and repeat generation into a separate directory:

```sh
python3 -I tools/qasm/qasm.py --org ORG --build /tmp/qasm \
  --out /tmp/qasm/empty --start empty --check
python3 -I tools/qasm/qasm.py --org ORG --build /tmp/qasm \
  --out /tmp/qasm/repeat --check
```

Use the default shipped start to reproduce this entry. `--start empty` is an optional diagnostic
for alternative fixed points; the reproduction checks here use the shipped seed at both sets.

## Inputs and construction

The generator imports the entry's program; it does not transcribe its circuit:

| Definition | Module under `lean/` |
|---|---|
| `QAsm.QT C D`, the program built from a record | `LvmQAsmProg` |
| `Har.qarithT`, `withPad`, table shapes and shapes-only arrays | `LvmQAsmArith2` |
| `cfg8`, `cfg20`, input regions, shared position classes and PoW fields | `LvmQAsmLay` |
| `QData`, `plOf`, `arrs`, `bspecs`, `bplOf` | `LvmQAsmTabs` |
| `CMain.freeLo8`, `CMain.freeLo20`, the free-region boundaries | `LvmLayout` |
| `autoGroups`, the grouping algorithm | `LvmM3Grp` |
| `qltData`, Q_link's static table | `LvmQLink` |
| `pubLanes`, the header's lane count | `LvmDecideM3` |
| `P8`, `P20`, the frozen numbers | `LvmParams` |
| `fitsR` and its table-counting functions | `LvmDecideM3Real` |

`Q_arith` checks the child's digest-only tape, its wiring sumcheck, the sponge, the bus, the
table sumcheck, the accumulator and the openings, including their PoW and OOD checks. The
generator calls `QAsm.QT`, the specified builder, so these details follow the imported Lean.
Likewise, `bspecs` supplies the shared position-lane classes and the PoW field class to the blob
dumper. The tool does not use the linear-time mirror `VF.QTF` in `LvmVFastQ` and can run while
that mirror's equality proofs need updating.

1. **Groups.** `mkData C Q` uses `autoGroups Q`: per row shape, pieces are taken largest first
   and partitioned by the binary decomposition of the shape's total rows.
2. **Placements.** Committed columns are listed in the record's field order: group columns in
   `Shape.committed` order, input-array finalize counts in `arrs` order, the written array's
   value column, then the `BITS` classes' committed columns. A stable sort by decreasing height
   places them back to back, starting at `freeLo C` rounded up to the largest column's height.
   Every height is a power of two, so every column is aligned. Exceeding `C_main` is an error.
3. **Fixed point.** The tool iterates `D ↦ mkData C (QT C D)` until all record fields repeat.
   From the shipped record, the first step reproduces it at both sets. Start from that record
   to reproduce the shipped files. `--start empty` explores convergence from another seed;
   reaching the shipped record from empty is not a requirement of reproduction.
4. **Blob.** The dump contains `LOOPIR1` (program), `M3B` (groups and input arrays), `BITS`
   (bit classes), `PUBX` (`qltData`) and `FREE` (the checksum input). Its grammar and consumer
   are `parse_blob` in `prover/src/lvm/loopir.rs` and `spec_tables` in `prover/src/lvm/m3.rs`.

The free-region boundary comes from the shared layout. At P20 it is 7,340,032. At P8 it is
1,574,912: the digest tape follows the sponge message columns and occupies the last 2,048 words
before the free region. Using just the end of those message columns would overlap the tape.
After alignment, the first group is placed at 7,340,032 for P20 and 1,638,400 for P8.

`QAsmTool.lean` marks the remaining encoding choices as **Tool logic**:

- the placement order described above;
- array kinds: public when public values are present, written for the BITS-output region at
  `obB C`, aliased otherwise;
- public-lane selectors: the prover inserts four statement lanes after `vk`, so header lane
  `i` selects lane `i` below 5 and `i + 4` thereafter; `PUBX` starts at `pubLanes + 4`;
- free BITS words: the class with `rd = false` receives the WOTS checksum of the message digest
  at `(sigIn C).md`, encoded as kind 0;
- the record and blob printers.

Byte reproduction checks these choices against the shipped files at both sets. For a changed
program, the entry's own Lean checks still decide whether the generated record is valid.

## Frozen numbers and padding

The tool computes the five values checked against the parameter record: `busDepth`,
`leafdecReads`, `tableRounds`, `tableEvals` and `pubTab`. These are the values at the shipped
fixed points:

| Quantity | P8 | P20 |
|---|---:|---:|
| Groups | 65 | 84 |
| Program blocks | 641 | 649 |
| Q's committed words | 2,862,540 | 4,726,504 |
| `busDepth` | 21 | 21 |
| `leafdecReads` | 1 | 1 |
| `tableRounds` | 16 | 16 |
| `tableEvals` | 2,522 | 2,851 |
| `pubTab` | 108 | 127 |

Each shape has one group per set bit in its total row count. Changing that count can change the
number of evaluations and the index of the public table. `busDepth` is the ceiling of the
base-two logarithm of the bus's push leaves; `tableRounds` is the largest sumcheck-table height.

The table phase reads the record it helps generate, so the iteration need not settle after a
program edit. `Har.withPad` stabilizes the body it wraps in `Har.qarithT`: bus, table sumcheck,
accumulator, ring switch, claims and openings. For each shape with `n` rows, `Har.roundUp6`
rounds up to a multiple of `2^(floor(log2(n)) - 5)`, with natural-number subtraction. The added
rows read zero cells. `muladd`, `lin`, `assert0` and `loadE` can be padded; `fixmul` and `readd`
cannot. Loop rows count once per iteration of the loop.

The padding does not cover `Q_link`, `Q_sig`, or the preceding tape, wiring and sponge gadgets
in `Har.phases47`. A change there directly changes a shape's total. Within the padded body,
added rows may fit in the existing slack, but crossing a rounding boundary can change the
record or cause a cycle. Run the generator after a change to determine its effect.

The unpadded body of `qarithT` is not exposed as a separate definition, so this tool does not
report per-shape slack. It can be observed by logging the existing `padSegs` result inside
`withPad` in a scratch copy, without restating the program. Verify that the instrumented copy
still reproduces all four files before using its counts.

At the shipped records, that observation gives these padding rows:

| Shape | P8 | P20 |
|---|---:|---:|
| `loadE E [K,K,K]` | 73 | 135 |
| `lin E [E,E]` | 37 | 218 |
| `muladd E [E,E,E]` | 127 | 835 |
| `muladd E [E,K,E]` | 14 | 206 |
| `lin K [K,K]` | 21 | 73 |
| `muladd K [K,K,K]` | 6 | 16 |
| Other shapes | 0 | 0 |

The padding occupies 3,576 committed words at P8 and 20,776 at P20. These counts describe
slack in the padded body, not a guarantee that an edit leaves the full record unchanged:
piece membership and addresses can also change.

## Changing the program

1. Edit the program in `lean/` and run this tool without `--check`.
2. Read the iteration and frozen-number diagnostics. If it settles, copy the generated record
   modules into `lean/` and the blobs into `prover/src/lvm/`. Set `header.txt` to the provenance
   appropriate for your entry before generating its final files.
3. If the frozen numbers differ, update the parameters in `lean/LvmParams.lean` and
   `prover/src/lvm/params.rs` and the facts that depend on them before adopting the new record.
   First choose the intended fixed point: an empty start can reach a different one. These values
   affect the proof's size and transcript. If the commitment layout changes, keep `LvmLayout`
   and its prover mirror consistent too.
4. Rebuild the entry, including its kernel decisions (`LvmQAsmFacts*`, `LvmFinDec`,
   `LvmQAsmHar*`). Update the fast mirror and its proofs (`VF.QF_eq`, `VF.QTF_eq`) as needed.
5. Rebuild the prover, which embeds the blobs.

If the iteration cycles, compare the group counts in its log, try `--start empty`, or revise
the program's padding. Increasing `--max-iter` helps a slow convergence but does not resolve
a cycle. This tool generates data; it does not choose new padding or parameter values.
