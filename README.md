# Pure-Kernel Lean 4.35.0 Proof of `S(13) ≥ 6,746,627,287`

This repository contains a standalone, **100% pure-kernel** Lean `v4.35.0` formalization of the world-record superpermutation lower bound:

$$S(13) \ge 6{,}746{,}627{,}287$$

exported as the official Superpermutation Almanac theorem in `AlmanacSolution.lean`:

```lean
AlmanacSubmission.lower_thirteen : Almanac.LowerBoundAt 13 6746627287
```

It improves over the previous `S(13)` bounds:
- `+3` above `6,746,627,284` (Level-1 `TropicCEGAR-Macro`),
- `+103` above `6,746,627,184`,
- `+239` above Halfar's `6,746,627,048`.

## Verification Guarantees

- **Zero `native_decide`**, **zero `sorry`** (outside the untouched official `AlmanacChallenge.lean`), **zero `#eval`**, **zero custom tactics/macros/syntax/FFI**.
- `#print axioms AlmanacSubmission.lower_thirteen`:
  ```text
  [propext, Classical.choice, Quot.sound]
  ```
- **Toolchain & Mathlib:** `leanprover/lean4:v4.35.0` with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- **Repository footprint (excluding `.lake/`):** `43.3 MiB` (`< 9%` of the 500 MiB cap), max `.lean` file `3,536` lines (`<< 10,000` line cap).

## Mathematical & Kernel Architecture

The proof bridges a **Level-2 `TropicCEGAR`** dual-potential certificate directly into Halfar's kernel-proved **Theorem C** (`LowerBounds/SBridgeTheoremC.lean`) at parameters:

- `(k, c_n, b_n, q) = (13, 1474, 68966, 8953)`, `A = 2·q·5 - c_n = 88056`, `boundC 13 1474 68966 8953 = 6,746,627,287`.
- **Level-2 Run-Length Alphabet:** `D_track = 3`, `R_max = 7`, `144` valid Level-1 tokens (`idA = 127` = `(9, 2, 4)`), `1,042` valid Level-2 tokens `(r, s1)`, with `10` tracked long symbols and `2` tracked pair symbols.
- **BPE `S_13` Group-Homomorphism Compression:** `3,283` forbidden CEGAR words are compressed via a `944`-node BPE DAG (max depth `14`) storing exact 52-bit 1-based `S_13` group elements (`compose13`), verified against `walkWordFast 13` in `LowerBounds/TropicL2Sound.lean`.
- **O(1) Pure-Kernel AC Automaton:** `573,189` BFS-reindexed alive Aho–Corasick trie states packed into `BigNat` chunks (`DataSt0..7`, `DataGo0..15`) with balanced `@Bool.rec` dispatchers, verified across `81` zero-Mathlib `decide +kernel` shards (`CheckBasic`, `CheckForb1_0..3`, `CheckCegar_0..7`, `CheckSmall_0..3`, `CheckStates_0..63`).

## Build & Verify

```bash
lake build AlmanacSolution
```

Measured total CPU time for all 81 certificate shards + `Data*` + `AlmanacSolution`: ~`2,690` CPU-seconds (`~27 min` wall clock throttled to 2 threads; `~5.5–6.5 min` on an 8-core machine).
