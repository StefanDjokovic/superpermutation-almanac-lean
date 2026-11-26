# Superpermutation Lower Bounds in Lean (`n = 11, 12, 13`)

A batch submission to the [Superpermutation Almanac](https://superpermutations.com) proving three new lower bounds in Lean 4.35.0:

| Statement | Meaning | Previous Record | Gain |
|---|---|---:|---:|
| `AlmanacSubmission.lower_eleven : Almanac.LowerBoundAt 11 43917905` | Every superpermutation on 11 symbols has length at least 43,917,905 | 43,917,904 | +1 |
| `AlmanacSubmission.lower_twelve : Almanac.LowerBoundAt 12 522622404` | Every superpermutation on 12 symbols has length at least 522,622,404 | 522,622,401 | +3 |
| `AlmanacSubmission.lower_thirteen : Almanac.LowerBoundAt 13 6746627184` | Every superpermutation on 13 symbols has length at least 6,746,627,184 | 6,746,627,048 | +136 |

## Mathematical Framework

All three bounds apply J. Halfar's kernel-checked **Theorem C** (`LowerBounds/TheoremC.lean`, built on X. Liu's `PreimageChain` library, Hunter–Raudvere's `Hunter` library, and J. Pantone's `Challenge.lean`), pushing the rational slope parameter `c = cn / q` past the `E`-chain threshold (`c > 1/11` at `n = 11`, `c > 2/46` at `n = 12`, `c > 5/31` at `n = 13`) so that every window of consecutive pieces in an exact weight-three chain satisfies

$$2r + 2(k - 4) + c\,\delta \le (k - 3)\,\delta + b.$$

| Symbols `k` | `cn` | `bn` | `q` | `A` | `q2` | `C1` | `C2` | `fuel` | `boundC` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 11 | 2313 | 111620 | 25000 | 197687 | 50000 | 350000 | 400000 | 5760 | **43,917,905** |
| 12 | 439 | 29260 | 10000 | 89561 | 20000 | 160000 | 180000 | 7440 | **522,622,404** |
| 13 | 408 | 9376 | 2500 | 24592 | 5000 | 45000 | 50000 | 3450 | **6,746,627,184** |

## Verification Architecture

* `LowerBounds/SearchFast.lean` (compiled via `WSearchEngine` with `precompileModules = true`): a zero-allocation `UInt64` bit-level + LIFO open-addressing hash-table implementation of Halfar's `S.search` window search.
* `LowerBounds/SearchFastEq.lean`: a standalone, **kernel-checked** (zero `sorry`, zero Mathlib imports) soundness proof `S.searchFast_sound` showing that for `5 ≤ k ≤ 15`, `S.searchFast ... = false → S.search ... = false`.
* `LowerBounds/RecordsNative11.lean`, `LowerBounds/RecordsNative12.lean`, `LowerBounds/RecordsNative13.lean`: the three independent `native_decide` search certificates (buildable in parallel).
* `LowerBounds/RecordsFinal.lean`, `LowerLinks.lean`, `AlmanacSolution.lean`: kernel-checked wiring through `S.searchFast_sound`, `S.runSearch_*`, `TheoremC`, and `Almanac.LowerBoundAt`.

## Axioms and Build

All three theorems in `AlmanacSolution.lean` depend only on the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) plus each certificate's `native_decide` axiom (`SuperpermLowerBounds.S.searchFast_*._native.native_decide.ax_1_1`), with zero `sorry`. The soundness bridge `SuperpermLowerBounds.S.searchFast_sound` depends on `[propext, Classical.choice, Quot.sound]` only.

Once `Hunter`/`PreimageChain`/`LowerBounds` are compiled, the three `native_decide` certificates run in ~55s total single-threaded (~10s for `n = 13`, ~22s for `n = 12`, ~23s for `n = 11`, or ~23s wall time in parallel).

```bash
lake build AlmanacSolution
```

## Attribution

This repository builds directly on:
* J. Halfar, `superpermutations` (Theorem C, `SSearch`, `SSound`, `SModel`, `SBridge`)
* X. Liu, `superpermutations-preimage-chain-lower-bounds` (`PreimageChain`)
* Hunter–Raudvere, `superpermutations-hunter` (`Hunter`)
* J. Pantone, `superperm-upper-43-80` (`Challenge.lean`)

See `NOTICE` and `licenses/` for full upstream licensing and attribution.
