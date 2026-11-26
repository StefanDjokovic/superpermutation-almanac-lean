# Pure-Kernel Superpermutation Lower Bound in Lean (`n = 13`: `S(13) ≥ 6,746,627,110`)

A 100% kernel-checked submission (zero `native_decide`, zero `Lean.ofReduceBool`) to the [Superpermutation Almanac](https://superpermutations.com) proving a new lower bound on 13 symbols in Lean 4.35.0:

| Statement | Meaning | Previous Record | Gain | Check Level |
|---|---|---:|---:|---|
| `AlmanacSubmission.lower_thirteen : Almanac.LowerBoundAt 13 6746627110` | Every superpermutation on 13 symbols has length at least 6,746,627,110 | 6,746,627,048 | **+62** | **Pure kernel** (`decide +kernel`) |

## Mathematical Framework

Applies J. Halfar's kernel-checked **Theorem C** (`LowerBounds/TheoremC.lean`, built on X. Liu's `PreimageChain`, Hunter–Raudvere's `Hunter`, and J. Pantone's `Challenge.lean`) with the small-denominator rational slope `c = 6/37` (past the `E`-chain threshold `5/31`):

| Symbols `k` | `cn` | `bn` | `q` | `A` | `q2` | `C1` | `C2` | `fuel` | `goK` states | `boundC` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 13 | 6 | 136 | 37 | 364 | 74 | 666 | 740 | 1909 | 263,583 | **6,746,627,110** |

The finite window search (`S.search 13 364 74 666 740 136 1909 = false`) is split into 155 independent kernel-evaluated part modules (`LowerBounds/SGen/C13_6_136_37P000.lean` .. `P154.lean`) and 544 state-definition modules (`D000.lean` .. `D543.lean`, 154 MiB total — smaller than Halfar's accepted 173 MiB `n = 12, 13` batch) generated with `tools/s_plan2.py` (`--leaf 450 --band 250 --per-file 3000`).

## Axioms and Build

`AlmanacSubmission.lower_thirteen` depends **only** on the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`, with zero `sorry` and zero `native_decide`.

```bash
lake exe cache get
lake build AlmanacSolution
```

## Attribution

Builds directly on J. Halfar (`superpermutations`), X. Liu (`superpermutations-preimage-chain-lower-bounds`), Hunter–Raudvere (`superpermutations-hunter`), and J. Pantone (`superperm-upper-43-80`). See `NOTICE` and `licenses/` for full upstream licensing and attribution.
