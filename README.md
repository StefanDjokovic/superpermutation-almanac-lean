# Superpermutation Almanac Lower Bounds: `S(11) >= 43,917,905`, `S(12) >= 522,622,407`, `S(13) >= 6,746,627,284` (100% Pure Kernel, Zero `native_decide`)

This repository contains **100% pure-kernel** Lean 4.35.0 formal proofs of **three new Superpermutation Almanac lower-bound world records**, verified completely by the Lean kernel (`decide +kernel`, zero `native_decide`, zero `Lean.ofReduceBool`, zero `sorry`, zero `#eval`, zero custom tactics/macros/elaborators):

| $n$ | Theorem in `AlmanacSolution.lean` | Previous Live Record | Gain | Exact `Theorem C` Params `(cn, bn, q)` | Macro DFA States / CEGAR Words | Cert Size |
|---:|---|---:|---:|---|---:|---:|
| **11** | `AlmanacSubmission.lower_eleven : Almanac.LowerBoundAt 11 43917905` | `43,917,904` | **`+1`** | `(36, 2718, 389)` | `28,012` / `149` | `1.5 MiB` |
| **12** | `AlmanacSubmission.lower_twelve : Almanac.LowerBoundAt 12 522622407` | `522,622,401` | **`+6`** | `(203, 24408, 4596)` | `50,708` / `243` | `2.3 MiB` |
| **13** | `AlmanacSubmission.lower_thirteen : Almanac.LowerBoundAt 13 6746627284` | `6,746,627,048` | **`+236`** | `(40, 1696, 243)` | `27,868` / `458` | `1.6 MiB` |

```lean
#print axioms AlmanacSubmission.lower_eleven
#print axioms AlmanacSubmission.lower_twelve
#print axioms AlmanacSubmission.lower_thirteen
-- All three depend ONLY on: [propext, Classical.choice, Quot.sound]
```

---

## Mathematical & Kernel-Verification Overview (`TropicCEGAR-Macro` -> Theorem C)

Instead of exhaustive DFS tree search (`SSearch`) or multi-hundred-MiB replay trees, each bound is proved by a **zero-tree-search tropical dual potential certificate** over a finite Aho–Corasick macro automaton bridged directly into Halfar's unmodified kernel-proved `LowerBounds/SBridgeTheoremC.lean`:

1. **Macro Alphabet Compression & `RESET` Soundness:** Consecutive full weight-3 `E`-pieces `(0, E)^m` followed by `(d, t)` (`m <= k - 3`) are compressed into macro transitions, with a sound `RESET(d >= D_track + 1)` edge returning to the root state `0`.
2. **O(1) Failure-Link & Sparse-Override Verification (`LowerBounds/TropicSound.lean`, 2,235 lines):** Proves `statePref (stFail u) <:+ statePref u` by strong induction on `u`, replacing `O(V)` list suffix reconstruction with O(1) failure-link hops (`failIter`) and iterating only over the `2–3` active override symbols (`ovList`).
3. **O(1)-per-Piece Two-Point Collision Witnesses (`checkWitness`):** Proves `S.code P[j] = (S.rotl (k-1) (c/16) j) * 16 + c%16`, verifying every CEGAR collision in `O(i2)` piece hops with zero binary search trees and only `2` `S.canon` calls, lifted to arbitrary starting states via $S_k$-equivariance.
4. **Pure-GMP-`Nat` Shifted Potentials & Chunked `BigNat` Bit-Packed Tables:** Shifts all potentials by `bias : Nat` (eliminating unary `Int` reduction) and encodes the DFA state/override tables in chunked `BigNat` hex words (`Nat.div` / `Nat.pow` / `Nat.mod`), shrinking the entire three-record repository to **`~7.6 MiB`** (max file `2,236` lines; generated cert shards `<= 520` lines) and checking all three records in **`~8–10 minutes` wall-clock on an 8-core machine**.

---

## Build & Verify

- **Lean toolchain:** `leanprover/lean4:v4.35.0`
- **Mathlib revision:** `56a005855ea17e0b0958f73ec801ae140b0a1679`

```bash
lake build AlmanacSolution
```

---

## Credits & Upstream Libraries

Built on the Superpermutation Almanac Lean formalization stack:
- Jay Pantone (`Challenge.lean`, `AlmanacDefs.lean`)
- Hunter & Raudvere (`Hunter/`)
- Xiaolong Liu (`PreimageChain/`)
- Jan Halfar (`Superperm/`, `LowerBounds/SModelDef.lean`, `LowerBounds/ChainCapacityC.lean`, `LowerBounds/TheoremCCore.lean`, `LowerBounds/SBridgeTheoremC.lean`)
- New contributions: `LowerBounds/TropicSound.lean`, `LowerBounds/TropicN11/`, `LowerBounds/TropicN12/`, `LowerBounds/TropicN13/`, `LowerLinks.lean`, `AlmanacSolution.lean`
