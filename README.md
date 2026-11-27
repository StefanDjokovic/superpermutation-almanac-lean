# Superpermutation lower bound $S(7) \ge 5{,}900$ in Lean 4

A complete, Almanac-compliant Lean 4 (`v4.35.0`) formalization proving **`Almanac.LowerBoundAt 7 5900`**: every superpermutation on 7 symbols has length at least **5,900**.

This repository extends the official Almanac `5,899` formalization (`jhalfar/superpermutations`, commit `64ab6a7`) to the full `5,900` proof (cost 135 accounting, Table $T'$, Theorem $K$, and Joint Statements $S_1 \dots S_5$), adding kernel-verified dominance pruning, a 3-row greatest-fixed-point upper bound ($U_3$), the Dual Cycle Lemma on $H = 70 \dots 83$, and unboxed compiled Lean 4 search engines (`FastK16Search`, `FastJ16Search`).

> **Runtime & Judge Transparency Note:** Every soundness bridge, combinatorial reduction, dominance table, and assembly theorem is **100% kernel-checked** (`[propext, Classical.choice, Quot.sound]` only, zero `sorry`). The 60 finite search evaluations use `native_decide` (compiled pure Lean 4, zero `@[extern]`/C FFI) and completed a full end-to-end build of `AlmanacSolution.olean` in **15 h 08 m wall-clock** on a 14-core Apple Silicon laptop. Because Theorem $K$ rows `K0`, `K1`, and `K2` alone take **12 h 05 m (79.9% of total runtime)**, a full clean rebuild currently **exceeds the Almanac judge's 2-hour automated re-evaluation cap on 8 CPUs**. See [Measured Build Timings](#measured-build-timings) and the [Open Speedup & Pure-Kernel Roadmap](#open-speedup--pure-kernel-roadmap) below.

---

## Statement

[`AlmanacSolution.lean`](AlmanacSolution.lean) proves:

| Statement | Meaning |
|---|---|
| `AlmanacSubmission.lower_seven : Almanac.LowerBoundAt 7 5900` | Every superpermutation on 7 symbols has length at least 5,900 |

`AlmanacDefs.lean`, `AlmanacStatement.lean`, and `AlmanacChallenge.lean` are the published Superpermutation Almanac scaffold files, unchanged.

---

## Mathematical Architecture & Kernel-Verified Accelerations

All mathematical reductions, pruning rules, and engine soundness proofs are **100% verified in the Lean 4 kernel** (no `sorry`, no `native_decide`, no `unsafe`, no `@[extern]`):

1. **Cost-135 Accounting & Configuration Reduction ([`LowerBounds/A15Final.lean`](LowerBounds/A15Final.lean), [`LowerBounds/F5900Joint.lean`](LowerBounds/F5900Joint.lean), [`LowerBounds/KFinal5900.lean`](LowerBounds/KFinal5900.lean), [`LowerBounds/J15Final5900.lean`](LowerBounds/J15Final5900.lean)):**
   - Connects Pantone's `Covers` to Almanac's `IsSuperpermutation` (`LowerLinks.lean`) and reduces $S(7) \ge 5{,}900$ to the absence of a standard configuration of cost $135$ (`A15.no_config_135`), combining `Caps`, `Profiles` (from `5,899`), Table $T'$, Theorem $K$, and Joint Statements $S_1 \dots S_5$.
2. **Reversal-Symmetric Local Dominance Pruning ([`LowerBounds/DomTables.lean`](LowerBounds/DomTables.lean), [`LowerBounds/DomSound.lean`](LowerBounds/DomSound.lean)):**
   - **$m = 3$ weight-3 shortcut dominance (440 motifs):** Any 3-row weight-3 subpath $P$ admitting a shorter valid replacement $P'$ ($m' \le 2$ rows) with identical entry/exit permutations, $C(P') \subseteq C(P)$, and $v(P') \ge v(P)$ cannot occur in a row-minimal counterexample (`FastSound.noM3_of_min_rows`).
   - **$m = 2$ weight-4 shortcut dominance (271 motifs):** Any 2-row weight-4 transition admitting a weight-3 replacement with $C(P') \subseteq C(P)$ and $v(P') \ge v(P)$ cannot occur when $v_s(x) \ge v_{s-1}(y)$ for $y \le x + 6$ (`FastSound.noW4_of_hlow`).
   - Both explicit witness tables are verified directly in the Lean kernel (`m3Witnesses_valid`, `w4Witnesses_valid`, axioms `[propext]` only), together with Rule JS (`K16.NoJS`).
3. **3-Row Greatest Fixed Point Upper Bound $U_3$ ([`LowerBounds/U3Sound.lean`](LowerBounds/U3Sound.lean)):**
   - Builds an exact 5,400-state greatest-fixed-point table `u3MinR` bounding the maximum remaining weight-3 rows reachable from any valid 3-row suffix under Rule JS and $m = 3$ dominance. Soundness is proved by well-founded induction (`FastSound.u3MinR_lt_nr`).
4. **Dual Cycle Lemma on $H = 70 \dots 83$ ([`LowerBounds/DualRingSearch.lean`](LowerBounds/DualRingSearch.lean), [`LowerBounds/DualRingSound.lean`](LowerBounds/DualRingSound.lean)):**
   - Applying `PS.cycle_lemma` to negated prefix deficits flips the ring invariant from $d T \le r H$ to $r H \le d T$ (`PS.ringCapRange_of_searchDual`). Combined with Theorem $K$'s `Dtab[0]`, this tightens ring caps on $H = 70 \dots 83$ (`TRdual`) in seconds and significantly shrinks `S2a1_hi` and `S3`.
5. **Unboxed Pure-Lean Compiled Search Engines ([`LowerBounds/FastK16Search.lean`](LowerBounds/FastK16Search.lean), [`LowerBounds/FastK16Sound.lean`](LowerBounds/FastK16Sound.lean), [`LowerBounds/FastJ16Search.lean`](LowerBounds/FastJ16Search.lean), [`LowerBounds/FastJ16Sound.lean`](LowerBounds/FastJ16Sound.lean)):**
   - 100% pure functional, structurally terminating Lean 4 implementations (compiled to native code via `SearchEngine` with `precompileModules = true`, zero `@[extern]`/C FFI, zero `unsafe`/`partial`/`Id.run`) that pack recursion state into unboxed `UInt64`/`UInt32`/`Int64` registers and flat `ByteArray` lookup tables.
   - Bit-exact completeness against the mathematical specifications `PS.SeqCapLt` and `J16.JV` is proved in the Lean kernel (`FastK16Sound.seqCap_of_fastK16`, `FastJ16Sound.jv_of_fastJ16`).
6. **Linearly Chained Sharded Evaluation ([`LowerBounds/F5900SmallNative.lean`](LowerBounds/F5900SmallNative.lean) .. [`LowerBounds/F5900K0_5Native.lean`](LowerBounds/F5900K0_5Native.lean), [`LowerBounds/F5900Native.lean`](LowerBounds/F5900Native.lean)):**
   - The 48 new `5,900` finite searches are organized into 23 linearly chained, Mathlib-free shard modules. Each shard uses Lean's `Task.spawn` parallelism (`KS.par`) over disjoint partition indices without oversubscription and caches cleanly as an `.olean`.

---

## Axiom Audit & Trust Boundary

Verified on Lean `leanprover/lean4:v4.35.0` with Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

### Soundness & Assembly Theorems (100% Pure Kernel)

Every soundness bridge and assembly theorem depends strictly on Lean's standard logical axioms:

| Theorem | Axioms (`#print axioms`) |
|---|---|
| `SuperpermLowerBounds.FastSound.m3Witnesses_valid` | `[propext]` |
| `SuperpermLowerBounds.FastSound.w4Witnesses_valid` | `[propext]` |
| `SuperpermLowerBounds.FastSound.noM3_of_min_rows` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.FastSound.noW4_of_hlow` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.FastSound.u3MinR_lt_nr` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.PS.ringCapRange_of_searchDual` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.FastK16Sound.seqCap_of_fastK16` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.FastJ16Sound.jv_of_fastJ16` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.K5900.tableT_of_fast` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.K5900.theoremK_of_fast` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.J5900.joint_of_fast` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.covers_5899_of_k16` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.covers_5900_of_caps` | `[propext, Classical.choice, Quot.sound]` |
| `SuperpermLowerBounds.covers_5900_of_joint` | `[propext, Classical.choice, Quot.sound]` |

### Final Theorem (`AlmanacSubmission.lower_seven`)

`#print axioms AlmanacSubmission.lower_seven` reports:
- Standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- **60 `native_decide` evaluation axioms** (`_native.native_decide.ax_1_1`), each corresponding 1-to-1 to a pure Boolean finite search returning `false`:
  - **12 inherited from `5,899`**: `K16.f0k` .. `K16.f5k` (`PK16F0Native`, `PK16F1Native`, `PK16Native`), `PS.ring` (`PRingNative`), `PS.prof14`, `PS.prof26`, `PS.prof34`, `PS.prof36`, `PS.prof4` (`PProfNative`).
  - **48 new `5,900` shards**: `F5900Shards.tr15`, `trdual_70` .. `trdual_83`, `c59`, `c62`, `c76`, `ring69`, `k8`, `k7`, `k6a`, `k6b`, `k5`, `k4`, `k3`, `k2_0` .. `k2_2`, `k1_0` .. `k1_4`, `k0_0` .. `k0_5`, `s5`, `s4`, `s3`, `s1`, `s2a1_lo`, `s2a1_hi`, `s2a2_0`, `s2a2_1`.
- **Zero** `sorryAx` (the only `sorry` in the repository is the untouched Almanac template `AlmanacChallenge.lean`), **zero** `unsafe`, **zero** `implemented_by` / `@[extern]`, **zero** `#eval`, **zero** custom macros/elaborators/syntax, **zero** `partial` functions.
- Every `.lean` file is at most `4,087` lines (well below the 10,000-line limit); total source size excluding `.lake/` is ~10 MiB.

---

## Measured Build Timings

Measured end-to-end on a 14-core Apple Silicon laptop (`lake build AlmanacSolution`, from `F5900SmallNative.olean` mtime `2026-11-26 21:19:40` to `AlmanacSolution.olean` mtime `2026-11-27 12:27:20`): **15 h 07 m 40 s (~15.1 hours wall-clock)**.

Because the 23 `F5900*Native` modules are chained linearly, each `.olean` timestamp delta gives the exact wall-clock duration of that shard (note that `F5900MedNative` overlapped briefly with the 12 inherited `5,899` base shards `PK16*Native` / `PRingNative` / `PProfNative`):

| Stage / Shard Module | Contents / Partition | Measured Wall-Clock | Share of Total |
|---|---|---:|---:|
| `F5900SmallNative` | `tr15`, `trdual_70..83`, `c59`, `k6a/b`, `k7`, `k8`, `s5` | `< 1 min` | `~0.1%` |
| `F5900MedNative` (+ `5,899` base shards) | `c62`, `c76`, `k5`, `s4`, `k4`, `ring69` | `11.3 min` | `1.2%` |
| `F5900K3Native` | Theorem $K$ row 3 (`0..199 / 199`) | `26.8 min` | `3.0%` |
| `F5900S1Native` | Joint $S_1$ (`0..199 / 199`) | `20.6 min` | `2.3%` |
| `F5900S2a1LoNative` | Joint $S_{2a1,\mathrm{lo}}$ (`0..199 / 199`) | `13.0 min` | `1.4%` |
| `F5900S2a1HiNative` | Joint $S_{2a1,\mathrm{hi}}$ (`0..199 / 199`) | `30.3 min` | `3.3%` |
| `F5900S3Native` | Joint $S_3$ (`0..199 / 199`) | `10.4 min` | `1.1%` |
| `F5900S2a2_0Native` | Joint $S_{2a2}$ (`0..100 / 199`) | `38.9 min` | `4.3%` |
| `F5900S2a2_1Native` | Joint $S_{2a2}$ (`100..199 / 199`) | `30.5 min` | `3.4%` |
| **Subtotal: Joint $S_1 \dots S_3$** | 6 shards | **143.8 min (2 h 24 m)** | **15.8%** |
| `F5900K2_0Native` | Theorem $K$ row 2 (`0..84 / 251`) | `27.0 min` | `3.0%` |
| `F5900K2_1Native` | Theorem $K$ row 2 (`84..168 / 251`) | `37.0 min` | `4.1%` |
| `F5900K2_2Native` | Theorem $K$ row 2 (`168..251 / 251`) | `92.3 min` | `10.2%` |
| **Subtotal: Theorem $K$ row 2 (`K2`)** | 3 shards | **156.3 min (2 h 36 m)** | **17.2%** |
| `F5900K1_0Native` | Theorem $K$ row 1 (`0..100 / 499`) | `30.0 min` | `3.3%` |
| `F5900K1_1Native` | Theorem $K$ row 1 (`100..200 / 499`) | `83.2 min` | `9.2%` |
| `F5900K1_2Native` | Theorem $K$ row 1 (`200..300 / 499`) | `109.3 min` | `12.0%` |
| `F5900K1_3Native` | Theorem $K$ row 1 (`300..400 / 499`) | `34.3 min` | `3.8%` |
| `F5900K1_4Native` | Theorem $K$ row 1 (`400..499 / 499`) | `90.9 min` | `10.0%` |
| **Subtotal: Theorem $K$ row 1 (`K1`)** | 5 shards | **347.7 min (5 h 48 m)** | **38.3%** |
| `F5900K0_0Native` | Theorem $K$ row 0 (`0..84 / 499`) | `19.6 min` | `2.2%` |
| `F5900K0_1Native` | Theorem $K$ row 0 (`84..167 / 499`) | `30.4 min` | `3.4%` |
| `F5900K0_2Native` | Theorem $K$ row 0 (`167..250 / 499`) | `41.6 min` | `4.6%` |
| `F5900K0_3Native` | Theorem $K$ row 0 (`250..333 / 499`) | `48.3 min` | `5.3%` |
| `F5900K0_4Native` | Theorem $K$ row 0 (`333..416 / 499`) | `16.4 min` | `1.8%` |
| `F5900K0_5Native` | Theorem $K$ row 0 (`416..499 / 499`) | `64.8 min` | `7.1%` |
| **Subtotal: Theorem $K$ row 0 (`K0`)** | 6 shards | **221.1 min (3 h 41 m)** | **24.4%** |
| `F5900Native` + `LowerLinks` + `AlmanacSolution` | Final kernel assembly | `0.7 min` | `0.1%` |
| **Total (`F5900SmallNative` $\to$ `AlmanacSolution`)** | **23 new shards + assembly** | **~908 min (15 h 08 m)** | **100%** |

**Key bottleneck:** Theorem $K$ rows `K0`, `K1`, and `K2` alone account for **12 h 05 m (79.9%)** of the entire build (`K0..K3` = **82.9%**), and `K1` alone takes **5 h 48 m (38.3%)**.

---

## Open Speedup & Pure-Kernel Roadmap

This proof is complete and machine-checked, but cutting `K0`/`K1`/`K2` by **10×–100×** would bring the entire rebuild well under the Almanac's 2-hour 8-CPU automated re-evaluation limit, and replacing `native_decide` would yield a 100% pure-kernel proof. High-leverage directions for contributors:

1. **Extend $U_3$ Lookahead to Weight-4 Transitions (`t < S`) and $m = 4$ Dominance:**
   - Currently `u3MinRBA` is only consulted once all weight-4 budget has been spent (`nt == ctx.S` in `FastK16Search.lean`). Adding a weight-4-aware greatest-fixed-point table (or a 4-row $m = 4$ dominance witness table verified by kernel `decide`, analogous to `DomTables.lean`) directly attacks `K1` (38.3%) and `K2` (17.2%).
2. **Eliminate Straggler Imbalance Across Partition Buckets:**
   - Within `K1` and `K2`, individual shards vary by $> 3\times$ (`K1_0`: 30 m vs `K1_2`: 109 m; `K2_0`: 27 m vs `K2_2`: 92 m) because `(q + 8192 * d) % nt` hash buckets have heavy-tailed subtree sizes and each shard waits for its slowest task. Using deeper split depth (`ds`), strided bucket assignment, or adaptive work-stealing across `nt` buckets reduces wall-clock tail latency immediately without changing soundness.
3. **Stronger Potential Tilts (`a, b, h`) & Two-Row Symmetry Breaking on `K0`/`K1`/`K2`:**
   - Tuning the rational tilt parameters `(a, b, h)` (or checking multiple linear potentials simultaneously at each node) and exploiting reversal symmetry on the initial rows can shrink the `K0`/`K1`/`K2` DFS trees by an order of magnitude.
4. **Replacing `native_decide` with Pure-Kernel Certificates (`decide +kernel`):**
   - For high-branching searches like `K0..K3`, an offline solver can emit either (a) a compact pruned-DFS certificate tree or (b) a finite-state dual potential / tropical-automaton witness (`phi[s]` on a finite Aho-Corasick / suffix automaton) whose validity is checked in linear time by `decide +kernel` with zero `native_decide` axioms.

---

## Build & Verification Instructions

Requires Lean `leanprover/lean4:v4.35.0` (managed automatically by `elan` via `lean-toolchain`) and Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`.

### Full Build (from scratch)

```bash
lake exe cache get
lake build AlmanacSolution
```

*Note:* A full clean rebuild takes ~15 hours wall-clock on a 14-core machine (longer on fewer cores). Because the 23 `F5900*Native` shards are linearly chained, an interrupted build resumes cleanly from the last completed `.olean` shard without losing prior progress.

### Checking Only the Kernel Soundness & Assembly Proofs (Fast, `< 2 min`)

To verify every mathematical reduction, dominance table, and engine soundness proof purely in the Lean kernel (without running the `native_decide` search shards):

```bash
lake exe cache get
lake build LowerBounds.DomSound LowerBounds.U3Sound LowerBounds.DualRingSound \
           LowerBounds.FastK16Sound LowerBounds.FastJ16Sound \
           LowerBounds.KFinal5900 LowerBounds.J15Final5900 LowerBounds.F5900Joint
```

### Axiom & External Kernel Verification

Once `AlmanacSolution` is built, verify the exact theorem signature and axiom footprint:

```bash
lake env lean --stdin <<'EOF'
import AlmanacSolution
#check (AlmanacSubmission.lower_seven : Almanac.LowerBoundAt 7 5900)
#print axioms AlmanacSubmission.lower_seven
EOF
```

To independently replay the kernel environment with `lean4checker`:

```bash
lake env lean4checker AlmanacSolution
```

*(Note: `lean4checker` verifies all kernel proof terms and definitions modulo the 60 `native_decide` axioms listed by `#print axioms` above.)*

---

## Sources and Licences

Built upon:
- [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations) (commit `64ab6a7`, Apache-2.0),
- [superpermutations-hunter](https://github.com/urdvr/superpermutations-hunter) (commit `d452221`, Apache-2.0),
- [superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80) (commit `c8fb7ff`, Apache-2.0),
- [superpermutations-preimage-chain-lower-bounds](https://github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds) (commit `8474c74`, CC BY 4.0).

`AlmanacDefs.lean`, `AlmanacStatement.lean`, and `AlmanacChallenge.lean` are the Almanac's files, unchanged.
