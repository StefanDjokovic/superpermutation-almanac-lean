# Superpermutation Almanac: `Almanac.AsymptoticUpper 0` (`S(n) = n! + (n-1)! + (n-2)! + o((n-3)!)`)

This repository contains a **100% pure-kernel, self-contained** Lean 4.35.0 formal proof closing the asymptotic $(n - 3)!$ upper-bound constant for superpermutations all the way down to **`0`**:

```lean
theorem AlmanacSubmission.asymptotic_upper : Almanac.AsymptoticUpper 0
-- For every ε > 0, for all sufficiently large n, there exists a superpermutation w on n symbols with
--   w.length ≤ n! + (n - 1)! + (n - 2)! + ε · (n - 3)!
```

```lean
#print axioms AlmanacSubmission.asymptotic_upper
-- 'AlmanacSubmission.asymptotic_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **Zero `sorry`**, **zero `native_decide`**, **zero `#eval`**, **zero custom tactics/macros/elaborators**
- **Total source size:** `~571 KiB` across `11` Lean files (max file `2,875` lines)
- **Build & check time:** `~30 seconds` on 1 core (builds completely from scratch on Lean 4.35.0 + Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`)

---

## Proof Architecture (`AsymptoticZero/`)

1. **`AsymptoticZero/Eulerian.lean` (`480` lines):** Hierholzer's theorem for finite balanced directed multigraphs and `word_of_bags` concatenating Eulerian bags into a single word.
2. **`AsymptoticZero/SliceModel.lean` (`1,214` lines):** Exact `F/S/D` pure selection slice model on `K = n - 2` symbols, `F_3(K + 2) + Q` total slice-body length identity, connector-cycle edges `connCycleEdges`, and full `Almanac.IsSuperpermutation (K + 2)` coverage theorem.
3. **`AsymptoticZero/WalkW6m.lean` (`1,236` lines — Lemma 1):** Universal loop-disjoint pure-`F/S` walk $W_{6m} = (F^{6m-3} S)^{4m}$ for every $m \ge 1$ with length $4m(6m - 2)$, charge $Q = 8m$, and exact trail count $\gcd(6m - 1, 4m(6m - 4)) = 1$.
4. **`AsymptoticZero/BlockEmbed.lean` (`1,643` lines — Lemma 2):** Direct slot-pinning $r$-layer composition `iterW6mLift` on $K_0 = 6mr$ symbols with uniform block-diagonal symmetry fiber counts, exact `'S'`-row bound, and exponentially decaying `'D'`-loop fraction $d_{6m}^r$.
5. **`AsymptoticZero/DLoopBags.lean` (`741` lines — Lemma 4):** Canonical `'D'`-loop aggregation bags via $w_0 = 6mr$ giving exact `2 d_{6m}^r (K - 1)!` closure + concatenation cost.
6. **`AsymptoticZero/LayerSliceGraph.lean` (`1,703` lines — Lemma 3, Part 1) & `AsymptoticZero/StarsAndBars.lean` (`2,874` lines — Lemma 3, Part 2):** Exact Stars-and-Bars single-`z`-cycle component theorem proving every layer $j$ connects all lifted walk trails into at most $(K - 6m)!$ components, so zero-overlap concatenation across all $r$ layers costs $O((K - 6m)! / (K - 2)!) = o((n - 3)!)$.
7. **`AsymptoticZero/Main.lean` (`350` lines):** Combines all walk and `'D'`-loop bags with explicit constructive $\varepsilon/3 + \varepsilon/3 + \varepsilon/3$ parameter selection (`T := 3 * ε.den + 1`, `m := T`, `r := 2 * T * Db + 1`, `N := max (r * 6 * m + 3) (T * r + 4)`) to prove `Almanac.AsymptoticUpper 0`.

---

## Build & Verify

```bash
lake build AlmanacSolution
```
