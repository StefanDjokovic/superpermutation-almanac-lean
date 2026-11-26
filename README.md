# Superpermutation Almanac Lower Bound: `S(10) >= 4,033,380` (100% Pure Kernel, Zero `native_decide`)

This repository contains a **100% pure-kernel** Lean 4.35.0 formal proof of a new Superpermutation Almanac lower-bound world record:

- **`AlmanacSubmission.lower_ten : Almanac.LowerBoundAt 10 4033380`** (`+1` over the previous record `4,033,379`)

Every finite verification step uses **`decide +kernel`** (zero `native_decide`, zero `Lean.ofReduceBool`, zero `sorry`, zero `#eval`, zero custom tactics/macros/elaborators).

```lean
#print axioms AlmanacSubmission.lower_ten
-- 'AlmanacSubmission.lower_ten' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Mathematical Overview (`TropicCEGAR-Macro` -> Theorem C)

Instead of exhaustively searching billions of DFS nodes in `SSearch` (which explodes near the critical `E`-chain slope `c_E(10) = 1/4`), we prove the exact `Theorem C` window bound (`ModelStatement 10 1 28 4`) using a **zero-tree-search tropical dual potential certificate** over a finite Aho–Corasick macro automaton:

1. **Macro Alphabet Compression:** Consecutive full weight-3 `E`-pieces `(0, E)^m` followed by a transition `(d, t)` (`m <= k - 3 = 7`) are grouped into macro transitions, with a sound `RESET(d >= D_track + 1)` edge back to the root state `0` covering all untracked larger deficits (`D_track = 4`).
2. **Exact Self-Colliding Forbidden Words:** A finite list of forbidden words (`29` CEGAR words + `3,808` active length-2 forbidden macro pairs + exact base collision lemmas) are proved to self-collide in $S_{10}$ starting from the canonical identity $1$-cycle `idc 10` and lifted to arbitrary starting states by $S_{10}$-equivariance.
3. **Exact Integer Dual Potential ($\phi$):** An exact integer potential `phi : State -> Nat` over only **`494` DFA states** (`cn = 1, bn = 28, q = 4, A = 27`) satisfies the exact telescoping inequality along every alive transition, proving every valid collision-free `ChainC.IsWindow` has bounded excess `<= bn = 28`.
4. **Soundness Bridge (`LowerBounds/TropicSound.lean`):** A pure-kernel induction (~1,673 lines, axioms strictly `[propext, Classical.choice, Quot.sound]`) bridges the verified DFA + potential table directly into Halfar's unmodified `LowerBounds/SBridgeTheoremC.lean` (`covers_length_ge_boundC_of_model`), establishing `S(10) >= 4,033,380`.

---

## Repository Footprint & Build Instructions

- **Lean toolchain:** `leanprover/lean4:v4.35.0`
- **Mathlib revision:** `56a005855ea17e0b0958f73ec801ae140b0a1679`
- **Total source size:** `~3.4 MiB` (`15` certificate files in `LowerBounds/TropicN10/`, max file `4,736` lines)
- **Verification time:** `~9 min` single-core CPU (`< 4 min` wall-clock on multi-core machines)

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
- New contributions: `LowerBounds/TropicSound.lean`, `LowerBounds/TropicN10/`, `LowerLinks.lean`, `AlmanacSolution.lean`
