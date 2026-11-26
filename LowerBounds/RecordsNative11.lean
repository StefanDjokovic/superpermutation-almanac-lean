import LowerBounds.SearchFast

/-!
# Compiled window-search certificate for `n = 11`: `S(11) ≥ 43,917,905`

Parameters for Halfar's Theorem C (`ConditionsC 11 2313 111620 25000`):
`cn = 2313`, `bn = 111620`, `q = 25000`, `A = 197687`, `q2 = 50000`,
`C1 = 350000`, `C2 = 400000`, `fuel = 5760`.
Evaluated via `native_decide` on the precompiled `S.searchFast` engine.
-/

namespace SuperpermLowerBounds
namespace S

theorem searchFast_11_43917905 :
    searchFast 11 197687 50000 350000 400000 111620 5760 = false := by
  native_decide

end S
end SuperpermLowerBounds
