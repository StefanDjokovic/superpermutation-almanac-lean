import LowerBounds.SearchFast

/-!
# Compiled window-search certificate for `n = 12`: `S(12) ≥ 522,622,404`

Parameters for Halfar's Theorem C (`ConditionsC 12 439 29260 10000`):
`cn = 439`, `bn = 29260`, `q = 10000`, `A = 89561`, `q2 = 20000`,
`C1 = 160000`, `C2 = 180000`, `fuel = 7440`.
Evaluated via `native_decide` on the precompiled `S.searchFast` engine.
-/

namespace SuperpermLowerBounds
namespace S

theorem searchFast_12_522622404 :
    searchFast 12 89561 20000 160000 180000 29260 7440 = false := by
  native_decide

end S
end SuperpermLowerBounds
