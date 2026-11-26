import LowerBounds.SearchFast

/-!
# Compiled window-search certificate for `n = 13`: `S(13) ≥ 6,746,627,184`

Parameters for Halfar's Theorem C (`ConditionsC 13 408 9376 2500`):
`cn = 408`, `bn = 9376`, `q = 2500`, `A = 24592`, `q2 = 5000`,
`C1 = 45000`, `C2 = 50000`, `fuel = 3450`.
Evaluated via `native_decide` on the precompiled `S.searchFast` engine.
-/

namespace SuperpermLowerBounds
namespace S

theorem searchFast_13_6746627184 :
    searchFast 13 24592 5000 45000 50000 9376 3450 = false := by
  native_decide

end S
end SuperpermLowerBounds
