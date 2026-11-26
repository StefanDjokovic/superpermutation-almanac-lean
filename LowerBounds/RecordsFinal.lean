import LowerBounds.SBridgeTheoremC
import LowerBounds.SModel
import LowerBounds.SRun
import LowerBounds.SearchFastEq
import LowerBounds.RecordsNative11
import LowerBounds.RecordsNative12
import LowerBounds.RecordsNative13

/-!
# Theorem C lower bounds for `n = 11, 12, 13`

Applies Halfar's kernel-checked `TheoremC` and `SSound` to the three verified window searches
in `LowerBounds.RecordsNative11`, `LowerBounds.RecordsNative12`, and `LowerBounds.RecordsNative13`
(bridged to `S.search` via `S.searchFast_sound`, checked by the kernel):

* `S(11) ≥ 43,917,905` (`c = 2313/25000`, `b = 111620/25000`)
* `S(12) ≥ 522,622,404` (`c = 439/10000`, `b = 29260/10000`)
* `S(13) ≥ 6,746,627,184` (`c = 408/2500`, `b = 9376/2500`)
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain SuperpermutationBounds

/-! ### 11 symbols: `S(11) ≥ 43,917,905` -/

theorem conditionsC_11_43917905 : ConditionsC 11 2313 111620 25000 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem boundC_11_43917905 : boundC 11 2313 111620 25000 = 43917905 := by decide

theorem modelStatement_11_43917905 : ModelStatement 11 2313 111620 25000 :=
  modelStatement_of_search (k := 11) (cn := 2313) (bn := 111620) (q := 25000)
    (A := 197687) (q2 := 50000) (C1 := 350000) (C2 := 400000) (fuel := 5760)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    S.runSearch_11
    (S.searchFast_sound (by decide) (by decide) S.searchFast_11_43917905)

theorem covers_length_ge_43917905 : ∀ w : List (Fin 11), Covers w → 43917905 ≤ w.length :=
  boundC_11_43917905 ▸
    covers_length_ge_boundC_of_model (by decide) conditionsC_11_43917905 modelStatement_11_43917905

/-! ### 12 symbols: `S(12) ≥ 522,622,404` -/

theorem conditionsC_12_522622404 : ConditionsC 12 439 29260 10000 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem boundC_12_522622404 : boundC 12 439 29260 10000 = 522622404 := by decide

theorem modelStatement_12_522622404 : ModelStatement 12 439 29260 10000 :=
  modelStatement_of_search (k := 12) (cn := 439) (bn := 29260) (q := 10000)
    (A := 89561) (q2 := 20000) (C1 := 160000) (C2 := 180000) (fuel := 7440)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    S.runSearch_12
    (S.searchFast_sound (by decide) (by decide) S.searchFast_12_522622404)

theorem covers_length_ge_522622404 : ∀ w : List (Fin 12), Covers w → 522622404 ≤ w.length :=
  boundC_12_522622404 ▸
    covers_length_ge_boundC_of_model (by decide) conditionsC_12_522622404 modelStatement_12_522622404

/-! ### 13 symbols: `S(13) ≥ 6,746,627,184` -/

theorem conditionsC_13_6746627184 : ConditionsC 13 408 9376 2500 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem boundC_13_6746627184 : boundC 13 408 9376 2500 = 6746627184 := by decide

theorem modelStatement_13_6746627184 : ModelStatement 13 408 9376 2500 :=
  modelStatement_of_search (k := 13) (cn := 408) (bn := 9376) (q := 2500)
    (A := 24592) (q2 := 5000) (C1 := 45000) (C2 := 50000) (fuel := 3450)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    S.runSearch_13
    (S.searchFast_sound (by decide) (by decide) S.searchFast_13_6746627184)

theorem covers_length_ge_6746627184 : ∀ w : List (Fin 13), Covers w → 6746627184 ≤ w.length :=
  boundC_13_6746627184 ▸
    covers_length_ge_boundC_of_model (by decide) conditionsC_13_6746627184 modelStatement_13_6746627184

end SuperpermLowerBounds
