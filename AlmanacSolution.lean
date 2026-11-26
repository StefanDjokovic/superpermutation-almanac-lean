-- Lower bounds for 11, 12, and 13 symbols from Halfar's Theorem C with newly pushed constants,
-- evaluating the compiled window search `S.searchFast` via `native_decide` and bridging
-- to `S.search` via the kernel-checked soundness proof `S.searchFast_sound`.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 11 symbols has length at least 43,917,905. -/
theorem lower_eleven : Almanac.LowerBoundAt 11 43917905 := LowerLinks.lower_eleven

/-- Every superpermutation on 12 symbols has length at least 522,622,404. -/
theorem lower_twelve : Almanac.LowerBoundAt 12 522622404 := LowerLinks.lower_twelve

/-- Every superpermutation on 13 symbols has length at least 6,746,627,184. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627184 := LowerLinks.lower_thirteen

end AlmanacSubmission
