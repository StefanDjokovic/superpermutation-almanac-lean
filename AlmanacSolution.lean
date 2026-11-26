-- Pure-kernel (`decide +kernel`, zero `native_decide`, zero `sorry`) lower bounds via
-- `TropicCEGAR-Macro` certificates bridged to Theorem C (`LowerBounds/TropicSound.lean`).
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 11 symbols has length at least 43,917,905. -/
theorem lower_eleven : Almanac.LowerBoundAt 11 43917905 := LowerLinks.lower_eleven

/-- Every superpermutation on 12 symbols has length at least 522,622,407. -/
theorem lower_twelve : Almanac.LowerBoundAt 12 522622407 := LowerLinks.lower_twelve

/-- Every superpermutation on 13 symbols has length at least 6,746,627,284. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627284 := LowerLinks.lower_thirteen

end AlmanacSubmission
