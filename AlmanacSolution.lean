-- Pure-kernel (`decide +kernel`, zero `native_decide`, zero `sorry`) lower bounds via
-- `TropicCEGAR-Macro` certificates bridged to Theorem C (`LowerBounds/TropicSound.lean`).
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 10 symbols has length at least 4,033,380. -/
theorem lower_ten : Almanac.LowerBoundAt 10 4033380 := LowerLinks.lower_ten

end AlmanacSubmission
