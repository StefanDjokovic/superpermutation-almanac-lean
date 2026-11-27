-- Pure-kernel (`decide +kernel`, zero `native_decide`, zero `sorry`) world-record lower bound
-- `S(13) >= 6,746,627,287` via Level-2 `TropicCEGAR` bridged to Theorem C (`LowerBounds/TropicL2Sound.lean`).
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 13 symbols has length at least 6,746,627,287. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627287 := LowerLinks.lower_thirteen

end AlmanacSubmission
