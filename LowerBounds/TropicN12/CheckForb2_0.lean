import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_forb2_0 : checkRangeAux 0 (checkForb2Sym cert) 24 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
