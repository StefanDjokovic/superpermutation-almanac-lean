import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_forb2_0 : checkRangeAux 0 (checkForb2Sym cert) 24 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
