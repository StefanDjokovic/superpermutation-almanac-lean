import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_forb2_6 : checkRangeAux 144 (checkForb2Sym cert) 19 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
