import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_forb2_0 : checkRangeAux 0 (checkForb2Sym cert) 24 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
