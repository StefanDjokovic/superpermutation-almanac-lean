import LowerBounds.TropicN10.Data

namespace SuperpermLowerBounds.Tropic.TropicN10
open SuperpermLowerBounds.Tropic

theorem chk_forb2_3 : checkRangeAux 60 (checkForb2Sym cert) 20 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN10
