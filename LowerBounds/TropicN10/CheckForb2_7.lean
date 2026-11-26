import LowerBounds.TropicN10.Data

namespace SuperpermLowerBounds.Tropic.TropicN10
open SuperpermLowerBounds.Tropic

theorem chk_forb2_7 : checkRangeAux 140 (checkForb2Sym cert) 5 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN10
