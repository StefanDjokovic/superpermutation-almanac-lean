import LowerBounds.TropicN10.Data

namespace SuperpermLowerBounds.Tropic.TropicN10
open SuperpermLowerBounds.Tropic

theorem chk_forb2_5 : checkRangeAux 100 (checkForb2Sym cert) 20 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN10
