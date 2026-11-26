import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_forb2_5 : checkRangeAux 120 (checkForb2Sym cert) 11 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
