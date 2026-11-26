import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_forb2_4 : checkRangeAux 96 (checkForb2Sym cert) 24 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
