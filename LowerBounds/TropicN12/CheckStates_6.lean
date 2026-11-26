import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_states_6 : checkRangeChunked 49152 1556 (stateCheck cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
