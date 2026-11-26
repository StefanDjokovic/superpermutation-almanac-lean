import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_states_1 : checkRangeChunked 8192 8192 (stateCheck cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
