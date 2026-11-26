import LowerBounds.TropicN10.Data

namespace SuperpermLowerBounds.Tropic.TropicN10
open SuperpermLowerBounds.Tropic

theorem chk_states_0 : checkRangeChunked 0 494 (stateCheck cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN10
