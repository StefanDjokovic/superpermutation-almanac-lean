import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_states_0 : checkRangeChunked 0 8192 (stateCheck cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
