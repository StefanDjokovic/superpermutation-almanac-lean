import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_states_3 : checkRangeChunked 24576 3292 (stateCheck cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
