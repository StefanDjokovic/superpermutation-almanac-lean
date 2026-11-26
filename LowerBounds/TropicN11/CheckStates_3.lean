import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_states_3 : checkRangeChunked 24576 3436 (stateCheck cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
