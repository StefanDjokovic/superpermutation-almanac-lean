import LowerBounds.TropicN10.Data

namespace SuperpermLowerBounds.Tropic.TropicN10
open SuperpermLowerBounds.Tropic

theorem chk_over_0 : checkRangeChunked 0 494 (fun u => checkRangeChunked 0 145 (overrideCheck cert u)) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN10
