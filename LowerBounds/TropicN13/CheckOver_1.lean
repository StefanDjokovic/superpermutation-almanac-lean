import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_over_1 : checkRangeChunked 8192 8192 (checkOverridesState cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
