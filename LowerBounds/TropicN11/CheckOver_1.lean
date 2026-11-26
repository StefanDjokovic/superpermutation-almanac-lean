import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_over_1 : checkRangeChunked 8192 8192 (checkOverridesState cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
