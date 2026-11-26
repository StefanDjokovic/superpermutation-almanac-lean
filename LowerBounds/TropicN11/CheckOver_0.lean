import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_over_0 : checkRangeChunked 0 8192 (checkOverridesState cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
