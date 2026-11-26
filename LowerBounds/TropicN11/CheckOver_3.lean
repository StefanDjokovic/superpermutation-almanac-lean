import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_over_3 : checkRangeChunked 24576 3436 (checkOverridesState cert) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
