import LowerBounds.TropicN13_287.Cert

namespace SuperpermLowerBounds.TropicL2.N13_287
theorem chk_cegarWit_5 : checkRangeChunked 2051 411 (cegarWitCheck cert) = true := by decide +kernel
theorem chk_cegarLeaf_5 : checkRangeChunked 2051 411 (cegarLeafCheck cert) = true := by decide +kernel
end SuperpermLowerBounds.TropicL2.N13_287
