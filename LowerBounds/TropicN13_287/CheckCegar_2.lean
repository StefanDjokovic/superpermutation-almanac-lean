import LowerBounds.TropicN13_287.Cert

namespace SuperpermLowerBounds.TropicL2.N13_287
theorem chk_cegarWit_2 : checkRangeChunked 820 411 (cegarWitCheck cert) = true := by decide +kernel
theorem chk_cegarLeaf_2 : checkRangeChunked 820 411 (cegarLeafCheck cert) = true := by decide +kernel
end SuperpermLowerBounds.TropicL2.N13_287
