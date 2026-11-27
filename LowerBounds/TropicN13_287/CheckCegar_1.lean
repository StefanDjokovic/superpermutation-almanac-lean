import LowerBounds.TropicN13_287.Cert

namespace SuperpermLowerBounds.TropicL2.N13_287
theorem chk_cegarWit_1 : checkRangeChunked 410 410 (cegarWitCheck cert) = true := by decide +kernel
theorem chk_cegarLeaf_1 : checkRangeChunked 410 410 (cegarLeafCheck cert) = true := by decide +kernel
end SuperpermLowerBounds.TropicL2.N13_287
