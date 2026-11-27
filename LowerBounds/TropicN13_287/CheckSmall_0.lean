import LowerBounds.TropicN13_287.Cert

namespace SuperpermLowerBounds.TropicL2.N13_287
theorem chk_root : checkRoot cert = true := by decide +kernel
theorem chk_pair : checkRangeAux 0 (checkPair cert) 2 = true := by decide +kernel
theorem chk_maxTr : checkRangeAux 0 (checkMaxTr cert) 10 = true := by decide +kernel
theorem chk_rootS1_0 : checkRangeChunked 0 36 (checkRootS1 cert) = true := by decide +kernel
end SuperpermLowerBounds.TropicL2.N13_287
