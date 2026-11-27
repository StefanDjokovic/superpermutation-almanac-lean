import LowerBounds.TropicN13_287.Cert

namespace SuperpermLowerBounds.TropicL2.N13_287

theorem chk_base : baseCheckL2 cert = true := by decide +kernel
theorem chk_alpha1 : checkRangeAux 0 (fun m => checkRangeAux 0 (fun d => checkRangeAux 0 (fun t => alpha1TripleCheck cert m d t) 5) 4) 11 = true := by decide +kernel
theorem chk_l1Elem : checkRangeChunked 0 144 (l1ElemCheck cert) = true := by decide +kernel
theorem chk_l2Single : checkRangeAux 0 (fun r => checkRangeChunked 0 144 (l2SingleCheck cert r)) 8 = true := by decide +kernel
theorem chk_bpe : checkRangeChunked 0 944 (bpeElemCheck cert) = true := by decide +kernel

end SuperpermLowerBounds.TropicL2.N13_287
