import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_base : baseCheck cert.k = true := by decide +kernel

theorem chk_alpha : checkRangeAux 0 (fun m => checkRangeAux 0 (fun d => checkRangeAux 0 (fun t => alphaTripleCheck cert m d t) 5) 4) 10 = true := by decide +kernel

theorem chk_d1 : checkRangeChunked 0 131 (d1Check cert) = true := by decide +kernel

theorem chk_root : checkRangeChunked 0 131 (rootEdgeCheck cert) = true := by decide +kernel

theorem chk_pairs : checkRangeChunked 0 131 (fun s => checkRangeChunked 0 131 (pairDepth1Check cert s)) = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
