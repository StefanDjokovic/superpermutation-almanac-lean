import LowerBounds.TropicN10.Data

namespace SuperpermLowerBounds.Tropic.TropicN10
open SuperpermLowerBounds.Tropic

theorem chk_cegar_0 : checkRangeAux 0 (fun fid => wordCollides cert.k (expandWord cert.symInfo (cert.cegarForb fid))) 22 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN10
