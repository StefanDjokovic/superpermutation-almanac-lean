import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_cegar_3 : checkRangeAux 172 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 19 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
