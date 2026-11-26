import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_cegar_5 : checkRangeAux 221 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 20 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
