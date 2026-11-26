import LowerBounds.TropicN12.Data

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic

theorem chk_cegar_4 : checkRangeAux 191 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 30 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN12
