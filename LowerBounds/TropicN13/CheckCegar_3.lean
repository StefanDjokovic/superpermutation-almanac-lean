import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_cegar_3 : checkRangeAux 318 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 76 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
