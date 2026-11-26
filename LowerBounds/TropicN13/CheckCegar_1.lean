import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_cegar_1 : checkRangeAux 143 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 93 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
