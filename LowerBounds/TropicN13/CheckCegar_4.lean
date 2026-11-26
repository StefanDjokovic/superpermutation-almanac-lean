import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_cegar_4 : checkRangeAux 394 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 62 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
