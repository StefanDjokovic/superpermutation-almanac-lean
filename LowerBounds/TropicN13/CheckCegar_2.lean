import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_cegar_2 : checkRangeAux 236 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 82 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
