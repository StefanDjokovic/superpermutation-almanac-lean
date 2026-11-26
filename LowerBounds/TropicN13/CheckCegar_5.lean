import LowerBounds.TropicN13.Data

namespace SuperpermLowerBounds.Tropic.TropicN13
open SuperpermLowerBounds.Tropic

theorem chk_cegar_5 : checkRangeAux 456 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 2 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN13
