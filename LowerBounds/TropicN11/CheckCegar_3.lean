import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_cegar_3 : checkRangeAux 147 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 2 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
