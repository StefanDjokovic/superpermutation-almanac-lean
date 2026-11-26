import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_cegar_0 : checkRangeAux 0 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 64 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
