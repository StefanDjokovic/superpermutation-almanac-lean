import LowerBounds.TropicN11.Data

namespace SuperpermLowerBounds.Tropic.TropicN11
open SuperpermLowerBounds.Tropic

theorem chk_cegar_1 : checkRangeAux 64 (fun fid => checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid)) 42 = true := by decide +kernel

end SuperpermLowerBounds.Tropic.TropicN11
