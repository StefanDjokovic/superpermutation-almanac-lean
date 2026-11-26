import LowerBounds.TropicSound
import LowerBounds.TropicN12.DataAlpha
import LowerBounds.TropicN12.DataCegar
import LowerBounds.TropicN12.DataStates
import LowerBounds.TropicN12.DataOv

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds.Tropic
local notation "sel(" c ", " a ", " b ")" => @Bool.rec (fun _ => _) b a c

private noncomputable def decOpt (v : Nat) : Option Nat :=
  sel(Nat.beq v 0, none, some (Nat.sub v 1))

noncomputable def cert : TropicCert where
  k := 12
  D_track := 3
  cn := 203
  bn := 24408
  q := 4596
  A := 41161
  bias := 165255
  ALPHA := 131
  V := 50708
  numCegar := 243
  symInfo := fun a =>
    let v := get_symInfo a
    (Nat.mod v 16, Nat.mod (Nat.div v 16) 16, Nat.div v 256)
  symId := fun m d t => decOpt (get_symId ((m * 4 + d) * 5 + t))
  d1State := get_d1State
  stD0 := fun u => Nat.beq (get_stD0 u) 1
  stPsi := fun u f =>
    sel(Nat.beq f 0, decOpt (get_stPsi0 u), sel(Nat.beq f 1, decOpt (get_stPsi1 u), decOpt (get_stPsi2 u)))
  stPar := get_stPar
  stSym := get_stSym
  stFail := get_stFail
  stFailSteps := get_stFailSteps
  maxPsi := fun s f =>
    sel(Nat.beq f 0, decOpt (get_maxPsi0 s), sel(Nat.beq f 1, decOpt (get_maxPsi1 s), decOpt (get_maxPsi2 s)))
  cegarForb := get_cegarForb
  cegarWit := fun fid =>
    let v := get_cegarWit fid
    (Nat.mod v 65536, Nat.mod (Nat.div v 65536) 256, Nat.mod (Nat.div v 16777216) 65536, Nat.div v 1099511627776)
  pairMode := fun s a => get_pairMode (s * 131 + a)
  ovList := get_ovList
  ovMap := get_ovMap

end SuperpermLowerBounds.Tropic.TropicN12
