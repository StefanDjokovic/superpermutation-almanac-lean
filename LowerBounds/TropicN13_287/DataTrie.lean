import LowerBounds.TropicN13_287.DataSt0
import LowerBounds.TropicN13_287.DataSt1
import LowerBounds.TropicN13_287.DataSt2
import LowerBounds.TropicN13_287.DataSt3
import LowerBounds.TropicN13_287.DataSt4
import LowerBounds.TropicN13_287.DataSt5
import LowerBounds.TropicN13_287.DataSt6
import LowerBounds.TropicN13_287.DataSt7
import LowerBounds.TropicN13_287.DataGo0
import LowerBounds.TropicN13_287.DataGo1
import LowerBounds.TropicN13_287.DataGo2
import LowerBounds.TropicN13_287.DataGo3
import LowerBounds.TropicN13_287.DataGo4
import LowerBounds.TropicN13_287.DataGo5
import LowerBounds.TropicN13_287.DataGo6
import LowerBounds.TropicN13_287.DataGo7
import LowerBounds.TropicN13_287.DataGo8
import LowerBounds.TropicN13_287.DataGo9
import LowerBounds.TropicN13_287.DataGo10
import LowerBounds.TropicN13_287.DataGo11
import LowerBounds.TropicN13_287.DataGo12
import LowerBounds.TropicN13_287.DataGo13
import LowerBounds.TropicN13_287.DataGo14
import LowerBounds.TropicN13_287.DataGo15

namespace SuperpermLowerBounds.TropicL2.N13_287
noncomputable section

def stPack (u : Nat) : Nat :=
  let p := Nat.div u 71680
  let r := Nat.mod u 71680
  @Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (getStPart0 r) (getStPart1 r) (Nat.ble 1 p)) (@Bool.rec (fun _ => Nat) (getStPart2 r) (getStPart3 r) (Nat.ble 3 p)) (Nat.ble 2 p)) (@Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (getStPart4 r) (getStPart5 r) (Nat.ble 5 p)) (@Bool.rec (fun _ => Nat) (getStPart6 r) (getStPart7 r) (Nat.ble 7 p)) (Nat.ble 6 p)) (Nat.ble 4 p)

def goPack (u : Nat) : Nat :=
  let p := Nat.div u 35840
  let r := Nat.mod u 35840
  @Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (getGoPart0 r) (getGoPart1 r) (Nat.ble 1 p)) (@Bool.rec (fun _ => Nat) (getGoPart2 r) (getGoPart3 r) (Nat.ble 3 p)) (Nat.ble 2 p)) (@Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (getGoPart4 r) (getGoPart5 r) (Nat.ble 5 p)) (@Bool.rec (fun _ => Nat) (getGoPart6 r) (getGoPart7 r) (Nat.ble 7 p)) (Nat.ble 6 p)) (Nat.ble 4 p)) (@Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (getGoPart8 r) (getGoPart9 r) (Nat.ble 9 p)) (@Bool.rec (fun _ => Nat) (getGoPart10 r) (getGoPart11 r) (Nat.ble 11 p)) (Nat.ble 10 p)) (@Bool.rec (fun _ => Nat) (@Bool.rec (fun _ => Nat) (getGoPart12 r) (getGoPart13 r) (Nat.ble 13 p)) (@Bool.rec (fun _ => Nat) (getGoPart14 r) (getGoPart15 r) (Nat.ble 15 p)) (Nat.ble 14 p)) (Nat.ble 12 p)) (Nat.ble 8 p)

end
end SuperpermLowerBounds.TropicL2.N13_287
