import LowerBounds.J16Search
import LowerBounds.KTables

/-!
# Lightweight table & rule definitions for the joint searches of `5,900`

Zero Mathlib imports, so every `native_decide` shard module imports this file in `< 0.1s`.
-/

namespace SuperpermLowerBounds
namespace J5900

/-- Tight exact ring cap table for `0..15` holes (verified by `PS.ringSearch`). -/
def TRex15 : List Nat :=
  [5, 5, 5, 5, 5, 5, 10, 10, 16, 13, 14, 15, 16, 16, 21, 22]

/-- Tightened ring cap table `min (TRtab[H]) (Dtab[0][H])` on `0..69`, plus Dual Cycle Lemma
exact bounds on `70..83` (`ringSearchDual` in `< 10 ms`). -/
def TRdual : List Nat :=
  [5, 5, 5, 5, 5, 5, 10, 10, 16, 16, 16, 16, 16, 16, 21, 22, 27, 27,
   33, 33, 35, 35, 37, 37, 38, 38, 40, 41, 46, 46, 48, 49, 50, 50, 56, 56,
   58, 58, 59, 60, 65, 65, 67, 67, 69, 69, 71, 71, 76, 77, 78, 78, 84, 84,
   84, 84, 86, 87, 89, 89, 91, 91, 93, 93, 95, 96, 97, 98, 99, 100,
   110, 111, 112, 114, 115, 117, 118, 120, 121, 122, 123, 124, 125, 126, 128]

/-- Ring cap table `min (TRtab[H]) (H + 11)` for `S2a1_lo` (`valK 7 L ≤ 11`). -/
def TRlo11 : List Nat :=
  [5, 5, 5, 5, 5, 5, 10, 10, 16, 16, 16, 16, 16, 16, 21, 22, 27, 27,
   29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
   47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
   65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82,
   83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

/-- Rules for `S1`. -/
def rulesS1 : J16.Rules :=
  { vcl := [(-99, 99), (-99, 99)], rp := 0, pa := 10, pb := 16, ph := 25, oi := 0, clip := false }

/-- Rules for `S2a1_hi` (`16 ≤ H ≤ 83`, `12 ≤ vR`). -/
def rulesS2a1Hi : J16.Rules :=
  { vcl := [(12, 99), (-99, 99)], rp := 1, pa := 10, pb := 16, ph := 25, oi := 99, clip := true }

/-- Rules for `S2a1_lo` (`16 ≤ H ≤ 83`, `vR ≤ 11`, `S5` first). -/
def rulesS2a1Lo : J16.Rules :=
  { vcl := [(-99, 99), (-99, 11)], rp := 0, pa := 10, pb := 16, ph := 25, oi := 99, clip := false }

/-- Rules for `S2a2` (`8 ≤ H ≤ 15`, `S5` first). -/
def rulesS2a2 : J16.Rules :=
  { vcl := [(-99, 99), (-99, 99)], rp := 0, pa := 10, pb := 16, ph := 25, oi := 99, clip := false }

/-- Rules for `S3`. -/
def rulesS3 : J16.Rules :=
  { vcl := [(-99, 99), (-99, 99), (-99, 99)], rp := 0, pa := 10, pb := 16, ph := 25, oi := 99, clip := false }

/-- Rules for `S4`. -/
def rulesS4 : J16.Rules :=
  { vcl := [(-99, 99), (-99, 99), (-99, 99)], rp := 0, pa := 10, pb := 15, ph := 30, oi := 0, clip := false }

/-- Rules for `S5`. -/
def rulesS5 : J16.Rules :=
  { vcl := [(-99, 99), (-99, 99), (-99, 99)], rp := 0, pa := 2, pb := 3, ph := 5, oi := 0, clip := false }

end J5900
end SuperpermLowerBounds
