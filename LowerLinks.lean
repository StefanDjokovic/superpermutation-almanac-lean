import AlmanacDefs
import LowerBounds.TropicN11
import LowerBounds.TropicN12
import LowerBounds.TropicN13

/-!
# Linking lemmas: Almanac templates from pure-kernel `TropicCEGAR-Macro` theorems

Proves that Pantone's `SuperpermutationBounds.Covers` agrees with `Almanac.IsSuperpermutation`,
and exports the pure-kernel lower bound theorems:
* `lower_eleven   : Almanac.LowerBoundAt 11 43917905`    (`+1` over live)
* `lower_twelve   : Almanac.LowerBoundAt 12 522622407`   (`+6` over live)
* `lower_thirteen : Almanac.LowerBoundAt 13 6746627284`  (`+236` over live)

Every finite check is verified purely by the Lean kernel (`decide +kernel`); zero `native_decide`.
-/

namespace LowerLinks

/-- Pantone's `Covers` is the Almanac's `IsSuperpermutation`. -/
theorem covers_iff_isSuperpermutation {n : Nat} (w : List (Fin n)) :
    SuperpermutationBounds.Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hnd hlen
    obtain ⟨u, v, huv⟩ := h p hlen hnd
    show ∃ s t, s ++ p ++ t = w
    exact ⟨u, v, huv.symm⟩
  · intro h p hlen hnd
    obtain ⟨u, v, huv⟩ : ∃ s t, s ++ p ++ t = w := h p hnd hlen
    exact ⟨u, v, huv.symm⟩

/-- **Every superpermutation on 11 symbols has at least 43,917,905 letters**, as the Almanac template. -/
theorem lower_eleven : Almanac.LowerBoundAt 11 43917905 := fun w hw =>
  SuperpermLowerBounds.Tropic.TropicN11.covers_length_ge_43917905 w
    ((covers_iff_isSuperpermutation w).mpr hw)

/-- **Every superpermutation on 12 symbols has at least 522,622,407 letters**, as the Almanac template. -/
theorem lower_twelve : Almanac.LowerBoundAt 12 522622407 := fun w hw =>
  SuperpermLowerBounds.Tropic.TropicN12.covers_length_ge_522622407 w
    ((covers_iff_isSuperpermutation w).mpr hw)

/-- **Every superpermutation on 13 symbols has at least 6,746,627,284 letters**, as the Almanac template. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627284 := fun w hw =>
  SuperpermLowerBounds.Tropic.TropicN13.covers_length_ge_6746627284 w
    ((covers_iff_isSuperpermutation w).mpr hw)

end LowerLinks
