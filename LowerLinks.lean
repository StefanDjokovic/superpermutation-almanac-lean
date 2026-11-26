import AlmanacDefs
import LowerBounds.TropicN10

/-!
# Linking lemmas: Almanac templates from pure-kernel `TropicCEGAR-Macro` theorems

Proves that Pantone's `SuperpermutationBounds.Covers` agrees with `Almanac.IsSuperpermutation`,
and exports the pure-kernel lower bound theorem(s):
* `lower_ten : Almanac.LowerBoundAt 10 4033380`, from `SuperpermLowerBounds.Tropic.TropicN10.covers_length_ge_4033380`.

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

/-- **Every superpermutation on 10 symbols has at least 4,033,380 letters**, as the Almanac template. -/
theorem lower_ten : Almanac.LowerBoundAt 10 4033380 := fun w hw =>
  SuperpermLowerBounds.Tropic.TropicN10.covers_length_ge_4033380 w
    ((covers_iff_isSuperpermutation w).mpr hw)

end LowerLinks
