import AlmanacDefs
import LowerBounds.TropicN13_287

/-!
# Linking lemma: Almanac template from pure-kernel Level-2 `TropicCEGAR` theorem

Proves that Pantone's `SuperpermutationBounds.Covers` agrees with `Almanac.IsSuperpermutation`,
and exports the pure-kernel lower bound theorem:
* `lower_thirteen : Almanac.LowerBoundAt 13 6746627287`

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

/-- **Every superpermutation on 13 symbols has at least 6,746,627,287 letters**, as the Almanac template. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627287 := fun w hw =>
  SuperpermLowerBounds.TropicL2.N13_287.covers_length_ge_6746627287 w
    ((covers_iff_isSuperpermutation w).mpr hw)

end LowerLinks
