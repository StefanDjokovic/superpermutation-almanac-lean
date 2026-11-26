import AlmanacDefs
import LowerBounds.RecordsFinal

/-!
# Linking lemmas: Almanac templates for `S(11) ≥ 43,917,905`, `S(12) ≥ 522,622,404`, `S(13) ≥ 6,746,627,184`
-/

namespace LowerLinks

theorem covers_iff_isSuperpermutation {n : Nat} (w : List (Fin n)) :
    SuperpermutationBounds.Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hnd hlen
    obtain ⟨u, v, huv⟩ := h p hlen hnd
    exact ⟨u, v, huv.symm⟩
  · intro h p hlen hnd
    obtain ⟨u, v, huv⟩ := h p hnd hlen
    exact ⟨u, v, huv.symm⟩

/-- Every superpermutation on 11 symbols has at least 43,917,905 letters. -/
theorem lower_eleven : Almanac.LowerBoundAt 11 43917905 := fun w hw =>
  SuperpermLowerBounds.covers_length_ge_43917905 w ((covers_iff_isSuperpermutation w).mpr hw)

/-- Every superpermutation on 12 symbols has at least 522,622,404 letters. -/
theorem lower_twelve : Almanac.LowerBoundAt 12 522622404 := fun w hw =>
  SuperpermLowerBounds.covers_length_ge_522622404 w ((covers_iff_isSuperpermutation w).mpr hw)

/-- Every superpermutation on 13 symbols has at least 6,746,627,184 letters. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627184 := fun w hw =>
  SuperpermLowerBounds.covers_length_ge_6746627184 w ((covers_iff_isSuperpermutation w).mpr hw)

end LowerLinks
