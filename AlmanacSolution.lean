-- A lower bound of 5,900 for 7 symbols, building on github.com/jhalfar/superpermutations with
-- kernel-verified dominance pruning (`m=3` 440-motif & `w4->w3` 271-motif shortcuts, `U3` 3-row
-- greatest-fixed-point upper bounds, unboxed ByteArray/UInt64 search engines `FastK16Search` and
-- `FastJ16Search`, and the Dual Cycle Lemma on `H = 70..83`). The linking lemma is in LowerLinks.lean.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 7 symbols has length at least 5,900. -/
theorem lower_seven : Almanac.LowerBoundAt 7 5900 := LowerLinks.lower_seven

end AlmanacSubmission
