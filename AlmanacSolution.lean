-- Lower bounds from Theorem C (proofs/lean/lower of github.com/jhalfar/superpermutations) with re-tuned
-- constants; every finite search is evaluated by the kernel. The linking lemmas are in LowerLinks.lean.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 13 symbols has length at least 6,746,627,110. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627110 := LowerLinks.lower_thirteen

end AlmanacSubmission
