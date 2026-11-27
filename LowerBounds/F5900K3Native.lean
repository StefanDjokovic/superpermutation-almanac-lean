import LowerBounds.F5900MedNative

/-!
# Row 3 of Theorem K (`Dtab 3 55..72`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem k3 :
    FastK16.seqSearch Dtab 3 55 72 20 31 60 true true true 200 20 199 0 199 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
