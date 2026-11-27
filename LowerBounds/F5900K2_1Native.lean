import LowerBounds.F5900K2_0Native

/-!
# Row 2 of Theorem K shard 1 (`parts 84..168 of 251`, `ds=18`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem k2_1 :
    FastK16.seqSearch Dtab 2 61 78 25 39 75 true true true 200 18 251 84 168 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
