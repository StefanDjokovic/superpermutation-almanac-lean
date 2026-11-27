import LowerBounds.F5900S2a2_1Native

/-!
# Row 2 of Theorem K shard 0 (`parts 0..84 of 251`, `ds=18`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem k2_0 :
    FastK16.seqSearch Dtab 2 61 78 25 39 75 true true true 200 18 251 0 84 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
