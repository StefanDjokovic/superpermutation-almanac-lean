import LowerBounds.F5900K1_0Native

/-!
# Row 1 of Theorem K shard 1 (`parts 100..200 of 499`, `ds=20`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem k1_1 :
    FastK16.seqSearch Dtab 1 62 84 25 38 70 true true true 200 20 499 100 200 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
