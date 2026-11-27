import LowerBounds.F5900K1_4Native

/-!
# Row 0 of Theorem K shard 0 (`parts 0..84 of 499`, `ds=20`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem k0_0 :
    FastK16.seqSearch Dtab 0 77 90 50 74 5 true true false 200 20 499 0 84 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
