import LowerBounds.F5900K0_0Native

/-!
# Row 0 of Theorem K shard 1 (`parts 84..167 of 499`, `ds=20`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem k0_1 :
    FastK16.seqSearch Dtab 0 77 90 50 74 5 true true false 200 20 499 84 167 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
