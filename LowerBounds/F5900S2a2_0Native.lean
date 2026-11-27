import LowerBounds.F5900S3Native

/-!
# Joint statement S2a2 shard 0 (`parts 0..100 of 199`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem s2a2_0 :
    FastJ16.jSearch Dtab TRex15 [(6, 0, 0), (0, 8, 15)] rulesS2a2 51 83 1 300 [(0, 16, 199)] true 0 100 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
