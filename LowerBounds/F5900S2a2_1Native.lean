import LowerBounds.F5900S2a2_0Native

/-!
# Joint statement S2a2 shard 1 (`parts 100..199 of 199`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem s2a2_1 :
    FastJ16.jSearch Dtab TRex15 [(6, 0, 0), (0, 8, 15)] rulesS2a2 51 83 1 300 [(0, 16, 199)] true 100 199 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
