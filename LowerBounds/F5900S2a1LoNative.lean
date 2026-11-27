import LowerBounds.F5900S1Native

/-!
# Joint statement S2a1_lo (`S5 R[16..83, v≤11]; 51, 83; 1`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem s2a1_lo :
    FastJ16.jSearch Dtab TRlo11 [(6, 0, 0), (0, 16, 83)] rulesS2a1Lo 51 83 1 300 [(0, 16, 199)] true 0 199 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
