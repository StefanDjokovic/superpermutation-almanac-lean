import LowerBounds.F5900S2a1LoNative

/-!
# Joint statement S2a1_hi (`R[16..83, v≥12] S5; 51, 83; 1`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem s2a1_hi :
    FastJ16.jSearch Dtab TRdual [(0, 16, 83), (6, 0, 0)] rulesS2a1Hi 51 83 1 300 [(0, 18, 199)] true 0 199 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
