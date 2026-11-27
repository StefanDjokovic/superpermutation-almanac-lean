import LowerBounds.F5900K3Native

/-!
# Joint statement S1 (`S4 S4; 55, 78; 1`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem s1 :
    FastJ16.jSearch Dtab TRdual [(5, 0, 0), (5, 0, 0)] rulesS1 55 78 1 300 [(0, 14, 199)] true 0 199 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
