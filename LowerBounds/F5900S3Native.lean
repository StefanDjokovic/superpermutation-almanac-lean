import LowerBounds.F5900S2a1HiNative

/-!
# Joint statement S3 (`S2 R R; 57, 76; 2`) (`native_decide`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem s3 :
    FastJ16.jSearch Dtab TRdual [(3, 0, 0), (0, 0, 76), (0, 0, 76)] rulesS3 57 76 2 300 [(0, 18, 199)] true 0 199 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
