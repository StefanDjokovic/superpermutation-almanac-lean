import LowerBounds.F5900SmallNative

/-!
# Medium evaluated equations of `S(7) ≥ 5,900` (`native_decide`)

Chained after `F5900SmallNative` so each multi-threaded `native_decide` runs without oversubscription:
`c62`, `c76`, `k5`, `s4`, `k4`, and `ring69`.
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem c62 :
    FastK16.seqSearch Ttab 0 62 75 50 79 5 true true false 200 18 61 0 61 = false := by
  native_decide

theorem c76 :
    FastK16.seqSearch Ttab 0 76 76 25 39 5 true true false 200 18 61 0 61 = false := by
  native_decide

theorem k5 :
    FastK16.seqSearch Dtab 5 44 60 10 17 25 true true true 200 18 61 0 61 = false := by
  native_decide

theorem s4 :
    FastJ16.jSearch Dtab TRdual [(2, 0, 0), (2, 0, 0), (0, 0, 71)] rulesS4 61 71 1 300 [(0, 14, 61)] true 0 61 = false := by
  native_decide

theorem k4 :
    FastK16.seqSearch Dtab 4 48 66 10 16 25 true true true 200 18 61 0 61 = false := by
  native_decide

theorem ring69 :
    PS.ringSearch 7 (Ttab.getD 0 []) TRtab 69 400 16 61 0 61 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
