import LowerBounds.PSearch
import LowerBounds.DualRingSearch
import LowerBounds.FastK16Search
import LowerBounds.FastJ16Search
import LowerBounds.KTables
import LowerBounds.J5900Defs

/-!
# Fast evaluated equations of `S(7) ≥ 5,900` (`native_decide`)

Evaluates the small finite searches in compiled Lean code (`SearchEngine` library):
- `tr15`: exact 15-hole ring cap `TRex15` (`PS.ringSearch`)
- `trdual_70` .. `trdual_83`: Dual Cycle Lemma exact ring caps on `H = 70..83` (`PS.ringSearchDual`)
- `c59`: chain cap at 59 holes (`FastK16.seqSearch`, `(5, 8, 5)`, `M3`)
- `k6a`, `k6b`, `k7`, `k8`: rows 6, 7, 8 of `Dtab`/`Ttab` (`FastK16.seqSearch`)
- `s5`: joint statement `S5` (`FastJ16.jSearch` on `Dtab` + `TRdual`)
-/

namespace SuperpermLowerBounds
namespace F5900Shards

open T5900 J5900

theorem tr15 :
    PS.ringSearch 7 (Ttab.getD 0 []) TRex15 15 100 0 1 0 1 = false := by
  native_decide

theorem trdual_70 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 70 70 200 0 1 0 1 = false := by
  native_decide

theorem trdual_71 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 71 71 200 0 1 0 1 = false := by
  native_decide

theorem trdual_72 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 72 72 200 0 1 0 1 = false := by
  native_decide

theorem trdual_73 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 73 73 200 0 1 0 1 = false := by
  native_decide

theorem trdual_74 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 74 74 200 0 1 0 1 = false := by
  native_decide

theorem trdual_75 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 75 75 200 0 1 0 1 = false := by
  native_decide

theorem trdual_76 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 76 76 200 0 1 0 1 = false := by
  native_decide

theorem trdual_77 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 77 77 200 0 1 0 1 = false := by
  native_decide

theorem trdual_78 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 78 78 200 0 1 0 1 = false := by
  native_decide

theorem trdual_79 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 79 79 200 0 1 0 1 = false := by
  native_decide

theorem trdual_80 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 80 80 200 0 1 0 1 = false := by
  native_decide

theorem trdual_81 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 81 81 200 0 1 0 1 = false := by
  native_decide

theorem trdual_82 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 82 82 200 0 1 0 1 = false := by
  native_decide

theorem trdual_83 :
    PS.ringSearchDual 7 (Dtab.getD 0 []) TRdual 83 83 200 0 1 0 1 = false := by
  native_decide

theorem c59 :
    FastK16.seqSearch Ttab 0 59 59 5 8 5 true true false 200 0 1 0 1 = false := by
  native_decide

theorem k6a :
    FastK16.seqSearch Dtab 6 0 43 10 17 25 true false false 200 0 1 0 1 = false := by
  native_decide

theorem k6b :
    FastK16.seqSearch Dtab 6 44 54 10 18 25 true true true 200 0 1 0 1 = false := by
  native_decide

theorem k7 :
    FastK16.seqSearch Ttab 7 0 48 1 0 0 true false false 200 0 1 0 1 = false := by
  native_decide

theorem k8 :
    FastK16.seqSearch Ttab 8 0 42 1 0 0 true false false 200 0 1 0 1 = false := by
  native_decide

theorem s5 :
    FastJ16.jSearch Dtab TRdual [(1, 0, 0), (1, 0, 0), (0, 0, 70)] rulesS5 62 70 2 300 [] true 0 1 = false := by
  native_decide

end F5900Shards
end SuperpermLowerBounds
