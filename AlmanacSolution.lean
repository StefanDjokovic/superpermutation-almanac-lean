-- Pure-kernel (zero `sorry`, zero `native_decide`) formal proof of
-- `S(n) = n! + (n-1)! + (n-2)! + o((n-3)!)` (`Almanac.AsymptoticUpper 0`).
import AlmanacDefs
import AsymptoticZero.Main

namespace AlmanacSubmission

/-- For every `ε > 0`, for all sufficiently large `n`, there exists a superpermutation on `n`
symbols of length at most `n! + (n-1)! + (n-2)! + ε (n-3)!`. -/
theorem asymptotic_upper : Almanac.AsymptoticUpper 0 :=
  AsymptoticZero.asymptotic_upper_zero

end AlmanacSubmission
