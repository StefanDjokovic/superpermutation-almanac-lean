import LowerBounds.PSearch

/-!
# Dual Cycle Lemma ring search (`r * H ≤ d * T`)

Rotating a ring to `argmin S_k` instead of `argmax S_k` flips `d * T ≤ r * H` to `r * H ≤ d * T`
inside `PS.ringKeep`. On high-hole rings (`H = 70..83`) where the chain cap `D_0[H]` has flat slope
`1.0`, this reduces the ring search from millions of nodes to `< 1,000` nodes (`< 5 ms`).
-/

namespace SuperpermLowerBounds
namespace PS

/-- Dual ring bad predicate: at least two rows, `Glo ≤ d ≤ G`, strictly above `PR[d]`. -/
def ringBadDual (PR : List Nat) (Glo G : Nat) (_ r d : Nat) : Bool :=
  2 ≤ r && Glo ≤ d && d ≤ G && PR.getD d 0 < r

/-- Dual Cycle Lemma ring keep predicate (`r * H ≤ d * T`, `Glo ≤ H ≤ G`). -/
def ringKeepDual (M PR : List Nat) (Glo G : Nat) (_ r d : Nat) : Bool :=
  (List.range (G + 1)).any fun H => Glo ≤ H && d ≤ H &&
    (let mh := M.getD H 0
     let pr := PR.getD H 0
     let mr := M.getD (H - d) 0
     (List.range (mh + 1)).any fun T => pr < T && r < T && r * H ≤ d * T && T ≤ r + mr)

/-- Compiled Dual Cycle Lemma ring search for `Glo ≤ H ≤ G`. -/
def ringSearchDual (k : Nat) (M PR : List Nat) (Glo G fuel ds nt pa pb : Nat) : Bool :=
  let B := M.getD G 0 + 2
  let tb := tab3 1 B (G + 1) (ringBadDual PR Glo G)
  let tn := tab3 1 B (G + 1) (ringKeepDual M PR Glo G)
  searchB k false noRule (look3 1 B (G + 1) tb (ringBadDual PR Glo G))
    (look3 1 B (G + 1) tn (ringKeepDual M PR Glo G)) noRule noRule fuel ds nt pa pb

end PS
end SuperpermLowerBounds
