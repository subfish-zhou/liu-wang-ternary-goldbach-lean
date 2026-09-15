import LiuWang.Proof.FiniteTernaryClosure.Regression
import LiuWang.Proof.PrimePowerRemoval.Main
import LiuWang.Proof.CircleLowerBound.Main

/-!
# Connection to the actual circle-method count

The signed interaction and M2/M3 integrals below are the frozen source objects.
The residual inequality is an explicit UNPAID hypothesis, not a new estimate.
The already proved 0.48166084 circle bound and strict 0.003 prime-power budget
leave the exact allowance 0.47866084. The count-to-prime bridge is reused.

The finite/analytic union theorem does not cover 1000 < N < exp 3100.
No finite regression is used to discharge an analytic error.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces
open LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.PrimePowerRemoval

namespace LiuWang.Proof.FiniteTernaryClosure

theorem threeOddPrimes_of_circle_residual {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hresidual :
      -(0.47866084 : ℝ) * (N : ℝ) ^ 2 ≤
        (interactionIntegral N).re +
          (∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
          (∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re -
          6760 * (N : ℝ) ^ 2 / sourceL N ^ 4) :
    LiuWang.IsThreeOddPrimeSum N := by
  have hcircle := CircleLowerBound.lambdaTripleCount_ge_strong hN hodd
  have hremove := lambdaTripleCount_sub_I_lt_budget hN
  apply isThreeOddPrimeSum_of_I_pos hN
  linarith

theorem threeOddPrimes_on_certified_union {N : ℕ}
    (h9 : 9 ≤ N) (hodd : Odd N)
    (hdomain : N ≤ 1000 ∨ Real.exp 3100 ≤ (N : ℝ))
    (hresidual : 1000 < N →
      -(0.47866084 : ℝ) * (N : ℝ) ^ 2 ≤
        (interactionIntegral N).re +
          (∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
          (∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re -
          6760 * (N : ℝ) ^ 2 / sourceL N ^ 4) :
    LiuWang.IsThreeOddPrimeSum N := by
  by_cases hsmall : N ≤ 1000
  · exact threeOddPrimes_9_1000 N h9 hsmall hodd
  · have hlarge : Real.exp 3100 ≤ (N : ℝ) := hdomain.resolve_left hsmall
    exact threeOddPrimes_of_circle_residual hlarge hodd (hresidual (by omega))

end LiuWang.Proof.FiniteTernaryClosure
