import LiuWang.Proof.Campaign20260915.MajorArc.ThirdHead
import LiuWang.Proof.Campaign20260915.MajorArc.RootAssembly

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries
open LiuWang.Proof.SourceRoute.MajorOrdinary

namespace LiuWang.Proof.Campaign20260915.MajorArc

theorem threeOddPrimes_of_low_high_and_minor {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N :=
  threeOddPrimes_of_original_arcs hN
    (ordinary_major_lower_with_third_head_paid hN hodd hlow hhigh) hsecond hthird

#print axioms threeOddPrimes_of_low_high_and_minor

end LiuWang.Proof.Campaign20260915.MajorArc
