import LiuWang.Proof.Campaign20260915.MajorArc.PaperPayment
import LiuWang.Proof.Campaign20260915.MajorArc.RootAssembly

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation

namespace LiuWang.Proof.Campaign20260915.MajorArc

theorem threeOddPrimes_of_paper_source {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4)
    (hordinary : -(0.00000009 * (N : ℝ) ^ 2) ≤ (paperOrdinaryIntegral N d e).re)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N := by
  have hm := paper_caseII_of_original_ordinary hN hodd hd h987 hphi hhigh hordinary
  apply threeOddPrimes_of_original_arcs hN _ hsecond hthird
  exact (mul_le_mul_of_nonneg_right (by norm_num : (0.5437 : ℝ) ≤ 0.5577)
    (sq_nonneg (N : ℝ))).trans hm

#print axioms threeOddPrimes_of_paper_source

end LiuWang.Proof.Campaign20260915.MajorArc
