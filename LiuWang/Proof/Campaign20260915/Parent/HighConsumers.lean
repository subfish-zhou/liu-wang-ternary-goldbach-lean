import LiuWang.Proof.Campaign20260915.MajorArc.PaperRoot
import LiuWang.Proof.Campaign20260915.HighSums.OriginalHighSum
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

namespace LiuWang.Proof.Campaign20260915.Parent.HighConsumers

open LiuWang.Proof.Campaign20260915.MajorArc
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem threeOddPrimes_of_paper_source_high_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hT1 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      ∀ alpha y : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hreal : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        ∀ (chi : Character q) (rho : ℂ), rho ∈ DirichletZeroCount.zeroValues chi 0 y →
          1 - (1 / c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0)
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
  apply threeOddPrimes_of_paper_source hN hodd hd h987 hphi _ hordinary hsecond hthird
  intro q inst hq hdq
  exact HighSums.highSum_original_of_T1_T7_near_one_real hN hq
    (hT1 q hq hdq) (hT7 q hq hdq) (hreal q hq hdq)

#print axioms threeOddPrimes_of_paper_source_high_paid

end LiuWang.Proof.Campaign20260915.Parent.HighConsumers

#print axioms LiuWang.Proof.Campaign20260915.HighSums.band_reciprocal_add_below_height
#print axioms LiuWang.Proof.Campaign20260915.HighSums.belowHeightLayerCorrection_nonneg
#print axioms LiuWang.Proof.Campaign20260915.HighSums.below_height_correction_nonneg
#print axioms LiuWang.Proof.Campaign20260915.HighSums.below_height_filter
#print axioms LiuWang.Proof.Campaign20260915.HighSums.below_height_layer_integrable
#print axioms LiuWang.Proof.Campaign20260915.HighSums.below_height_layer_mass
#print axioms LiuWang.Proof.Campaign20260915.HighSums.below_height_layer_mass_integrable
#print axioms LiuWang.Proof.Campaign20260915.HighSums.combined_exponent_mono
#print axioms LiuWang.Proof.Campaign20260915.HighSums.compensated_excess_after_endpoint_table
#print axioms LiuWang.Proof.Campaign20260915.HighSums.compensated_highSum_large_height
#print axioms LiuWang.Proof.Campaign20260915.HighSums.compensated_highSum_small_height
#print axioms LiuWang.Proof.Campaign20260915.HighSums.count_le_below_height_of_real
#print axioms LiuWang.Proof.Campaign20260915.HighSums.differenceKernel_le_positive_correction
#print axioms LiuWang.Proof.Campaign20260915.HighSums.excessHighSum_add_belowHeightLayerCorrection
#print axioms LiuWang.Proof.Campaign20260915.HighSums.exp_neg_ninety_le
#print axioms LiuWang.Proof.Campaign20260915.HighSums.family_reciprocal_add_below_height
#print axioms LiuWang.Proof.Campaign20260915.HighSums.highSum_large_height_of_near_one_real
#print axioms LiuWang.Proof.Campaign20260915.HighSums.highSum_large_height_second_without_tail
#print axioms LiuWang.Proof.Campaign20260915.HighSums.highSum_original_of_T1_T7_near_one_real
#print axioms LiuWang.Proof.Campaign20260915.HighSums.highSum_small_height_of_near_one_real
#print axioms LiuWang.Proof.Campaign20260915.HighSums.near_one_count_zero_of_not_first
#print axioms LiuWang.Proof.Campaign20260915.HighSums.paid_high_budget
#print axioms LiuWang.Proof.Campaign20260915.HighSums.paid_high_budget_with_transfer
#print axioms LiuWang.Proof.Campaign20260915.HighSums.short_correction_endpoint_certificate
#print axioms LiuWang.Proof.Campaign20260915.HighSums.short_correction_scaled
#print axioms LiuWang.Proof.Campaign20260915.HighSums.short_main_nonneg
#print axioms LiuWang.Proof.Campaign20260915.HighSums.source36_full_lambda_paid
#print axioms LiuWang.Proof.Campaign20260915.HighSums.sourceMass_eq_compensated_height
#print axioms LiuWang.Proof.Campaign20260915.HighSums.tail_slice_le_below_height_mass
#print axioms LiuWang.Proof.Campaign20260915.HighSums.tail_slice_le_two_segments
#print axioms LiuWang.Proof.Campaign20260915.HighSums.tail_slice_nonneg
#print axioms LiuWang.Proof.Campaign20260915.HighSums.tail_slice_zero_of_not_first
#print axioms LiuWang.Proof.Campaign20260915.HighSums.tail_slice_zero_of_second
#print axioms LiuWang.Proof.Campaign20260915.HighSums.transferRemainder_le_endpoint
#print axioms LiuWang.Proof.Campaign20260915.HighSums.transferRemainder_le_four_div_hundred_thousand
#print axioms LiuWang.Proof.Campaign20260915.HighSums.zeroTail_eq_first_case_integral
#print axioms LiuWang.Proof.Campaign20260915.HighSums.zeroTail_le_compensation_of_near_one_real
#print axioms LiuWang.Proof.Campaign20260915.HighSums.zeroTail_nonneg
#print axioms LiuWang.Proof.Campaign20260915.HighSums.zeroTail_zero_of_second
