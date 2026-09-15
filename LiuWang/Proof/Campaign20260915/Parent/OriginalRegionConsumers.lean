import LiuWang.Proof.Campaign20260915.OriginalRegion.LectureAudit
import LiuWang.Proof.Campaign20260915.Parent.PaperOrdinaryPaid
import LiuWang.Proof.Campaign20260915.Parent.OrdinaryHighBridge

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.Campaign20260915.Parent.OriginalRegionConsumers

theorem moving_high_real {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ), rho ∈ zeroValues chi 0 y →
        1 - (1 / c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0 := by
  intro y hy chi rho hz hb
  have hr := mem_zeroValues.mp hz
  apply OriginalRegion.original_middle_local_source_free hN hq hy.1 chi rho
    hr.1 hr.2.1.1 hr.2.1.2.1 hr.2.1.2.2
  simpa only [c1, div_div] using hb

open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation
open LiuWang.Proof.Campaign20260915.MajorArc
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
open LiuWang.Proof.SingularSeries
open LiuWang.Proof.SourceRoute.MajorOrdinary
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.Campaign20260915.MajorArc LiuWang.Proof.DirichletZeroCount

theorem threeOddPrimes_paper_region_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h987 : 987 ≤ (d.modulus : ℝ))
    (hphi : (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hT1 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ alpha y : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N :=
  PaperOrdinaryPaid.threeOddPrimes_of_paper_source_budgets_paid hN hodd hd h987 hphi hT1 hT7
    (fun q _ hq => moving_high_real (q := q) hN hq) hsecond hthird

#print axioms threeOddPrimes_paper_region_paid

theorem threeOddPrimes_ordinary_region_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hT1 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ alpha y : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N :=
  OrdinaryHighBridge.threeOddPrimes_of_low_counts_and_minor hN hodd hlow hT1 hT7
    (fun q _ hq => moving_high_real (q := q) hN hq) hsecond hthird

#print axioms threeOddPrimes_ordinary_region_paid

#print axioms moving_high_real
end LiuWang.Proof.Campaign20260915.Parent.OriginalRegionConsumers

#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.all_nonprincipal_lecture_poles_paid
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.conductor_euler_support_share
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.consecutive_power_corrections_disjoint
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.cubic_lecture_poles_paid
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.cubic_lecture_selected
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.equation_5_42_source_free
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.fourth_lecture_poles_paid
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.fourth_lecture_selected
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.fourth_order_damped_nonneg
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.fourth_order_low_no_zero
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.fourth_order_real_axis_budget
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.fourth_root_phase_nonneg
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.harmonic_support_upper
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.higher_order_lecture_budget
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lectureCoefficients_exact
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lectureCoefficients_pos
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lectureShift_properties
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_badPrimeCost_joint
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_center_selected
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_conductor_euler_joint
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_damped_nonneg
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_high_pole_free_budget
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_moving_pole_budget
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_original_scalar
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_phase_nonneg
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_principal_euler_reserve
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_scaled_budget_contradiction
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_selected_bound
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_selected_envelope_strict
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.lecture_signed_moving_envelope
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.low_sum_of_short_absence_source_free
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.low_weight_of_short_absence_source_free
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.moving_original_real
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.ordinary_fourth_order_low_original
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.ordinary_high_original
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.ordinary_higher_order_original
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.ordinary_source_free_original_closed
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.originalClosedZeros_subsingleton
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.originalGap_le_lectureShift
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.original_high_local_source_free
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.original_middle_local_source_free
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.original_nonreal_residual
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.original_short_classification_closed
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.phase_nat_power
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.primitive_badPrimeCost
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.primitive_high_original
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.primitive_higher_order_original
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.primitive_source_free_original_closed
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.principal_badPrimeCost
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.principal_original_no_zero
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.principal_original_no_zero_closed
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.quadratic_conjugate_mass
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.quadratic_lecture_poles_paid
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.quadratic_pair_signed_budget
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.quarter_height_pole_obstruction
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.real_axis_signed_selection
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.reflectedKernel_conjugate_at_zero
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.signedCost_le_harmonicBound
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.signed_real_principal_strong
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.smallOrderLowZeros_subsingleton
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.small_order_low_classification
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.small_order_low_zeros_equal
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.sourceP_original_scale
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.source_free_low_original_classification
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.source_free_nonreal_seed_cap
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.source_free_original_classification
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.source_free_original_classification_closed
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.source_free_original_option
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.source_free_original_zeros_equal_closed
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.square_polynomial_identity
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.square_polynomial_nonneg
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.zeta_lecture_budget
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.zeta_original_no_zero
#print axioms LiuWang.Proof.Campaign20260915.OriginalRegion.zeta_original_no_zero_closed
