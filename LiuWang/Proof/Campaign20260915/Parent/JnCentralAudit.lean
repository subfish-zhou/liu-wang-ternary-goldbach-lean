import LiuWang.Proof.Campaign20260915.ZetaJnCentral.LocalBudgetAudit
import LiuWang.Proof.Campaign20260915.Parent.RealNormalizationAudit

/-! Sharp local Jn and its actual normalized-zeta consumer.
The Jn bound includes integer eta; the zeta identity below retains its noninteger domain.
Final explicit Phi bounds and original R0/R2 strict endpoint budgets remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set
namespace LiuWang.Proof.Campaign20260915.Parent.JnCentralAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaJnCentral

theorem actual_normalized_Jn_paid {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    |sourceJnNormalized eta| ≤ eta ^ (-(1 / 2 : ℝ)) * ((51 / 50) / eta ^ 3) := by
  have he0 : 0 < eta := by nlinarith
  have h := hankel_normalized_re_bound (sourceTime_pos he0)
    (rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
      (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y))
  have hp : ‖rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊‖ = eta ^ (-(1 / 2 : ℝ)) := by
    simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] using
      exterior_localPrefactor_norm (1 / 2) he0 ⌊eta⌋₊
  rw [norm_mul, hp] at h
  have hj := mul_le_mul_of_nonneg_left (source_R2_Jn_budget he ht).2
    (Real.rpow_nonneg he (-(1 / 2 : ℝ)))
  simpa only [sourceJnNormalized, mul_assoc] using h.trans hj

theorem actual_zeta_Jn_and_both_tails_paid {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))| ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) +
          sourceSevenUniformBudget eta (sourcePhiParameter eta ⌊eta⌋₊) + (51 / 50) / eta ^ 3) +
        1 / (10 * eta ^ 4) +
          11 / (2 * Real.pi) * eta ^ (-(3 / 2 : ℝ)) * Real.exp (-sourceTime eta / 11) := by
  have h := RealNormalizationAudit.actual_zeta_both_tails_paid
    (by nlinarith : 10 ≤ eta) hint
  have hj := actual_normalized_Jn_paid he ht
  linarith

#print axioms actual_normalized_Jn_paid
#print axioms actual_zeta_Jn_and_both_tails_paid
end LiuWang.Proof.Campaign20260915.Parent.JnCentralAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_middle_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_middle_half
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_middle_integrals
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.positive_div_one_sub_exp_neg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussian_times_distance
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.centralTaylorConstant_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_central_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_central_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_measurable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_central_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_local_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_local_split
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_local_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_floor_local_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_budget_parameters
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.saddle_exponent_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.firstOrderPolynomial_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.descent_exponent_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.descent_exponent_envelope
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.firstOrder_remainder
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_one_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.power_gaussian_third
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.firstOrderGaussianConstant_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.firstOrderPolynomial_gaussian
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussian_interval_le_full
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_one_source_order
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_taylor_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_one_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_seven_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.hankelDenominator_int_add
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sine_real_part
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sine_norm_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.hankelDenominator_sine
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.hankelDenominator_re_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.hankelDenominator_im_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.poleArcDenominator_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.pole_circle_denominator
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleRadius_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleRadius_lt_half
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.source_pole_circle_denominator
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jnCore_descent
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jnCore_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleDistance_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.source_pole_circle_distance
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussian_exponent_disk
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.poleArcCoreBound_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_source_pole_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_source_pole_arc_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_source_pole_arc_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleNormal_coordinates
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleNormal_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorPoint_deriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorPoint_radius
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorVelocity_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorCosine_mem
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorAngle_mem
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorPoint_axis
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorPoint_side
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorPoint_descent_decomposition
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorPoint_endpoint
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorPoint_distance
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleCap_open
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleCap_convex
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleCap_no_integer
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleCap_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleCap_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleCap_minor
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleCap_minor_chord
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleCap_path_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_source_minor_deformation
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourcePoleDistance_lt_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jnCore_source_sphere
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_source_minor_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_source_minor_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinorLow_le_high
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_source_minor_oriented
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_source_minor_segment_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sourceMinor_endpoints_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.centralSupBound_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_central_sup
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_central_subinterval
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_minor_connectors
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_local_subinterval_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_local_minor_split
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_local_arc_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_four_weighted
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_five_weighted
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_six_weighted
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_seven_weighted
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_weight_drop
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_eight_weighted
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_seven_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_eight_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianMomentEnvelope_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianMoment_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.norm_interval_of_gaussian
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_central_gaussian_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianMonomial_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianMonomial_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianMonomial_interval
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthRadius_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthRadius_cube
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.saddleScale_two_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthRadius_upper
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthRadius_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthRadius_data
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthSourceMajorant
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthRadius_ninth
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthCentralConstant
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninthCutoff_ninth
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exp_neg_le_fourth
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.ninth_outer_integrals
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_nine_source_order
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_seven_to_nine_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_seven_to_nine_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_seven_source_order
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_floor_seven_source_order
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.source_pole_disks_separated
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.source_pole_disks_not_both
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_floor_contour_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_floor_contour_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_floor_contour
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.floorContour_source_orders
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_R0_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_R2_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_seven_source_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_seven_R2_domain
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.absoluteGaussian_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.absoluteGaussian_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianAbsoluteMoment_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianAbsoluteMoment_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianAbsoluteMoment_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianAbsoluteMoment_step
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exactGaussianWeight_expand
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exactGaussianWeight_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exactGaussianWeight_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.norm_interval_exactGaussian
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_central_exact_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianMonomial_exact_interval
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.smallCircle_weight
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.smallCircle_coefficient
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.smallCircle_remainder
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.smallCircle_remainder_four
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_smallCircle_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_smallCircle_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.powerGaussian_antitone
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.powerGaussian_tail_interval
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.rationalGaussianMoment_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianAbsoluteMoment_rational
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.inverse_descent_constant_rational
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exactGaussianBudget_rational
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exactGaussianBudget_eleven
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exactGaussian_seven_corrections
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfthRadius_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfthRadius_cube
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfthRadius_data
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exp_five_le_150
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfthRadius_majorant
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfthRadius_twelfth
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_twelfth_central
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfth_coefficient_scaled
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfth_outer_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.norm_interval_twoGaussians
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_twelfth_outer
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exp_three_eighths_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfth_exp_seed
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfth_exp_seed_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfth_denominator
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.twelfthOuterBudget_source
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_twelfth_source_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.norm_div_eta_pow
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sharp_scaled_four
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sharp_scaled_five
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sharp_scaled_six
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_recurrence_weighted
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sharp_scaled_seven
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sharp_scaled_eight
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sharp_scaled_nine
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sharp_scaled_ten
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.sharp_scaled_eleven
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.scaled_weighted_to_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_successor_split
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_successor_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_finite_remainder_split
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.weighted_coefficient_drop
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.gaussianMonomial_scaled_interval
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_seven_correction_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_seven_sharp
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_floor_seven_sharp
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.floorContour_seven_sharp
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_seven_sharp_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_seven_sharp_R2
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.mediumRadius_data
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.exp_thirty_three_fifths_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.mediumCircle_weight
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.mediumCircle_coefficient
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.mediumCircle_remainder
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_medium_central
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_outer_from_coefficients
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.medium_outer_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_medium_outer
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.medium_exp_seed
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.medium_exp_seed_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.outer_denominator_99
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.mediumOuterBudget_source
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_medium_source_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.norm_div_eta_pow_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_two
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_four
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_five
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_six
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_seven
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_eight
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_nine
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_ten
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_scaled_eleven
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.firstCoefficientEnvelope_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_weighted_drop
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.firstCoefficientEnvelope_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.first_correction_scalar
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_one_correction_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_one_sharp
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.jn_floor_one_sharp
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.source_R0_Jn_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.source_R2_Jn_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.source_R0_contour_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.source_R2_contour_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_one_sharp_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.one_polynomial_outer_allocation
#print axioms LiuWang.Proof.Campaign20260915.ZetaJnCentral.local_hankel_one_sharp_R0
