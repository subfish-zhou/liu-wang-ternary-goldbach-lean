import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SourceOrderConsumer
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.Audit

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

example (sigma : ℝ) {eta : ℝ} (he : 2 ≤ eta)
    (hint : ∀ k : ℤ, eta ≠ k) (N : ℕ) :
    ‖jnFloorContour sigma eta (N + 1)‖ ≤
      arcLocalBudget sigma eta (21 / 40 * (rsSaddleScale * eta)) N := by
  have he0 : 0 < eta := by linarith
  have hp := local_budget_parameters he0
  have hD : sourcePoleDistance ≤ eta / 2 := by linarith [sourcePoleDistance_lt_one]
  apply jn_floor_contour_bound sigma he hint hp.1 hp.2.1
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD rsSaddleScale_pos.le)
    (by norm_num : (0 : ℝ) ≤ 21 / 20)).trans hp.2.2.2

example :
    IntervalIntegrable (rsJnIntegrand (1 / 2) 2 ⌊(2 : ℝ)⌋₊ 7) volume (2 / 2) (-2 / 2) ∧
    ‖∫ y : ℝ in (2 / 2)..(-2 / 2), rsJnIntegrand (1 / 2) 2 ⌊(2 : ℝ)⌋₊ 7 y‖ ≤
      seventhJnConstant / 2 ^ 3 :=
  jn_floor_seven_source_order le_rfl

#print axioms jn_middle_pointwise
#print axioms jn_middle_half
#print axioms jn_middle_integrals
#print axioms positive_div_one_sub_exp_neg
#print axioms jn_zero
#print axioms gaussian_times_distance
#print axioms centralTaylorConstant_nonneg
#print axioms jn_central_pointwise
#print axioms jn_central_integral
#print axioms jn_measurable
#print axioms jn_central_integrable
#print axioms jn_local_integrable
#print axioms jn_local_split
#print axioms jn_local_budget
#print axioms jn_floor_local_budget
#print axioms local_budget_parameters
#print axioms saddle_exponent_norm
#print axioms firstOrderPolynomial_nonneg
#print axioms descent_exponent_norm
#print axioms descent_exponent_envelope
#print axioms firstOrder_remainder
#print axioms jn_one_pointwise
#print axioms power_gaussian_third
#print axioms firstOrderGaussianConstant_nonneg
#print axioms firstOrderPolynomial_gaussian
#print axioms gaussian_interval_le_full
#print axioms jn_one_source_order
#print axioms local_hankel_taylor_error
#print axioms local_hankel_one_error
#print axioms local_hankel_seven_error
#print axioms hankelDenominator_int_add
#print axioms sine_real_part
#print axioms sine_norm_lower
#print axioms hankelDenominator_sine
#print axioms hankelDenominator_re_lower
#print axioms hankelDenominator_im_lower
#print axioms poleArcDenominator_pos
#print axioms pole_circle_denominator
#print axioms sourcePoleRadius_pos
#print axioms sourcePoleRadius_lt_half
#print axioms source_pole_circle_denominator
#print axioms jnCore_descent
#print axioms jnCore_analytic
#print axioms sourcePoleDistance_pos
#print axioms source_pole_circle_distance
#print axioms gaussian_exponent_disk
#print axioms poleArcCoreBound_nonneg
#print axioms jn_source_pole_pointwise
#print axioms jn_source_pole_arc_integrable
#print axioms jn_source_pole_arc_bound
#print axioms sourcePoleNormal_coordinates
#print axioms sourcePoleNormal_norm
#print axioms sourceMinorPoint_deriv
#print axioms sourceMinorPoint_radius
#print axioms sourceMinorVelocity_norm
#print axioms sourceMinorCosine_mem
#print axioms sourceMinorAngle_mem
#print axioms sourceMinorPoint_axis
#print axioms sourceMinorPoint_side
#print axioms sourceMinorPoint_descent_decomposition
#print axioms sourceMinorPoint_endpoint
#print axioms sourceMinorPoint_distance
#print axioms sourcePoleCap_open
#print axioms sourcePoleCap_convex
#print axioms sourcePoleCap_no_integer
#print axioms sourcePoleCap_analytic
#print axioms sourcePoleCap_exact
#print axioms sourcePoleCap_minor
#print axioms sourcePoleCap_minor_chord
#print axioms sourcePoleCap_path_integral
#print axioms jn_source_minor_deformation
#print axioms sourcePoleDistance_lt_one
#print axioms jnCore_source_sphere
#print axioms jn_source_minor_integrable
#print axioms jn_source_minor_bound
#print axioms sourceMinorLow_le_high
#print axioms jn_source_minor_oriented
#print axioms jn_source_minor_segment_bound
#print axioms sourceMinor_endpoints_bound
#print axioms centralSupBound_nonneg
#print axioms jn_central_sup
#print axioms jn_central_subinterval
#print axioms jn_minor_connectors
#print axioms jn_local_subinterval_integrable
#print axioms jn_local_minor_split
#print axioms jn_local_arc_budget
#print axioms scaled_four_weighted
#print axioms scaled_five_weighted
#print axioms scaled_six_weighted
#print axioms scaled_seven_weighted
#print axioms scaled_weight_drop
#print axioms scaled_eight_weighted
#print axioms scaled_seven_bound
#print axioms scaled_eight_bound
#print axioms gaussianMomentEnvelope_nonneg
#print axioms gaussianMoment_pointwise
#print axioms norm_interval_of_gaussian
#print axioms jn_central_gaussian_integral
#print axioms gaussianMonomial_pointwise
#print axioms gaussianMonomial_integrable
#print axioms gaussianMonomial_interval
#print axioms ninthRadius_pos
#print axioms ninthRadius_cube
#print axioms saddleScale_two_three
#print axioms ninthRadius_upper
#print axioms ninthRadius_lower
#print axioms ninthRadius_data
#print axioms ninthSourceMajorant
#print axioms ninthRadius_ninth
#print axioms ninthCentralConstant
#print axioms ninthCutoff_ninth
#print axioms exp_neg_le_fourth
#print axioms ninth_outer_integrals
#print axioms jn_nine_source_order
#print axioms jn_seven_to_nine_pointwise
#print axioms jn_seven_to_nine_integral
#print axioms jn_seven_source_order
#print axioms jn_floor_seven_source_order
#print axioms source_pole_disks_separated
#print axioms source_pole_disks_not_both
#print axioms jn_floor_contour_eq
#print axioms jn_floor_contour_bound
#print axioms local_hankel_floor_contour
#print axioms floorContour_source_orders
#print axioms jn_R0_height
#print axioms jn_R2_height
#print axioms local_hankel_seven_source_error
#print axioms local_hankel_seven_R2_domain

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
