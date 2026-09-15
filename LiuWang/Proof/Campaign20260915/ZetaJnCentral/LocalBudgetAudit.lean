import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SourceLocalBudgets
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.ContourAudit

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

example :
    IntervalIntegrable (rsJnIntegrand (1 / 2) 12 ⌊(12 : ℝ)⌋₊ 1) volume (12 / 2) (-12 / 2) ∧
    ‖∫ y : ℝ in (12 / 2)..(-12 / 2), rsJnIntegrand (1 / 2) 12 ⌊(12 : ℝ)⌋₊ 1 y‖ ≤
      (731 / 1000) / 12 :=
  source_R0_Jn_budget (by norm_num) (by norm_num)

example :
    IntervalIntegrable (rsJnIntegrand (1 / 2) 45 ⌊(45 : ℝ)⌋₊ 7) volume (45 / 2) (-45 / 2) ∧
    ‖∫ y : ℝ in (45 / 2)..(-45 / 2), rsJnIntegrand (1 / 2) 45 ⌊(45 : ℝ)⌋₊ 7 y‖ ≤
      (51 / 50) / 45 ^ 3 :=
  source_R2_Jn_budget (by norm_num) (by norm_num)

example : 2 * (37 / 50 : ℝ) < 3 / 2 ∧ 2 * (103 / 100 : ℝ) < 57 / 25 := by
  norm_num

#print axioms absoluteGaussian_integrable
#print axioms absoluteGaussian_integral
#print axioms gaussianAbsoluteMoment_nonneg
#print axioms gaussianAbsoluteMoment_zero
#print axioms gaussianAbsoluteMoment_one
#print axioms gaussianAbsoluteMoment_step
#print axioms exactGaussianWeight_expand
#print axioms exactGaussianWeight_integrable
#print axioms exactGaussianWeight_integral
#print axioms norm_interval_exactGaussian
#print axioms jn_central_exact_integral
#print axioms gaussianMonomial_exact_interval
#print axioms smallCircle_weight
#print axioms smallCircle_coefficient
#print axioms smallCircle_remainder
#print axioms smallCircle_remainder_four
#print axioms jn_smallCircle_pointwise
#print axioms jn_smallCircle_integral
#print axioms powerGaussian_antitone
#print axioms powerGaussian_tail_interval
#print axioms rationalGaussianMoment_nonneg
#print axioms gaussianAbsoluteMoment_rational
#print axioms inverse_descent_constant_rational
#print axioms exactGaussianBudget_rational
#print axioms exactGaussianBudget_eleven
#print axioms exactGaussian_seven_corrections
#print axioms twelfthRadius_pos
#print axioms twelfthRadius_cube
#print axioms twelfthRadius_data
#print axioms exp_five_le_150
#print axioms twelfthRadius_majorant
#print axioms twelfthRadius_twelfth
#print axioms jn_twelfth_central
#print axioms twelfth_coefficient_scaled
#print axioms twelfth_outer_pointwise
#print axioms norm_interval_twoGaussians
#print axioms jn_twelfth_outer
#print axioms exp_three_eighths_le
#print axioms twelfth_exp_seed
#print axioms twelfth_exp_seed_three
#print axioms twelfth_denominator
#print axioms twelfthOuterBudget_source
#print axioms jn_twelfth_source_budget
#print axioms norm_div_eta_pow
#print axioms sharp_scaled_four
#print axioms sharp_scaled_five
#print axioms sharp_scaled_six
#print axioms scaled_recurrence_weighted
#print axioms sharp_scaled_seven
#print axioms sharp_scaled_eight
#print axioms sharp_scaled_nine
#print axioms sharp_scaled_ten
#print axioms sharp_scaled_eleven
#print axioms scaled_weighted_to_norm
#print axioms jn_successor_split
#print axioms jn_successor_integral
#print axioms jn_finite_remainder_split
#print axioms weighted_coefficient_drop
#print axioms gaussianMonomial_scaled_interval
#print axioms jn_seven_correction_budget
#print axioms jn_seven_sharp
#print axioms jn_floor_seven_sharp
#print axioms floorContour_seven_sharp
#print axioms local_hankel_seven_sharp_error
#print axioms local_hankel_seven_sharp_R2
#print axioms mediumRadius_data
#print axioms exp_thirty_three_fifths_le
#print axioms mediumCircle_weight
#print axioms mediumCircle_coefficient
#print axioms mediumCircle_remainder
#print axioms jn_medium_central
#print axioms jn_outer_from_coefficients
#print axioms medium_outer_pointwise
#print axioms jn_medium_outer
#print axioms medium_exp_seed
#print axioms medium_exp_seed_three
#print axioms outer_denominator_99
#print axioms mediumOuterBudget_source
#print axioms jn_medium_source_budget
#print axioms norm_div_eta_pow_lower
#print axioms first_scaled_one
#print axioms first_scaled_two
#print axioms first_scaled_three
#print axioms first_scaled_four
#print axioms first_scaled_five
#print axioms first_scaled_six
#print axioms first_scaled_seven
#print axioms first_scaled_eight
#print axioms first_scaled_nine
#print axioms first_scaled_ten
#print axioms first_scaled_eleven
#print axioms firstCoefficientEnvelope_nonneg
#print axioms first_weighted_drop
#print axioms firstCoefficientEnvelope_bound
#print axioms first_correction_scalar
#print axioms jn_one_correction_budget
#print axioms jn_one_sharp
#print axioms jn_floor_one_sharp
#print axioms source_R0_Jn_budget
#print axioms source_R2_Jn_budget
#print axioms source_R0_contour_budget
#print axioms source_R2_contour_budget
#print axioms local_hankel_one_sharp_error
#print axioms one_polynomial_outer_allocation
#print axioms local_hankel_one_sharp_R0

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
