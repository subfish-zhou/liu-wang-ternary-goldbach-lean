import LiuWang.Proof.Campaign20260915.ZetaValidation.CompleteCountCheck

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.Campaign20260915.Parent.ZetaCompleteAudit

theorem original_verification_iff_above_sixteen :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      |s.im| < 1894438 → s.re = 1 / 2) ↔
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      16 < |s.im| → |s.im| < 1894438 → s.re = 1 / 2) := by
  constructor
  · intro h s hz h0 h1 _ ht
    exact h s hz h0 h1 ht
  · intro h s hz h0 h1 ht
    by_cases hlow : |s.im| ≤ 16
    · exact (ZetaValidation.zeta_sixteen_all_simple_on_line hz h0 h1 hlow).1
    · exact h s hz h0 h1 (lt_of_not_ge hlow) ht

#print axioms original_verification_iff_above_sixteen
end LiuWang.Proof.Campaign20260915.Parent.ZetaCompleteAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.critical_polynomial_argument
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_abel_correction_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coeff0
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coeff1
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coeff2
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coeff3
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coeff4
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coeff5
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coeff6
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coeff7
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_coefficient_real
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_cpow
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_partial_sum_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_prefix_rational
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_prefix_real
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_second_order_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_tail_phase
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_tail_phase_rational
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.horizontal_zeta_re_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.originalHeightGammaArgumentCenter_abs
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.originalHeightGammaPhaseCenter_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.originalHeightRoundedArgument_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.originalHeightRoundedArgument_reduced
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.roundQComplexAt_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.roundRationalAt_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.unitPhaseAt_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.unitPhaseAt_original_scale
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.unitTaylorAt_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.unitTaylorAt_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.weighted_prefix_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.xiCountingPrimitive_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.xiCountingPrimitive_sixteen_im
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.xiCountingPrimitive_two_im
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.xi_right_vertical_primitive
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.xi_upper_horizontal_primitive
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.xi_upper_integral_primitive
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.xi_upper_integral_sixteen_lt
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zetaClosedCount_sixteen
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zetaClosedValues_sixteen_pair
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_ne_zero_height_sixteen
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_ne_zero_horizontal_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaValidation.zeta_sixteen_all_simple_on_line
