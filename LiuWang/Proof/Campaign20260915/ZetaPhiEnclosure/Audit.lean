import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.CertifiedEnclosures

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem positive_half_enclosed :
    (precisePhi (1 / 2) (1 / 10 ^ 24)).Contains (1 / 2) := by
  have h := precisePhi_correct (1 / 2) (1 / 10 ^ 24) (z := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  simpa only [rsPhi_half] using h

theorem negative_half_enclosed :
    (precisePhi (-(1 / 2)) (1 / 10 ^ 24)).Contains (1 / 2) := by
  have h := precisePhi_correct (-(1 / 2)) (1 / 10 ^ 24) (z := -(1 / 2))
    (by norm_num) (by norm_num) (by norm_num)
  simpa only [rsPhi_neg_half] using h

theorem small_kernel_pilot_radius : (phiEnclosure 8 (1 / 2) 0).radius ≤ (1 : ℚ) / 100 := by
  decide +kernel

theorem small_kernel_pilot_pi_error : roundedMachinError 40 (10 ^ 20) ≤ (1 : ℚ) / 10 ^ 12 := by
  decide +kernel

#print axioms siegel_denominator_im
#print axioms siegel_denominator_lower
#print axioms correctionKernel_real_bound
#print axioms correction_center_norm
#print axioms correction_moment_kernel_bound
#print axioms correctionMoment_bound
#print axioms gaussianJet_bound
#print axioms rsPhi_derivative_bound
#print axioms rsPhi_derivative_lipschitz
#print axioms pi_square_lower
#print axioms pi_fourth_lower
#print axioms rsPhiOne_bound
#print axioms rsPhiTwo_bound
#print axioms rsPhiOne_lipschitz
#print axioms rsPhiTwo_lipschitz
#print axioms rsPhi_derivative_input_error
#print axioms sincApprox_cast
#print axioms sineJet_correct
#print axioms sincPolynomial_zero
#print axioms sine_taylor_eq
#print axioms sincPolynomial_error
#print axioms sinc_integral
#print axioms sinc_lipschitz
#print axioms sincApprox_error
#print axioms sinc_argument_error
#print axioms phi_numerator_error
#print axioms phi_denominator_error
#print axioms clamp_error
#print axioms phiApprox_correct
#print axioms piApprox_correct
#print axioms phiEnclosure_correct
#print axioms rsPhi_taylor_error
#print axioms stencilWeight_abs
#print axioms stencil_polynomial_identity
#print axioms derivativeApprox_correct
#print axioms derivativeEnclosure_correct
#print axioms RationalBall.add_correct
#print axioms RationalBall.divide_correct
#print axioms piSquareError_correct
#print axioms piFourthError_correct
#print axioms inwardStep_ne_zero
#print axioms inwardStep_domain
#print axioms phiOneApprox_correct
#print axioms phiTwoApprox_correct
#print axioms phiOneEnclosure_correct
#print axioms phiTwoEnclosure_correct
#print axioms correctionMoment_truncation
#print axioms correctionMoment_rational_truncation
#print axioms sourceGaussianPhase_norm
#print axioms sourceLocalPolynomial_seven_high_moment_error
#print axioms r2HighMomentBudget_simplified
#print axioms sourcePhi_enclosure
#print axioms sourcePhiOne_enclosure
#print axioms sourcePhiTwo_enclosure
#print axioms machinPi_correct
#print axioms roundedMachinPi_correct
#print axioms precisePi_correct
#print axioms precisePiError_small
#print axioms precisePhi_correct
#print axioms precisePhiOne_correct
#print axioms precisePhiTwo_correct
#print axioms sincApprox_abs_bound
#print axioms sincError_bound
#print axioms phi_arguments_bound
#print axioms scaled_argument_bound
#print axioms phiApprox_center_bound
#print axioms phiApprox_radius_bound
#print axioms precisePi_abs_le_four
#print axioms precisePiError_nonneg
#print axioms sincTail128_small
#print axioms precisePhi_center_bound
#print axioms precisePhi_radius_bound
#print axioms inwardStep_abs
#print axioms preciseDerivative_bounds
#print axioms RationalBall.divide_radius_bound
#print axioms precisePhiOne_radius_small
#print axioms precisePhiTwo_radius_small
#print axioms precisePhi_radius_small
#print axioms certified_phi_errors
#print axioms certified_r2_center_error
#print axioms sourceLocalPolynomial_seven_certified
#print axioms positive_half_enclosed
#print axioms negative_half_enclosed
#print axioms small_kernel_pilot_radius
#print axioms small_kernel_pilot_pi_error

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
