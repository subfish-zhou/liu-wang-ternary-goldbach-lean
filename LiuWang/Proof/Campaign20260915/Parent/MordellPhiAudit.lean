import LiuWang.Proof.Campaign20260915.ZetaMordell.Audit

/-! Parent acceptance of actual directed integrals and their Phi bridge.
This module does not assert the actual zeta transformation or its error budget.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.Parent.MordellPhiAudit
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem actual_correction_integral {z : ℝ} (hz : |z| < 3 / 2) :
    Integrable (correctionKernel (z : ℂ)) ∧
      (∫ t : ℝ, correctionKernel (z : ℂ) t) = (rsPhi z : ℂ) :=
  ⟨correctionKernel_integrable z, correctionIntegral_eq_rsPhi hz⟩

theorem actual_correction_derivatives {z : ℝ} (hz : |z| < 3 / 2) :
    iteratedDeriv 3 correctionIntegral (z : ℂ) / (12 * Real.pi ^ 2) = (rsPhiOne z : ℂ) ∧
    iteratedDeriv 2 correctionIntegral (z : ℂ) / (16 * Real.pi ^ 2) +
      iteratedDeriv 6 correctionIntegral (z : ℂ) / (288 * Real.pi ^ 4) = (rsPhiTwo z : ℂ) :=
  ⟨correctionIntegral_third_deriv_phiOne hz, correctionIntegral_derivs_phiTwo hz⟩

#print axioms actual_correction_integral
#print axioms actual_correction_derivatives
end LiuWang.Proof.Campaign20260915.Parent.MordellPhiAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.analyticAt_dslope_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionCenteredKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionCenteredMoment_tendsto
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionDerivPolynomial_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionDerivPolynomial_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionDerivPolynomial_kernel
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionDerivPolynomial_six
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionDerivPolynomial_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionDerivPolynomial_two
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionDerivPolynomial_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionGeneratingKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionGenerating_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionGenerating_inverse
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionGenerating_normalization
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_centered_moment
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_cos_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_deriv_moment_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_derivs_phiTwo
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_eq_rsPhi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_generating_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_iteratedDeriv_eq_rsPhi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_normalization
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_phiOne
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_phiTwo
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_tendsto
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionIntegral_third_deriv_phiOne
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionKernel_generating_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionKernel_normalization
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionMoment_generating_deriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionMoment_phi_derivatives
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionPhiOne_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionPhiOne_polynomial
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionPhiTwo_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionPhiTwo_polynomial
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionPolynomial_integral_phiOne
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionPolynomial_integral_phiTwo
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_even
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_five
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_four
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_odd
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_rec
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_six
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_succ
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_two
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.gaussianJet_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellAmplitude_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellAmplitude_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellDenominator_exp_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellDenominator_inv_bounded
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellDenominator_inv_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellDenominator_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellExpSlope_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellFrequency_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellGaussian_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellGaussian_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellGaussian_norm_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellGaussian_phase
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellGaussian_quadratic
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellIntegral_contour_shift
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellIntegral_difference
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellIntegral_difference_exp
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellIntegral_iteratedDeriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellIntegral_tendsto
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellKernel_difference
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellLine_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellLine_norm_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellMoment_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellMoment_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellPole_difference_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellPole_difference_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellPole_horizontal_difference
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegularKernel_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegularKernel_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegular_horizontal_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegular_horizontal_difference
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegular_horizontal_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegular_horizontal_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegular_rectangle
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegular_vertical_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRegular_vertical_tendsto
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_bottom
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_bottom_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_bottom_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_bottom_line
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_denominator_inv_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_exp_eq_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_exp_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_gaussian_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_phase
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_top
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_top_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_top_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_top_line
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotated_vertical_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellRotor_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellSpatialShift
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellWeightedKernel_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellWeightedKernel_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellWeightedKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.mordellWeightedKernel_uniform_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelCenteredKernel_expansion
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelCenteredKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_at_removable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_centered_moment
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_closed_form
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_closed_form_all
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_closed_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_conj
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_contour_shift
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_difference
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_iteratedDeriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_power_moment
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelIntegral_tendsto
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelKernel_conj
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelLine_conj
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelLine_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelMoment_conj
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelMoment_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelMoment_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelPowerKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelPowerKernel_unweight
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelWeightedKernel_conj
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.siegelWeightedKernel_integrable
