import LiuWang.Proof.Campaign20260915.ZetaMordell.SourceGaussianAudit

/-! Actual local Hankel consumer of the proved Gaussian-to-Mordell transport.
Both the polynomial exterior integral and the genuine Jn integral remain explicit.
Integer eta and the complete zeta remainder are not discharged by this module.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Parent.SourceGaussianAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem actual_local_hankel_split (sigma : ℝ) (N : ℕ) {eta : ℝ}
    (he : 0 < eta) (hint : ∀ k : ℤ, eta ≠ k) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) =
    rsLocalPrefactor sigma eta ⌊eta⌋₊ *
      ((sourceGaussianPhase eta ⌊eta⌋₊ *
        ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
          (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊) +
        ∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ,
          rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ N y) +
        ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ N y) := by
  have hf := sourceFraction_floor he.le hint
  rw [rsHankel_local_truncation sigma ⌊eta⌋₊ N he hint,
    sourceLocalPolynomial_interval sigma hf.1 hf.2 N]

#print axioms actual_local_hankel_split
end LiuWang.Proof.Campaign20260915.Parent.SourceGaussianAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionMoment_one_three_phi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionMoment_two_four_six_phi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionMoment_zero_phi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.correctionPolynomial_moment_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_analytic
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_half
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_horizontal_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_horizontal_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_horizontal_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_integral_moment
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_line
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_rectangle
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_tail_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeKernel_vertical_tendsto
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreePoint
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreePoint_line
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFreeRotor
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFree_denominator_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFree_denominator_tail
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.poleFree_gaussian_factor
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceFraction_floor
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussianPhase
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_descent_coordinates
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_integer_shift
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_moment_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_moment_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_moment_pointwise
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_phiOne
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_phiOne_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_phiTwo
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_phiTwo_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_phiZero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_polynomial_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_polynomial_transfer
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_prefactor
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_scaled_moment_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceGaussian_scaled_moment_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceLocalPolynomial_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceLocalPolynomial_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceLocalPolynomial_interval
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceLocalPolynomial_one_phi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceLocalPolynomial_phi_derivatives
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceLocalPolynomial_phi_floor
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceLocalPolynomial_prefactored
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceLocalPolynomial_seven_phi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourcePhase_square
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourcePhiParameter
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourcePhiParameter_delta
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourcePhiParameter_domain
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourcePhiParameter_floor_domain
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourcePhiParameter_mem
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_scaled_five
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_scaled_four
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_scaled_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_scaled_recurrence
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_scaled_six
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_scaled_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_scaled_two
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_scaled_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.sourceSaddle_time_scale
