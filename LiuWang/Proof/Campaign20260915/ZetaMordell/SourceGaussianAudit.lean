import LiuWang.Proof.Campaign20260915.ZetaMordell.SourceMainTerm

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

#print axioms poleFreeRotor
#print axioms poleFreePoint
#print axioms poleFreeKernel
#print axioms poleFree_denominator_ne_zero
#print axioms poleFreeKernel_analytic
#print axioms poleFreeKernel_horizontal_continuous
#print axioms poleFree_denominator_tail
#print axioms poleFree_gaussian_factor
#print axioms poleFreeKernel_tail_bound
#print axioms poleFreeKernel_horizontal_integrable
#print axioms poleFreeKernel_vertical_tendsto
#print axioms poleFreeKernel_rectangle
#print axioms poleFreeKernel_horizontal_eq
#print axioms poleFreePoint_line
#print axioms poleFreeKernel_line
#print axioms poleFreeKernel_half
#print axioms poleFreeKernel_integral_moment
#print axioms sourceGaussianPhase
#print axioms sourcePhiParameter
#print axioms sourceFraction_floor
#print axioms sourcePhiParameter_mem
#print axioms sourcePhiParameter_domain
#print axioms sourcePhiParameter_floor_domain
#print axioms sourcePhiParameter_delta
#print axioms sourceGaussian_integer_shift
#print axioms sourceGaussian_descent_coordinates
#print axioms sourceGaussian_moment_pointwise
#print axioms sourceGaussian_moment_integrable
#print axioms sourceGaussian_moment_integral
#print axioms sourceGaussian_scaled_moment_integrable
#print axioms sourceGaussian_scaled_moment_integral
#print axioms sourceLocalPolynomial_integrable
#print axioms sourceLocalPolynomial_integral
#print axioms sourceGaussian_polynomial_integrable
#print axioms sourceGaussian_polynomial_transfer
#print axioms sourceGaussian_phiZero
#print axioms sourceGaussian_phiOne
#print axioms sourceGaussian_phiOne_integrable
#print axioms sourceGaussian_phiTwo
#print axioms sourceGaussian_phiTwo_integrable
#print axioms sourceLocalPolynomial_phi_derivatives
#print axioms sourceLocalPolynomial_phi_floor
#print axioms sourceLocalPolynomial_interval
#print axioms sourceSaddle_scaled_zero
#print axioms sourceSaddle_scaled_one
#print axioms sourceSaddle_scaled_two
#print axioms sourceSaddle_scaled_recurrence
#print axioms sourceSaddle_scaled_three
#print axioms sourceSaddle_scaled_four
#print axioms sourceSaddle_scaled_five
#print axioms sourceSaddle_scaled_six
#print axioms sourceSaddle_time_scale
#print axioms sourcePhase_square
#print axioms sourceGaussian_prefactor
#print axioms correctionMoment_zero_phi
#print axioms correctionPolynomial_moment_sum
#print axioms correctionMoment_one_three_phi
#print axioms correctionMoment_two_four_six_phi
#print axioms sourceLocalPolynomial_one_phi
#print axioms sourceLocalPolynomial_seven_phi
#print axioms sourceLocalPolynomial_prefactored

example {eta : ℝ} {m : ℕ} (h : eta - m = 1 / 4) :
    -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y)) =
      sourceGaussianPhase eta m * (rsPhi (-1 / 2) : ℂ) := by
  have hf := sourceGaussian_phiZero (by linarith : 0 < eta - m) (by linarith : eta - m < 1)
  norm_num [sourcePhiParameter, h] at hf ⊢
  exact hf

example {eta : ℝ} {m : ℕ} (h : eta - m = 3 / 4) :
    -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      (-(2 / 9 : ℂ) * Real.pi ^ 2 * (rsDescentPoint eta y - eta) ^ 6 -
        (5 / 6 : ℂ) * Real.pi * I * (rsDescentPoint eta y - eta) ^ 4 +
        (3 / 8 : ℂ) * (rsDescentPoint eta y - eta) ^ 2 - I / (96 * Real.pi))) =
      sourceGaussianPhase eta m * (rsPhiTwo (1 / 2) : ℂ) := by
  have hf := sourceGaussian_phiTwo (by linarith : 0 < eta - m) (by linarith : eta - m < 1)
  norm_num [sourcePhiParameter, h] at hf ⊢
  exact hf

end LiuWang.Proof.Campaign20260915.ZetaMordell
