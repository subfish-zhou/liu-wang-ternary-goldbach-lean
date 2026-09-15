import LiuWang.Proof.Campaign20260915.Totient.RSFullSmoothingAudit

/-! Parent consumption of the actual all-order psi spectral bounds.
The weighted zero moment is an actual expression, not a supplied bound.
The numerical moment and high-zero payments remain separate obligations.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Parent.TotientFullSmoothingAudit
open LiuWang.Proof.Campaign20260915.Totient

theorem actual_psi_moment_bounds {m : ℕ} (hm : 1 ≤ m)
    {δ a x : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hcut : 1 + (m : ℝ) * δ * a < a) (hax : a ≤ x) :
    x - (m : ℝ) * δ * x / 2 -
      x * 2 ^ m / δ ^ m * (∑' p, rsZeroMoment m (Real.log x) p) - 1.84 <
      Chebyshev.psi x ∧
    Chebyshev.psi x <
      x + (m : ℝ) * δ * x / 2 +
        x * (1 + (1 + δ) ^ (m + 1)) ^ m / δ ^ m *
          (∑' p, rsZeroMoment m (Real.log x) p) + rsTrivialKernel x :=
  rsPsi_original_moment_bounds hm hδ ha hcut hax

#print axioms actual_psi_moment_bounds
end LiuWang.Proof.Campaign20260915.Parent.TotientFullSmoothingAudit

#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPolyIntegral_derivative
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPolyIntegral_degree
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPolyIntegral_interval
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPolynomial_difference_vanish
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaCorrection_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_positive_primitive_integrable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaPrimitive_integrable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaPrimitive_integral
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPolePrimitive_deriv
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPolePrimitive_integral
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_spectral_polynomial
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_spectral_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsTrivialTerm_hasSum
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsTrivialTerm_nonneg
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsTrivialTerm_antitone
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsTrivialPrimitive_deriv
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_scaled_gamma_term
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsTrivialPrimitive_summable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaCorrection_eq_trivial_sum
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaCorrection_deriv
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsTrivialKernel_nonneg
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsTrivialKernel_antitone
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_difference_congr_positive
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_local_difference_integrable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_local_difference_integral
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_difference_re
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_difference_ofReal
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsTrivialKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaPrimitive_real_integrable
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaCorrection_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaPrimitive_real_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaPrimitive_difference_bounds
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsGammaPrimitive_normalized_bounds
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_difference_sub
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_factorial_power_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPolePrimitive_finite_difference
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_real_spectrum
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsiPrimitive_normalized_spectral_bounds
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsi_original_moment_bounds
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroMoment_sum_antitone
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsZeroMoment_low_high
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsi_delta_epsilon_of_actual_moment
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsi_delta_epsilon_of_low_window_and_high_sum
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_delta_root_budget
#print axioms LiuWang.Proof.Campaign20260915.Totient.rs_low_weight_sqrt
#print axioms LiuWang.Proof.Campaign20260915.Totient.rsPsi_original_root_epsilon
