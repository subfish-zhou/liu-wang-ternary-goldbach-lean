import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.Lemma13Source
import LiuWang.Proof.Campaign20260915.RSSection8Scalar.OriginalL

/-! Original Lemma 8 with the shared actual K, and its contribution to actual L.
This does not supply numerical K endpoints or the other Lemma 13 terms.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set
namespace LiuWang.Proof.Campaign20260915.Parent.WeightedPsiAudit
open LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
open LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel
open LiuWang.Proof.Campaign20260915.RSSection8Scalar

theorem actual_lemma8 {x : ℝ} (hx : 1 < x) :
    |∫ y in Ioi x,
      (y - Chebyshev.psi y) * (1 + Real.log y) / (y ^ 2 * Real.log y ^ 2)| <
      (2 + Real.log x) / Real.log x ^ 2 *
        (originalK 1 x + (184 / 100 : ℝ) / x + (31 / 100 : ℝ) / x ^ 3) := by
  simpa only [originalK, originalKernelTerm] using lemma8 hx

theorem actual_psi_L_contribution {x : ℝ} (hx : 1 < x) :
    |Real.log x * ∫ y in Ioi x,
      (y - Chebyshev.psi y) * (1 + Real.log y) / (y ^ 2 * Real.log y ^ 2)| +
      2.04 / x ^ (1 / 2 : ℝ) + 4.5 * x ^ (-2 / 3 : ℝ) + 1.02 / (x - 1) < L x := by
  have h : |Real.log x * ∫ y in Ioi x,
      (y - Chebyshev.psi y) * (1 + Real.log y) / (y ^ 2 * Real.log y ^ 2)| <
      (2 + Real.log x) / Real.log x *
        (originalK 1 x + (184 / 100 : ℝ) / x + (31 / 100 : ℝ) / x ^ 3) := by
    simpa only [originalK, originalKernelTerm] using lemma13_psi_L_contribution hx
  unfold L LValue
  linarith

#print axioms actual_lemma8
#print axioms actual_psi_L_contribution
end LiuWang.Proof.Campaign20260915.Parent.WeightedPsiAudit

#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weight_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.scaledWeight_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weight_eq_scaled
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.scaledWeight_eq
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.scaledWeight_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weight_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weight_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weightSlope_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.inv_mul_log_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.inv_mul_log_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weight_integrableOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weight_integral_Ioi
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroPrimitive_weight_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSum_weight_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSum_weight_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialCoefficient_summable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialCoefficient_sum_lt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialTailTerm_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialTailTerm_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialTerm_div_sq_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialTerm_div_sq_integral
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.inv_sq_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialKernel_div_sq_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialKernel_div_sq_integral
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialTailTerm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialTailTerm_summable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialKernel_div_sq_integral_lt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.scaledWeight_antitone
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.lemma8Factor_pos
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.scaledWeight_le_lemma8Factor
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialKernel_weight_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.trivialKernel_weight_integral_lt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.constant_weight_integral_lt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.signedCorrection_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.signedCorrection_integral_abs_lt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weight_contDiffOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weightedPrimitive_eq_integral
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.errorPrimitive_spectral
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.errorPrimitive_ac
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.errorPrimitive_ae_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.actual_weighted_error_compact
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.regularPrimitive_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.regularPrimitive_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.regular_weighted_compact
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weightedPrimitive_add
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.weightedPrimitive_const
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.actual_weighted_spectral_compact
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.signedPsiError_intervalIntegrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.signedPsiError_tail_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.signedPsiError_integrableOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.signedPsiError_improper_limit
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.spectralPrimitive_weight_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.actual_spectral_weighted_tail_limit
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.momentTerm_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.momentTerm_le_zero
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.momentSum_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.momentSum_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.momentSum_le_log_sixth
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSlopeEnvelope_continuousOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSlopeEnvelope_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSlopeEnvelope_tail_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSlopeEnvelope_integrableOn
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroPrimitive_slope_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroPrimitive_slope_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSum_slope_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSum_slope_integral_exchange
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.actual_infinite_weighted_spectral_identity
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.logCube_primitive_deriv
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.logCube_primitive_limit
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.logCubeKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.logCubeKernel_integral
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zero_ne
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroPower_norm
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroC_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroD_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.momentTerm_antitone
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroBoundary_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroBoundary_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroRemainder_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroRemainder_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroRemainder_integral_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroPower_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroBoundary_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroPrimitive_weight_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.integratedZeroTail_eq
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.integratedZeroTail_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.integratedZeroTail_summable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroSlope_integrals_summable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.actual_infinite_zero_tail_identity
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zero_tail_sum_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.lemma8_moment
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.momentSum_eq_original_K
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.lemma8
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.lemma13_psi_tail_lower
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.lemma13_psi_tail_upper
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroIntegrand_norm
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.zeroIntegrand_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.original_zero_integral_eq
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.original_zero_integrals_summable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.actual_original_zero_integral_identity
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.original_zero_integral_norm_bound
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.original_weighted_error_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.lemma13_psi_L_contribution
