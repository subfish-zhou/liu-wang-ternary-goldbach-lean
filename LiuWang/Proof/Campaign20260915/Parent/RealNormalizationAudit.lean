import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.ActualC2Normalization
import LiuWang.Proof.Campaign20260915.Parent.LeftC2TailAudit
import LiuWang.Proof.Campaign20260915.Parent.RightC2TailAudit

/-! Actual real normalization with both infinite-tail budgets consumed.
Central Jn, the final Phi derivative enclosures and original total constants remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set
namespace LiuWang.Proof.Campaign20260915.Parent.RealNormalizationAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem phase_projection_le_norm (z : ℂ) (t : ℝ) :
    |(z * criticalGammaPhase t).re| ≤ ‖z‖ := by
  simpa only [norm_mul, norm_criticalGammaPhase, mul_one] using
    Complex.abs_re_le_norm (z * criticalGammaPhase t)

theorem actual_normalized_left {eta : ℝ} (he : 10 ≤ eta) :
    |sourceLeftNormalized eta| ≤ 1 / (10 * eta ^ 4) := by
  unfold sourceLeftNormalized
  exact (phase_projection_le_norm _ _).trans
    (LeftC2TailAudit.actual_prefactored_left_tail he
      (by norm_num [criticalPoint]) (by simp [criticalPoint, sourceTime_eq]))

theorem actual_normalized_right {eta : ℝ} (he : 1 ≤ eta) :
    |sourceRightNormalized eta| ≤
      11 / (2 * Real.pi) * eta ^ (-(3 / 2 : ℝ)) * Real.exp (-sourceTime eta / 11) := by
  have hr := RightC2TailAudit.actual_prefactored_right_tail he
  rw [source_criticalPoint] at hr
  exact (phase_projection_le_norm _ _).trans hr

theorem actual_zeta_both_tails_paid {eta : ℝ}
    (he : 10 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))| ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) +
          sourceSevenUniformBudget eta (sourcePhiParameter eta ⌊eta⌋₊)) +
        |sourceJnNormalized eta| + 1 / (10 * eta ^ 4) +
          11 / (2 * Real.pi) * eta ^ (-(3 / 2 : ℝ)) * Real.exp (-sourceTime eta / 11) := by
  have h := normalized_zeta_C2_total_budget (by linarith : 1 ≤ eta) hint
  have hl := actual_normalized_left he
  have hr := actual_normalized_right (by linarith : 1 ≤ eta)
  linarith

#print axioms phase_projection_le_norm
#print axioms actual_normalized_left
#print axioms actual_normalized_right
#print axioms actual_zeta_both_tails_paid
end LiuWang.Proof.Campaign20260915.Parent.RealNormalizationAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.criticalPoint_conj
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceChi_critical
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceChi_mul_phase
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.critical_inverse_power_conj
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.critical_inverse_power_phase
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.source_sums_normalized
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalizedCriticalZeta_expanded
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.hankel_phase_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceTime_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceTime_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.source_criticalPoint
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.critical_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.source_denominator_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.source_denominator_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseTransport_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseTransport_distance
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseTransport_stirling_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.source_gaussian_critical
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_source_prefactor
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.abs_sourceSignedAmplitude
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.source_seven_decomposition
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceExtraCorrection_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_source_seven_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.phase_real_correction_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_source_seven_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.correctionMoment_derivative_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.momentDerivativeBudget_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.momentDerivativeBudget_four
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.momentDerivativeBudget_five
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.momentDerivativeBudget_six
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceExtraBudget_le_derivative
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_source_seven_derivative_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.hankel_critical_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.hankel_normalized_re_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_central_seven_exterior
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_central_seven_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_source_seven_residual
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_source_seven_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseRemainder_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseTransport_unit_distance
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseTransport_re_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseTransport_im_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_source_seven_real_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_central_seven_real_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_source_seven_real_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceHeightScale_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceTime_heightScale
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceLeadingArgument_heightScale
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseRemainder_heightScale
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceRealMainSum_cos
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_seven_at_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_seven_real_budget_at_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.arctan_abs_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.source_stirling_offset
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.source_stirling_offset_bounds
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceHeightScale_time
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceGammaPhaseBudget_uniform
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourcePhaseBudget_uniform
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceRealPhaseBudget_uniform
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceSevenRealBudget_uniform
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_source_seven_uniform_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_central_seven_uniform_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_seven_uniform_budget_at_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_C2_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_central_seven_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_C2_seven_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.sourceExpandedResidual_eq_original_C2
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_C2_full_phase
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_C2_correction_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_C2_total_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaRealNormalization.normalized_zeta_C2_at_height
