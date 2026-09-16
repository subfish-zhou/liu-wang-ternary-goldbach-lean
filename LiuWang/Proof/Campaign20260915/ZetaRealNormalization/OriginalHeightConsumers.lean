import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.CriticalC2Mass

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem sourceHeightScale_sq {t : ℝ} (ht : 0 ≤ t) :
    sourceHeightScale t ^ 2 = t / (2 * Real.pi) := by
  exact Real.sq_sqrt (div_nonneg ht (by positivity))

theorem normalized_zeta_R0_height_margin {t : ℝ}
    (ht : 250 * Real.pi < t) (hint : ∀ k : ℤ, sourceHeightScale t ≠ k) :
    |normalizedCriticalZeta t -
      (2 * ∑ n ∈ Finset.range ⌊sourceHeightScale t⌋₊,
        Real.cos (criticalGammaArgument t - t * Real.log (n + 1)) / Real.sqrt (n + 1) +
        sourceSignedAmplitude (sourceHeightScale t) ⌊sourceHeightScale t⌋₊ *
          rsPhi (sourcePhiParameter (sourceHeightScale t) ⌊sourceHeightScale t⌋₊))| +
      (11 / 20) * (t / (2 * Real.pi)) ^ (-(3 / 4 : ℝ)) ≤
        (3 / 2) * (t / (2 * Real.pi)) ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by nlinarith [Real.pi_pos]
  have he0 := sourceHeightScale_pos ht0
  have he : 11 ≤ sourceHeightScale t := by
    have hs := sourceHeightScale_sq ht0.le
    have hx : 125 < t / (2 * Real.pi) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    nlinarith
  have h := normalized_zeta_R0_margin he hint
  rw [sourceTime_heightScale ht0.le, sourceHeightScale_sq ht0.le, sourceRealMainSum_cos] at h
  linarith

theorem normalized_zeta_R0_height_strict {t : ℝ}
    (ht : 250 * Real.pi < t) (hint : ∀ k : ℤ, sourceHeightScale t ≠ k) :
    |normalizedCriticalZeta t -
      (2 * ∑ n ∈ Finset.range ⌊sourceHeightScale t⌋₊,
        Real.cos (criticalGammaArgument t - t * Real.log (n + 1)) / Real.sqrt (n + 1) +
        sourceSignedAmplitude (sourceHeightScale t) ⌊sourceHeightScale t⌋₊ *
          rsPhi (sourcePhiParameter (sourceHeightScale t) ⌊sourceHeightScale t⌋₊))| <
        (3 / 2) * (t / (2 * Real.pi)) ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by nlinarith [Real.pi_pos]
  have hp : 0 < (t / (2 * Real.pi)) ^ (-(3 / 4 : ℝ)) := by positivity
  linarith [normalized_zeta_R0_height_margin ht hint]

theorem critical_height_scale_eight {t : ℝ} (ht : 128 * Real.pi ≤ t) :
    8 ≤ sourceHeightScale t := by
  have ht0 : 0 < t := by nlinarith [Real.pi_pos]
  have he := sourceHeightScale_pos ht0
  have hs := sourceHeightScale_sq ht0.le
  have hx : 64 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  nlinarith

theorem critical_zeta_norm_at_height {t : ℝ}
    (ht : 128 * Real.pi ≤ t) (hint : ∀ k : ℤ, sourceHeightScale t ≠ k) :
    ‖riemannZeta (criticalPoint t)‖ ≤
      |2 * ∑ n ∈ Finset.range ⌊sourceHeightScale t⌋₊,
        Real.cos (criticalGammaArgument t - t * Real.log (n + 1)) / Real.sqrt (n + 1)| +
          48 / 25 := by
  have ht0 : 0 < t := by nlinarith [Real.pi_pos]
  simpa only [sourceTime_heightScale ht0.le, sourceRealMainSum_cos] using
    critical_zeta_norm_main_budget (critical_height_scale_eight ht) hint

#print axioms normalized_zeta_R0_height_strict
#print axioms critical_zeta_norm_at_height

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
