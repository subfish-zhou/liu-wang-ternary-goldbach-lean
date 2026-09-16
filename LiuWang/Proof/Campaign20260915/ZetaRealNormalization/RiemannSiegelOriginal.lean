import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.OriginalHeightConsumers
import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourceCorrectionAllocation

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem normalized_zeta_R2_margin {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ *
          sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))| ≤
        (223 / 100) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have he0 : 0 < eta := by nlinarith
  have hf := sourceFraction_floor he hint
  have h := abs_sub_le (normalizedCriticalZeta (sourceTime eta))
    (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourceSevenNormalized eta ⌊eta⌋₊)
    (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ + sourceSignedAmplitude eta ⌊eta⌋₊ *
      sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))
  rw [add_sub_add_left_eq_sub] at h
  apply (h.trans (add_le_add (normalized_zeta_full_seven_margin he ht hint)
    (normalized_source_seven_original_allocation (by nlinarith : 1 ≤ eta) hf.1 hf.2))).trans_eq
  rw [original_scale_two he0]
  ring

theorem normalized_zeta_R2_strict {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    |normalizedCriticalZeta (sourceTime eta) -
      (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
        sourceSignedAmplitude eta ⌊eta⌋₊ *
          sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))| <
        (57 / 25) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have hp : 0 < (eta ^ 2) ^ (-(7 / 4 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  exact (normalized_zeta_R2_margin he ht hint).trans_lt (by nlinarith)

theorem normalized_zeta_R2_height_margin {t : ℝ}
    (ht : 4000 * Real.pi < t) (hint : ∀ k : ℤ, sourceHeightScale t ≠ k) :
    |normalizedCriticalZeta t -
      (2 * ∑ n ∈ Finset.range ⌊sourceHeightScale t⌋₊,
        Real.cos (criticalGammaArgument t - t * Real.log (n + 1)) / Real.sqrt (n + 1) +
        sourceSignedAmplitude (sourceHeightScale t) ⌊sourceHeightScale t⌋₊ *
          (rsPhi (sourcePhiParameter (sourceHeightScale t) ⌊sourceHeightScale t⌋₊) -
            rsPhiOne (sourcePhiParameter (sourceHeightScale t) ⌊sourceHeightScale t⌋₊) /
              sourceHeightScale t +
            rsPhiTwo (sourcePhiParameter (sourceHeightScale t) ⌊sourceHeightScale t⌋₊) /
              sourceHeightScale t ^ 2))| +
      (1 / 20) * (t / (2 * Real.pi)) ^ (-(7 / 4 : ℝ)) ≤
        (57 / 25) * (t / (2 * Real.pi)) ^ (-(7 / 4 : ℝ)) := by
  have ht0 : 0 < t := by nlinarith [Real.pi_pos]
  have he0 := sourceHeightScale_pos ht0
  have he : 2000 < sourceHeightScale t ^ 2 := by
    rw [sourceHeightScale_sq ht0.le, lt_div_iff₀ (by positivity)]
    linarith
  have h := normalized_zeta_R2_margin he0.le he hint
  rw [sourceTime_heightScale ht0.le, sourceHeightScale_sq ht0.le, sourceRealMainSum_cos] at h
  dsimp only [sourceRealCorrection] at h
  linarith

theorem normalized_zeta_R2_height_strict {t : ℝ}
    (ht : 4000 * Real.pi < t) (hint : ∀ k : ℤ, sourceHeightScale t ≠ k) :
    |normalizedCriticalZeta t -
      (2 * ∑ n ∈ Finset.range ⌊sourceHeightScale t⌋₊,
        Real.cos (criticalGammaArgument t - t * Real.log (n + 1)) / Real.sqrt (n + 1) +
        sourceSignedAmplitude (sourceHeightScale t) ⌊sourceHeightScale t⌋₊ *
          (rsPhi (sourcePhiParameter (sourceHeightScale t) ⌊sourceHeightScale t⌋₊) -
            rsPhiOne (sourcePhiParameter (sourceHeightScale t) ⌊sourceHeightScale t⌋₊) /
              sourceHeightScale t +
            rsPhiTwo (sourcePhiParameter (sourceHeightScale t) ⌊sourceHeightScale t⌋₊) /
              sourceHeightScale t ^ 2))| <
        (57 / 25) * (t / (2 * Real.pi)) ^ (-(7 / 4 : ℝ)) := by
  have ht0 : 0 < t := by nlinarith [Real.pi_pos]
  have hp : 0 < (t / (2 * Real.pi)) ^ (-(7 / 4 : ℝ)) := by positivity
  linarith [normalized_zeta_R2_height_margin ht hint]

#print axioms normalized_zeta_R0_strict
#print axioms normalized_zeta_R0_height_margin
#print axioms normalized_zeta_R0_height_strict
#print axioms normalized_zeta_R2_margin
#print axioms normalized_zeta_R2_strict
#print axioms normalized_zeta_R2_height_margin
#print axioms normalized_zeta_R2_height_strict
#print axioms normalized_source_seven_original_allocation
#print axioms critical_C2_absolute_mass
#print axioms critical_zeta_norm_at_height

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
