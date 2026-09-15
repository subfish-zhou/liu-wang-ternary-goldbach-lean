import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.RealPhaseBudget

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def sourceHeightScale (t : ℝ) : ℝ := Real.sqrt (t / (2 * Real.pi))

theorem sourceHeightScale_pos {t : ℝ} (ht : 0 < t) : 0 < sourceHeightScale t := by
  unfold sourceHeightScale
  positivity

theorem sourceTime_heightScale {t : ℝ} (ht : 0 ≤ t) :
    sourceTime (sourceHeightScale t) = t := by
  rw [sourceTime, sourceHeightScale, sourceSaddle_time_scale ht, Real.sq_sqrt ht]

theorem sourceLeadingArgument_heightScale {t : ℝ} (ht : 0 ≤ t) :
    sourceLeadingArgument (sourceHeightScale t) =
      t / 2 * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8 := by
  rw [sourceLeadingArgument, sourceTime_heightScale ht, sourceHeightScale,
    Real.log_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

theorem sourcePhaseRemainder_heightScale {t : ℝ} (ht : 0 ≤ t) :
    sourcePhaseRemainder (sourceHeightScale t) =
      t / 2 * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8 -
        criticalGammaArgument t := by
  rw [sourcePhaseRemainder, sourceLeadingArgument_heightScale ht, sourceTime_heightScale ht]

theorem sourceRealMainSum_cos (t : ℝ) (m : ℕ) :
    sourceRealMainSum t m = 2 * ∑ n ∈ Finset.range m,
      Real.cos (criticalGammaArgument t - t * Real.log (n + 1)) / Real.sqrt (n + 1) := by
  unfold sourceRealMainSum
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  ring

theorem normalized_zeta_seven_at_height {t : ℝ} {m : ℕ}
    (ht : 0 < t) (hm : 0 < m)
    (h0 : 0 < sourceHeightScale t - m) (h1 : sourceHeightScale t - m < 1) :
    normalizedCriticalZeta t =
      sourceRealMainSum t m +
        sourceSevenNormalized (sourceHeightScale t) m +
        sourceExpandedResidual (sourceHeightScale t) m := by
  simpa only [sourceTime_heightScale ht.le] using normalized_zeta_source_seven_residual hm h0 h1

theorem normalized_zeta_seven_real_budget_at_height {t : ℝ} {m : ℕ}
    (ht : 0 < t) (hm : 0 < m)
    (h0 : 0 < sourceHeightScale t - m) (h1 : sourceHeightScale t - m < 1) :
    |normalizedCriticalZeta t -
      (2 * ∑ n ∈ Finset.range m,
        Real.cos (criticalGammaArgument t - t * Real.log (n + 1)) / Real.sqrt (n + 1) +
        sourceSignedAmplitude (sourceHeightScale t) m *
          sourceRealCorrection (sourceHeightScale t) (sourcePhiParameter (sourceHeightScale t) m))| ≤
      |sourceExpandedResidual (sourceHeightScale t) m| +
        sourceHeightScale t ^ (-(1 / 2 : ℝ)) *
          sourceSevenRealBudget (sourceHeightScale t) (sourcePhiParameter (sourceHeightScale t) m) := by
  simpa only [sourceTime_heightScale ht.le, sourceRealMainSum_cos] using
    normalized_zeta_source_seven_real_budget hm h0 h1

#print axioms sourcePhaseRemainder_heightScale
#print axioms normalized_zeta_seven_real_budget_at_height

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
