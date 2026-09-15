import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.ThreeLines
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.WeightedRight
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.DetectorMean
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HWeightedDetection

set_option autoImplicit false

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

open Strip

theorem actual_L2_three_lines {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Set.Icc (1 / 2) (1 + delta y)) :
    MeasureTheory.Integrable
      (fun t : ℝ => ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2) ∧
    weightedMean y σ ≤
      weightedMean y (1 / 2) ^ (1 - rightWeight y σ) *
        weightedMean y (1 + delta y) ^ rightWeight y σ :=
  ⟨regularG_strip_integrable hy hσ, weightedMean_interpolation hy hσ⟩

theorem actual_L2_explicit_prefix {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Set.Icc (1 / 2) (1 + delta y)) :
    weightedMean y σ ≤
      (230 * y ^ 2 * Real.log y) ^ (1 - rightWeight y σ) *
        (280 * Real.log y ^ 4) ^ rightWeight y σ := by
  have hw := weight_bounds hy hσ
  apply (weightedMean_interpolation hy hσ).trans
  exact mul_le_mul
    (Real.rpow_le_rpow (weightedMean_nonneg _ _) (weightedMean_critical_sharp hy) (by linarith))
    (Real.rpow_le_rpow (weightedMean_nonneg _ _)
      (weightedMean_moving_sharp hy) hw.1)
    (Real.rpow_nonneg (weightedMean_nonneg _ _) _)
    (Real.rpow_nonneg (by have := Sharp.log_ge_nine hy; positivity) _)

theorem actual_right_mean {y : ℝ} (hy : 10000 ≤ y) :
    (∀ T : ℝ, 0 ≤ T → M y (1 + delta y) T ≤
      (6 * T / (y - 1)) * Real.log y ^ 2 + 132 * Real.log y ^ 4) ∧
    MeasureTheory.Integrable
      (fun t : ℝ => ‖regularG y (((1 + delta y : ℝ) : ℂ) + t * Complex.I)‖ ^ 2) ∧
    weightedMean y (1 + delta y) ≤ 280 * Real.log y ^ 4 := by
  have hd := delta_bounds hy
  exact ⟨fun _ hT => M_moving_sharp hy hT,
    regularG_right_integrable hy le_rfl (by linarith), weightedMean_moving_sharp hy⟩

theorem actual_source_3_45 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    weightedMean y (1 + delta y) ≤ (905727 / 10000) * Real.log y ^ 5 :=
  moving_90_5727 hy

theorem actual_lemma_3_5 {y σ : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hσ : σ ∈ Set.Icc (1 / 2) (1 - delta y)) :
    M y σ y ≤ 1861 * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) ∧
    M y σ y ≤ (331839 / 100) * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) := by
  have hy' : 10000 ≤ y := by linarith [Sharp.log_six_ge_one]
  exact ⟨M_lemma_3_5_sharp hy' hσ, lemma_3_5 hy hσ⟩

theorem actual_H_vertical_budget {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Set.Icc (1 / 2) (1 - delta y)) :
    IntervalIntegrable (fun t : ℝ =>
      Real.log ‖H y ((σ : ℂ) + t * Complex.I)‖ -
        Real.log ‖H y ((2 : ℂ) + t * Complex.I)‖) MeasureTheory.volume (-y) y ∧
    (∫ t in -y..y,
      Real.log ‖H y ((σ : ℂ) + t * Complex.I)‖ -
        Real.log ‖H y ((2 : ℂ) + t * Complex.I)‖) ≤
      1861 * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) +
        16 * y / (y - 1) ^ 2 :=
  littlewood_vertical_budget hy hσ

theorem actual_H_closed_count {y a T ε : ℝ} (hy : 3 < y)
    (ha : a ≤ 2) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ a' ∈ Set.Ioo (a - ε) a, ∃ T' ∈ Set.Ioo T (T + ε),
      (∀ s ∈ RectangleBorder ((a' : ℂ) - T' * Complex.I) ((2 : ℂ) + T' * Complex.I),
        entireH y s ≠ 0) ∧
      RectangleBorderIntegrable (logDeriv (entireH y))
        ((a' : ℂ) - T' * Complex.I) ((2 : ℂ) + T' * Complex.I) ∧
      RectangleIntegral' (logDeriv (entireH y))
        ((a' : ℂ) - T' * Complex.I) ((2 : ℂ) + T' * Complex.I) =
        (detectorCount y ((a' : ℂ) - T' * Complex.I) ((2 : ℂ) + T' * Complex.I) : ℂ) ∧
      zetaDetectorRectangleCount ((a : ℂ) - T * Complex.I) ((2 : ℂ) + T * Complex.I) ≤
        detectorCount y ((a' : ℂ) - T' * Complex.I) ((2 : ℂ) + T' * Complex.I) :=
  closed_zeta_count_detected hy ha hT hε

theorem actual_H_weighted_count {y α ε : ℝ} (hy : 10000 ≤ y)
    (hα : α ≤ 2) (hε : 0 < ε) :
    ∃ a ∈ Set.Ioo (α - delta y - ε) (α - delta y), ∃ U ∈ Set.Ioo y (y + ε),
      (∀ s ∈ RectangleBorder ((a : ℂ) - U * Complex.I) ((2 : ℂ) + U * Complex.I),
        entireH y s ≠ 0) ∧
      RectangleBorderIntegrable (weightedDetectorKernel y ((a : ℂ) - U * Complex.I))
        ((a : ℂ) - U * Complex.I) ((2 : ℂ) + U * Complex.I) ∧
      delta y * (zetaDetectorRectangleCount
        ((α : ℂ) - y * Complex.I) ((2 : ℂ) + y * Complex.I) : ℝ) ≤
        (RectangleIntegral' (weightedDetectorKernel y ((a : ℂ) - U * Complex.I))
          ((a : ℂ) - U * Complex.I) ((2 : ℂ) + U * Complex.I)).re :=
  closed_zeta_weighted_detection (by linarith) hα (by linarith) (delta_bounds hy).1 hε

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
