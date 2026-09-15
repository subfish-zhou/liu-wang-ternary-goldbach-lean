import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer.Weight
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer.Kernel
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer.Finiteness
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.WeightedRight

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

def extendedWindow (y sigma u : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc (-u) u, ENNReal.ofReal (F y ((sigma : ℂ) + t * I))

def extendedWeightedMean (y sigma : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ENNReal.ofReal (‖regularG y ((sigma : ℂ) + t * I)‖ ^ 2)

theorem extendedWeightedMean_eq {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) :
    extendedWeightedMean y sigma = ENNReal.ofReal (weightedMean y sigma) := by
  exact (ofReal_integral_eq_lintegral_ofReal (regularG_integrable hy hs)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem extendedWindow_eq {y sigma u : ℝ} (hs1 : sigma ≠ 1) (hu : 0 ≤ u) :
    extendedWindow y sigma u = ENNReal.ofReal (M y sigma u) := by
  unfold extendedWindow GlobalZeroDensity.M
  rw [intervalIntegral.integral_of_le (by linarith : -u ≤ u),
    ← integral_Icc_eq_integral_Ioc]
  exact (ofReal_integral_eq_lintegral_ofReal
    (continuous_vertical_F y hs1).integrableOn_Icc
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem original_kernel_identity (y sigma : ℝ) (hy : 0 < y) :
    (∫⁻ t : ℝ, ENNReal.ofReal
      (F y ((sigma : ℂ) + t * I) / (2 + Real.exp (|t| / y)))) =
      ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (sourceKernel u) * extendedWindow y sigma (y * u) := by
  have h := sourceKernel_window_identity (F_measurable y sigma) y hy
  unfold extendedWindow
  rw [← h]
  apply lintegral_congr
  intro t
  rw [← ENNReal.ofReal_mul (show 0 ≤ F y ((sigma : ℂ) + t * I) from sq_nonneg _)]
  congr 1
  ring

theorem equation_3_43_extended {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) :
    extendedWeightedMean y sigma ≤ ENNReal.ofReal (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (sourceKernel u) * extendedWindow y sigma (y * u) := by
  have hy0 : 0 < y := by linarith [(source_height_log_bounds hy).1]
  rw [← original_kernel_identity y sigma hy0, ← lintegral_const_mul']
  · apply lintegral_mono_ae
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    have hp : (sigma : ℂ) + t * I ≠ 1 := by
      intro h; have hi := congrArg Complex.im h; simp at hi; exact ht hi
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (regularG_source_envelope hy hs hp)
  · exact ENNReal.ofReal_ne_top

theorem original_kernel_identity_real_lintegral {y sigma : ℝ}
    (hy : 0 < y) (hs1 : sigma ≠ 1) :
    (∫⁻ t : ℝ, ENNReal.ofReal
      (F y ((sigma : ℂ) + t * I) / (2 + Real.exp (|t| / y)))) =
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (sourceKernel u * M y sigma (y * u)) := by
  rw [original_kernel_identity y sigma hy]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [extendedWindow_eq hs1 (mul_nonneg hy.le hu.le),
    ENNReal.ofReal_mul (sourceKernel_pos u).le]

theorem kernel_M_integrable {y sigma : ℝ}
    (hy : 0 < y) (hs : 0 < sigma) (hs1 : sigma ≠ 1) :
    IntegrableOn (fun u : ℝ => sourceKernel u * M y sigma (y * u)) (Ioi 0) := by
  have hm : AEStronglyMeasurable
      (fun u : ℝ => sourceKernel u * M y sigma (y * u)) (volume.restrict (Ioi 0)) :=
    (sourceKernel_continuous.mul
      ((MeanInterpolation.continuous_M y hs1).comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hn : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ sourceKernel u * M y sigma (y * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (sourceKernel_pos u).le
      (M_integrable_nonneg y hs1 (mul_nonneg hy.le hu.le)).2
  apply (lintegral_ofReal_ne_top_iff_integrable hm hn).mp
  rw [← original_kernel_identity_real_lintegral hy hs1,
    ← ofReal_integral_eq_lintegral_ofReal (F_weighted_integrable hy hs hs1)
      (Filter.Eventually.of_forall (fun _ => by unfold F; positivity))]
  exact ENNReal.ofReal_ne_top

theorem original_kernel_identity_real {y sigma : ℝ}
    (hy : 0 < y) (hs : 0 < sigma) (hs1 : sigma ≠ 1) :
    (∫ t : ℝ, F y ((sigma : ℂ) + t * I) / (2 + Real.exp (|t| / y))) =
      ∫ u in Ioi (0 : ℝ), sourceKernel u * M y sigma (y * u) := by
  have hn : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ sourceKernel u * M y sigma (y * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (sourceKernel_pos u).le
      (M_integrable_nonneg y hs1 (mul_nonneg hy.le hu.le)).2
  have hnF : ∀ᵐ t : ℝ, 0 ≤ F y ((sigma : ℂ) + t * I) / (2 + Real.exp (|t| / y)) :=
    Filter.Eventually.of_forall (fun _ => by unfold F; positivity)
  have he := original_kernel_identity_real_lintegral hy hs1
  rw [← ofReal_integral_eq_lintegral_ofReal (F_weighted_integrable hy hs hs1) hnF,
    ← ofReal_integral_eq_lintegral_ofReal (kernel_M_integrable hy hs hs1) hn] at he
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg_of_ae hnF) (integral_nonneg_of_ae hn)).mp he

theorem equation_3_43 {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) (hs1 : sigma ≠ 1) :
    weightedMean y sigma ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      ∫ u in Ioi (0 : ℝ), sourceKernel u * M y sigma (y * u) := by
  have hy0 : 0 < y := by linarith [(source_height_log_bounds hy).1]
  have hs0 : 0 < sigma := by linarith [hs.1]
  have he := equation_3_43_extended hy hs
  rw [extendedWeightedMean_eq hy hs, ← original_kernel_identity y sigma hy0,
    ← ofReal_integral_eq_lintegral_ofReal (F_weighted_integrable hy0 hs0 hs1)
      (Filter.Eventually.of_forall (fun _ => by unfold F; positivity)),
    original_kernel_identity_real hy0 hs0 hs1,
    ← ENNReal.ofReal_mul (by positivity)] at he
  apply (ENNReal.ofReal_le_ofReal_iff (by
    apply mul_nonneg (by positivity)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (sourceKernel_pos u).le
      (M_integrable_nonneg y hs1 (mul_nonneg hy0.le hu.le)).2)).mp he

theorem equation_3_43_half {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    weightedMean y (1 / 2) ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      ∫ u in Ioi (0 : ℝ), sourceKernel u * M y (1 / 2) (y * u) := by
  have hd : 0 < sourceDelta y := by
    rw [sourceDelta_eq_strip_delta]
    exact (Strip.delta_bounds (by linarith [(source_height_log_bounds hy).1])).1
  exact equation_3_43 hy ⟨le_rfl, by linarith⟩ (by norm_num)

theorem equation_3_43_right {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    weightedMean y (1 + sourceDelta y) ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      ∫ u in Ioi (0 : ℝ), sourceKernel u * M y (1 + sourceDelta y) (y * u) := by
  have hd : 0 < sourceDelta y := by
    rw [sourceDelta_eq_strip_delta]
    exact (Strip.delta_bounds (by linarith [(source_height_log_bounds hy).1])).1
  exact equation_3_43 hy ⟨by linarith, le_rfl⟩ (by linarith)

theorem equation_3_43_one_extended {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    ENNReal.ofReal (weightedMean y 1) ≤ ENNReal.ofReal (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (sourceKernel u) * extendedWindow y 1 (y * u) := by
  have hd : 0 < sourceDelta y := by
    rw [sourceDelta_eq_strip_delta]
    exact (Strip.delta_bounds (by linarith [(source_height_log_bounds hy).1])).1
  have hs : (1 : ℝ) ∈ Icc (1 / 2) (1 + sourceDelta y) := ⟨by norm_num, by linarith⟩
  rw [← extendedWeightedMean_eq hy hs]
  exact equation_3_43_extended hy hs

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer
