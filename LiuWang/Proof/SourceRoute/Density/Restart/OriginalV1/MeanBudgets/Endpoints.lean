import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.KernelBudgets
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer.Transfer

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets

theorem equation_3_44 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hzmax : ∀ u : ℝ, 0 ≤ u → ∀ t ∈ Icc (-(y * u)) (y * u),
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ 12.5 * (2 + y * u))
    (hzmean : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        8 * (2 + y * u) ^ 2)
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y) :
    weightedMean y (1 / 2) ≤ 254.13 * y ^ 2 * Real.log y := by
  have hy0 : 0 < y := by linarith [(source_height_log_bounds hy).1]
  have hi := integral_mono_ae
    (kernel_M_integrable hy0 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num))
    (equation_3_44_integrable y) ?_
  · have hm := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 4 + (10 : ℝ) ^ (-7 : ℤ) by positivity)
    exact (equation_3_43_half hy).trans (hm.trans (equation_3_44_kernel hy))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hw := lemma_3_4_from_original_inputs hy hu.le
      (hzmax u hu.le) (hzmean u hu.le) (hchen24 u hu.le)
    have hm := mul_le_mul_of_nonneg_left hw (sourceKernel_pos u).le
    convert! hm using 1
    ring

theorem equation_3_44_from_3_36 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (h336 : ∀ t : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      Real.sqrt 2 * (2 + (1 / 2 + |t|)⁻¹) * Real.sqrt (1 / 2 + |t|))
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y) :
    weightedMean y (1 / 2) ≤ 254.13 * y ^ 2 * Real.log y := by
  have hy0 : 0 ≤ y := by linarith [(source_height_log_bounds hy).1]
  exact equation_3_44 hy
    (fun u hu => (zeta_inputs_of_3_36 (mul_nonneg hy0 hu) h336).1)
    (fun u hu => (zeta_inputs_of_3_36 (mul_nonneg hy0 hu) h336).2) hchen24

theorem equation_3_45 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    weightedMean y (1 + sourceDelta y) ≤ 90.5727 * Real.log y ^ 5 := by
  have hy0 : 0 < y := by linarith [(source_height_log_bounds hy).1]
  have hd : 0 < sourceDelta y := by
    rw [sourceDelta_eq_strip_delta]
    exact (Strip.delta_bounds (by linarith [(source_height_log_bounds hy).1])).1
  have hi := integral_mono_ae
    (kernel_M_integrable hy0 (by linarith : 0 < 1 + sourceDelta y) (by linarith))
    (equation_3_45_integrable y) ?_
  · have hm := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 4 + (10 : ℝ) ^ (-7 : ℤ) by positivity)
    exact (equation_3_43_right hy).trans (hm.trans (equation_3_45_kernel hy))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hm := mul_le_mul_of_nonneg_left (hchen14 u hu.le) (sourceKernel_pos u).le
    simpa only [mul_assoc] using hm

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets
