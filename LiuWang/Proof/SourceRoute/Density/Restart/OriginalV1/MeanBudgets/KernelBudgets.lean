import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.Moments
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.CriticalMean

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets

theorem kernel_quadratic_integrable (a b c : ℝ) :
    IntegrableOn (fun u : ℝ => sourceKernel u * (a + b * u + c * u ^ 2)) (Ioi 0) := by
  unfold IntegrableOn
  have h0 := (sourceKernel_integrable_tail 0).const_mul a
  have h1 := (kernel_moment_integrable 1).const_mul b
  have h2 := (kernel_moment_integrable 2).const_mul c
  convert! (h0.fun_add h1).fun_add h2 using 1
  ext u
  simp only [pow_one]
  ring

theorem kernel_quadratic_integral (a b c : ℝ) :
    (∫ u in Ioi (0 : ℝ), sourceKernel u * (a + b * u + c * u ^ 2)) =
      a / 3 + b * (Real.log 3 / 2) +
        c * ∫ u in Ioi (0 : ℝ), sourceKernel u * u ^ 2 := by
  have h0 := (sourceKernel_integrable_tail 0).const_mul a
  have h1 : IntegrableOn (fun u : ℝ => b * (sourceKernel u * u)) (Ioi 0) := by
    unfold IntegrableOn
    simpa using (kernel_moment_integrable 1).const_mul b
  have he : (fun u : ℝ => sourceKernel u * (a + b * u + c * u ^ 2)) =
      (fun u : ℝ => a * sourceKernel u + b * (sourceKernel u * u) +
        c * (sourceKernel u * u ^ 2)) := by ext u; ring
  rw [he, integral_add (h0.fun_add h1) ((kernel_moment_integrable 2).const_mul c),
    integral_add h0 h1, integral_const_mul, integral_const_mul, integral_const_mul,
    kernel_moment_zero, kernel_moment_one]
  ring

theorem kernel_quadratic_bound {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∫ u in Ioi (0 : ℝ), sourceKernel u * (a + b * u + c * u ^ 2)) ≤
      a / 3 + b * 0.55 + c * (125 / 81) := by
  rw [kernel_quadratic_integral]
  have h1 := mul_le_mul_of_nonneg_left
    (show Real.log 3 / 2 ≤ 0.55 by linarith [Real.log_three_lt_d9]) hb
  have h2 := mul_le_mul_of_nonneg_left kernel_moment_two hc
  linarith

theorem equation_3_44_integrable (y : ℝ) :
    IntegrableOn (fun u : ℝ => sourceKernel u * (12.508 * y) * Real.log y *
      (2 * 2.19021 * u + 2 * 2.906 + 2.19021 * y * u ^ 2 + 2.906 * y * u))
      (Ioi 0) := by
  unfold IntegrableOn
  convert! (kernel_quadratic_integrable (2 * 2.906)
    (2 * 2.19021 + 2.906 * y) (2.19021 * y)).const_mul (12.508 * y * Real.log y) using 1
  ext u
  ring

theorem equation_3_44_kernel {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      (∫ u in Ioi (0 : ℝ), sourceKernel u * (12.508 * y) * Real.log y *
        (2 * 2.19021 * u + 2 * 2.906 + 2.19021 * y * u ^ 2 + 2.906 * y * u)) ≤
      254.13 * y ^ 2 * Real.log y := by
  obtain ⟨hy', hL⟩ := source_height_log_bounds hy
  have he : (fun u : ℝ => sourceKernel u * (12.508 * y) * Real.log y *
      (2 * 2.19021 * u + 2 * 2.906 + 2.19021 * y * u ^ 2 + 2.906 * y * u)) =
      (fun u : ℝ => (12.508 * y * Real.log y) *
        (sourceKernel u * (2 * 2.906 + (2 * 2.19021 + 2.906 * y) * u +
          (2.19021 * y) * u ^ 2))) := by ext u; ring
  rw [he, integral_const_mul]
  have hm := kernel_quadratic_bound
    (a := 2 * 2.906) (b := 2 * 2.19021 + 2.906 * y) (c := 2.19021 * y)
    (by positivity) (by positivity)
  have hnum : (4 + (10 : ℝ) ^ (-7 : ℤ)) * 12.508 *
      (2 * 2.906 / 3 + (2 * 2.19021 + 2.906 * y) * 0.55 + (2.19021 * y) * (125 / 81)) ≤
      254.13 * y := by norm_num; linarith
  have hm' := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) * (12.508 * y * Real.log y) by positivity)
  have hn' := mul_le_mul_of_nonneg_right hnum
    (show 0 ≤ y * Real.log y by positivity)
  nlinarith

theorem equation_3_45_integrable (y : ℝ) :
    IntegrableOn (fun u : ℝ => sourceKernel u * (67.929 + 0.0003 * u) *
      Real.log y ^ 5) (Ioi 0) := by
  unfold IntegrableOn
  convert! (kernel_quadratic_integrable 67.929 0.0003 0).mul_const (Real.log y ^ 5) using 1
  ext u
  ring

theorem equation_3_45_kernel {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      (∫ u in Ioi (0 : ℝ), sourceKernel u * (67.929 + 0.0003 * u) * Real.log y ^ 5) ≤
      90.5727 * Real.log y ^ 5 := by
  have hL := (source_height_log_bounds hy).2
  have he : (fun u : ℝ => sourceKernel u * (67.929 + 0.0003 * u) * Real.log y ^ 5) =
      (fun u : ℝ => Real.log y ^ 5 * (sourceKernel u * (67.929 + 0.0003 * u + 0 * u ^ 2))) := by
    ext u; ring
  rw [he, integral_const_mul]
  have hm := kernel_quadratic_bound (a := 67.929) (b := 0.0003) (c := 0)
    (by norm_num) (by norm_num)
  have hm' := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) * Real.log y ^ 5 by positivity)
  norm_num at hm' ⊢
  nlinarith [show 0 ≤ Real.log y ^ 5 by positivity]

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets
