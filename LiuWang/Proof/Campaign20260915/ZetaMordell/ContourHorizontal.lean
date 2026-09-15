import LiuWang.Proof.Campaign20260915.ZetaMordell.ContourRegularization

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

theorem mordellRotated_bottom_line (t : ℝ) :
    mordellRotor * ((t : ℂ) - I) = mordellLine ((t - 1) / 4) := by
  unfold mordellRotor mordellLine
  push_cast
  ring_nf
  simp only [I_sq]
  ring

theorem mordellRotated_top_line (t : ℝ) :
    mordellRotor * ((t : ℂ) + I) = mordellLine ((t + 1) / 4) - 1 := by
  unfold mordellRotor mordellLine
  push_cast
  ring_nf
  simp only [I_sq]
  ring

theorem mordellRotated_bottom (a : ℂ) (t : ℝ) :
    mordellRotatedKernel a ((t : ℂ) - I) = mordellKernel a ((t - 1) / 4) / 4 := by
  unfold mordellRotatedKernel
  rw [mul_assoc (2 * Real.pi * I) mordellRotor ((t : ℂ) - I), mordellRotated_bottom_line]
  unfold mordellKernel mordellGaussian mordellDenominator mordellRotor
  ring

theorem mordellSpatialShift (a z : ℂ) :
    exp (Real.pi * I * (z - 1) ^ 2 + 2 * Real.pi * I * a * (z - 1)) /
        (exp (2 * Real.pi * I * (z - 1)) - 1) =
      -exp (-2 * Real.pi * I * a) *
        (exp (Real.pi * I * z ^ 2 + 2 * Real.pi * I * (a - 1) * z) /
          (exp (2 * Real.pi * I * z) - 1)) := by
  have hd : exp (2 * Real.pi * I * (z - 1)) = exp (2 * Real.pi * I * z) := by
    rw [mul_sub, mul_one, exp_sub, Complex.exp_two_pi_mul_I, div_one]
  have hn : exp (Real.pi * I * (z - 1) ^ 2 + 2 * Real.pi * I * a * (z - 1)) =
      -exp (-2 * Real.pi * I * a) *
        exp (Real.pi * I * z ^ 2 + 2 * Real.pi * I * (a - 1) * z) := by
    rw [show Real.pi * I * (z - 1) ^ 2 + 2 * Real.pi * I * a * (z - 1) =
      Real.pi * I + (-2 * Real.pi * I * a) +
        (Real.pi * I * z ^ 2 + 2 * Real.pi * I * (a - 1) * z) by ring,
      exp_add, exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hd, hn]
  ring

theorem mordellRotated_top (a : ℂ) (t : ℝ) :
    mordellRotatedKernel a ((t : ℂ) + I) =
      -exp (-2 * Real.pi * I * a) * mordellKernel (a - 1) ((t + 1) / 4) / 4 := by
  unfold mordellRotatedKernel
  rw [mul_assoc (2 * Real.pi * I) mordellRotor ((t : ℂ) + I), mordellRotated_top_line, mul_div_assoc,
    mordellSpatialShift]
  unfold mordellKernel mordellGaussian mordellDenominator mordellRotor
  ring

theorem mordellRotated_bottom_integrable (a : ℂ) :
    Integrable (fun t : ℝ => mordellRotatedKernel a ((t : ℂ) - I)) := by
  simp_rw [mordellRotated_bottom]
  have h := ((mordellKernel_integrable a).comp_div (by norm_num : (4 : ℝ) ≠ 0)).comp_add_right (-1)
  simpa only [sub_eq_add_neg] using h.div_const (4 : ℂ)

theorem mordellRotated_top_integrable (a : ℂ) :
    Integrable (fun t : ℝ => mordellRotatedKernel a ((t : ℂ) + I)) := by
  simp_rw [mordellRotated_top]
  have h := ((mordellKernel_integrable (a - 1)).comp_div
    (by norm_num : (4 : ℝ) ≠ 0)).comp_add_right 1
  exact (h.const_mul _).div_const _

theorem mordellRotated_bottom_integral (a : ℂ) :
    (∫ t : ℝ, mordellRotatedKernel a ((t : ℂ) - I)) = mordellIntegral a := by
  simp_rw [mordellRotated_bottom]
  rw [integral_div, integral_sub_right_eq_self (fun t : ℝ => mordellKernel a (t / 4)) 1,
    Measure.integral_comp_div]
  norm_num [smul_eq_mul, mordellIntegral]

theorem mordellRotated_top_integral (a : ℂ) :
    (∫ t : ℝ, mordellRotatedKernel a ((t : ℂ) + I)) =
      -exp (-2 * Real.pi * I * a) * mordellIntegral (a - 1) := by
  simp_rw [mordellRotated_top]
  rw [integral_div, integral_const_mul,
    integral_add_right_eq_self (fun t : ℝ => mordellKernel (a - 1) (t / 4)) 1,
    Measure.integral_comp_div]
  norm_num [smul_eq_mul, mordellIntegral]
  ring

theorem mordellRegular_horizontal_difference (a : ℂ) (t : ℝ) :
    mordellRegularKernel a ((t : ℂ) - I) - mordellRegularKernel a ((t : ℂ) + I) =
      (mordellRotatedKernel a ((t : ℂ) - I) - mordellRotatedKernel a ((t : ℂ) + I)) -
        ((2 * Real.pi * I : ℂ)⁻¹ / ((t : ℂ) - I) -
          (2 * Real.pi * I : ℂ)⁻¹ / ((t : ℂ) + I)) := by
  have hm : (t : ℂ) - I ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this
  have hp : (t : ℂ) + I ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this
  rw [mordellRegularKernel_eq a (by simp) hm, mordellRegularKernel_eq a (by simp) hp]
  ring

theorem mordellRegular_horizontal_integrable (a : ℂ) :
    Integrable (fun t : ℝ =>
      mordellRegularKernel a ((t : ℂ) - I) - mordellRegularKernel a ((t : ℂ) + I)) := by
  simp_rw [mordellRegular_horizontal_difference]
  exact ((mordellRotated_bottom_integrable a).sub (mordellRotated_top_integrable a)).sub
    mordellPole_difference_integrable

theorem mordellRegular_horizontal_integral (a : ℂ) :
    (∫ t : ℝ, mordellRegularKernel a ((t : ℂ) - I) -
      mordellRegularKernel a ((t : ℂ) + I)) =
        mordellIntegral a + exp (-2 * Real.pi * I * a) * mordellIntegral (a - 1) - 1 := by
  simp_rw [mordellRegular_horizontal_difference]
  rw [integral_sub
    (f := fun t : ℝ => mordellRotatedKernel a ((t : ℂ) - I) - mordellRotatedKernel a ((t : ℂ) + I))
    ((mordellRotated_bottom_integrable a).sub (mordellRotated_top_integrable a))
    mordellPole_difference_integrable,
    integral_sub (mordellRotated_bottom_integrable a) (mordellRotated_top_integrable a),
    mordellRotated_bottom_integral, mordellRotated_top_integral, mordellPole_difference_integral]
  ring

end LiuWang.Proof.Campaign20260915.ZetaMordell
