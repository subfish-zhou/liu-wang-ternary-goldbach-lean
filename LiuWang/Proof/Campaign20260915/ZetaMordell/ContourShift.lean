import LiuWang.Proof.Campaign20260915.ZetaMordell.ContourHorizontal
import LiuWang.Proof.Campaign20260915.ZetaMordell.ContourVertical
import LiuWang.Proof.Campaign20260915.ZetaMordell.SiegelOrientation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Filter Set
open scoped Real Topology ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

theorem mordellRegular_horizontal_continuous (a : ℂ) {y : ℝ} (hy : |y| ≤ 1) :
    Continuous (fun t : ℝ => mordellRegularKernel a ((t : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (mordellRegularKernel_analytic a (by simpa using hy)).continuousAt.comp (by fun_prop)

theorem mordellRegular_rectangle (a : ℂ) (T : ℝ) :
    (∫ t in -T..T, mordellRegularKernel a ((t : ℂ) - I) -
      mordellRegularKernel a ((t : ℂ) + I)) +
      I * (∫ y in (-1 : ℝ)..1, mordellRegularKernel a ((T : ℂ) + y * I)) -
      I * (∫ y in (-1 : ℝ)..1, mordellRegularKernel a ((-T : ℝ) + y * I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (mordellRegularKernel a) ((-T : ℝ) - I) ((T : ℂ) + I) (by
      intro z hz
      have hy := hz.2
      norm_num at hy
      exact (mordellRegularKernel_analytic a (abs_le.mpr hy)).differentiableAt.differentiableWithinAt)
  have hm : Continuous (fun t : ℝ => mordellRegularKernel a ((t : ℂ) - I)) := by
    simpa [sub_eq_add_neg] using mordellRegular_horizontal_continuous a (y := -1) (by norm_num)
  have hp : Continuous (fun t : ℝ => mordellRegularKernel a ((t : ℂ) + I)) := by
    simpa using mordellRegular_horizontal_continuous a (y := 1) (by norm_num)
  rw [intervalIntegral.integral_sub (hm.intervalIntegrable _ _) (hp.intervalIntegrable _ _)]
  simpa [smul_eq_mul, sub_eq_add_neg] using h

theorem mordellIntegral_contour_shift (a : ℂ) :
    mordellIntegral a + exp (-2 * Real.pi * I * a) * mordellIntegral (a - 1) = 1 := by
  have hh := intervalIntegral_tendsto_integral (mordellRegular_horizontal_integrable a)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  simp only [id_eq] at hh
  have hr := mordellRegular_vertical_tendsto a tendsto_abs_atTop_atTop
  have hl := mordellRegular_vertical_tendsto (T := fun T : ℝ => -T) a
    (by simpa only [abs_neg] using tendsto_abs_atTop_atTop)
  have hlimit := (hh.add (hr.const_mul I)).sub (hl.const_mul I)
  have he : (∫ t : ℝ, mordellRegularKernel a ((t : ℂ) - I) -
      mordellRegularKernel a ((t : ℂ) + I)) = 0 := by
    apply tendsto_nhds_unique (by simpa only [mul_zero, add_zero, sub_zero] using hlimit)
    have hfun : (fun T : ℝ =>
      (∫ t in -T..T, mordellRegularKernel a ((t : ℂ) - I) -
        mordellRegularKernel a ((t : ℂ) + I)) +
        I * (∫ y in (-1 : ℝ)..1, mordellRegularKernel a ((T : ℂ) + y * I)) -
        I * (∫ y in (-1 : ℝ)..1, mordellRegularKernel a ((-T : ℝ) + y * I))) =
        fun _ => 0 := funext (mordellRegular_rectangle a)
    rw [hfun]
    exact tendsto_const_nhds
  rw [mordellRegular_horizontal_integral] at he
  exact sub_eq_zero.mp he

theorem siegelIntegral_contour_shift (u : ℂ) :
    siegelIntegral u = exp (-2 * Real.pi * I * u) * siegelIntegral (u + 1) + 1 := by
  have h := congrArg conj (mordellIntegral_contour_shift (1 / 2 - conj u))
  simp only [map_add, map_mul, map_one, ← Complex.exp_conj, map_neg, conj_ofNat,
    conj_ofReal, conj_I, map_sub, map_div₀, conj_conj] at h
  have he : exp (-2 * (Real.pi : ℂ) * -I * (1 / 2 - u)) =
      -exp (-2 * Real.pi * I * u) := by
    rw [show -2 * (Real.pi : ℂ) * -I * (1 / 2 - u) =
      Real.pi * I + (-2 * Real.pi * I * u) by ring, exp_add, Complex.exp_pi_mul_I]
    ring
  rw [he, ← siegelIntegral_conj] at h
  have hs : 1 / 2 - conj u - 1 = 1 / 2 - conj (u + 1) := by simp; ring
  rw [hs, ← siegelIntegral_conj] at h
  linear_combination h

end LiuWang.Proof.Campaign20260915.ZetaMordell
