import LiuWang.Proof.SingularIntegral.Window

/-!
# 原三角域的 Fubini、Lebesgue 面积与有限复权积分

这里只对紧三角域上的可积函数使用 Fubini。闭端点与 `Ioc` 的
转换均由真实 Lebesgue 零测等式完成。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Interval

namespace LiuWang.Proof.SingularIntegral

theorem integral_triangle_indicator_slice (f : ℝ × ℝ → ℂ) (x : ℝ) :
    (∫ y : ℝ, triangle.indicator f (x, y)) =
      (Icc (0.001 : ℝ) 0.998).indicator
        (fun x => ∫ y in (0.001 : ℝ)..(0.999 - x), f (x, y)) x := by
  by_cases hx : x ∈ Icc (0.001 : ℝ) 0.998
  · rw [indicator_of_mem hx]
    have heq : (fun y : ℝ => triangle.indicator f (x, y)) =
        (Icc (0.001 : ℝ) (0.999 - x)).indicator (fun y => f (x, y)) := by
      ext y
      simp only [triangle, indicator_apply, mem_ofPred_eq, hx, true_and]
    rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx.2])]
  · rw [indicator_of_notMem hx]
    have heq : (fun y : ℝ => triangle.indicator f (x, y)) = 0 := by
      ext y
      simp only [triangle, indicator_apply, mem_ofPred_eq, hx, false_and, ↓reduceIte,
        Pi.zero_apply]
    simp [heq]

theorem integral_triangle_eq_iterated (f : ℝ × ℝ → ℂ) (hf : IntegrableOn f triangle) :
    (∫ x in triangle, f x) =
      ∫ x in (0.001 : ℝ)..0.998, ∫ y in (0.001 : ℝ)..(0.999 - x), f (x, y) := by
  rw [← integral_indicator triangle_measurableSet]
  change (∫ x, triangle.indicator f x ∂volume.prod volume) = _
  rw [integral_prod _ ((integrable_indicator_iff triangle_measurableSet).2 hf)]
  simp_rw [integral_triangle_indicator_slice]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0.001 : ℝ) ≤ 0.998)]

theorem triangle_outer_intervalIntegrable (f : ℝ × ℝ → ℂ) (hf : IntegrableOn f triangle) :
    IntervalIntegrable
      (fun x => ∫ y in (0.001 : ℝ)..(0.999 - x), f (x, y)) volume 0.001 0.998 := by
  have h := ((integrable_indicator_iff triangle_measurableSet).2 hf).integral_prod_left
  simp_rw [integral_triangle_indicator_slice] at h
  have hs := (integrable_indicator_iff measurableSet_Icc).1 h
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hs

theorem triangle_volume :
    volume triangle = ENNReal.ofReal ((0.997 : ℝ) ^ 2 / 2) := by
  have hf : IntegrableOn (fun _ : ℝ × ℝ => (1 : ℂ)) triangle :=
    continuousOn_const.integrableOn_compact triangle_isCompact
  have h := integral_triangle_eq_iterated (fun _ => (1 : ℂ)) hf
  rw [triangle_iterated_area_complex] at h
  simp only [setIntegral_const, Complex.real_smul, mul_one, measureReal_def] at h
  have hr : (volume triangle).toReal = (0.997 : ℝ) ^ 2 / 2 := by
    have hh := congrArg Complex.re h
    norm_num at hh ⊢
    exact hh
  rw [← hr, ENNReal.ofReal_toReal triangle_isCompact.measure_lt_top.ne]

theorem sourceSimplex_volume :
    volume sourceSimplex = ENNReal.ofReal ((0.997 : ℝ) ^ 2 / 2) := by
  rw [sourceSimplex_eq_triangle, triangle_volume]

theorem simplex_cpow_inner_intervalIntegrable (N : ℝ) (hN : 0 < N)
    (rho₁ rho₂ rho₃ : ℂ) {x : ℝ} (hx : x ∈ Icc (0.001 : ℝ) 0.998) :
    IntervalIntegrable (fun y : ℝ =>
      ((N * x : ℝ) : ℂ) ^ (rho₁ - 1) *
      ((N * y : ℝ) : ℂ) ^ (rho₂ - 1) *
      ((N * (1 - x - y) : ℝ) : ℂ) ^ (rho₃ - 1))
      volume 0.001 (0.999 - x) := by
  have hc : ContinuousOn (fun y : ℝ =>
      ((N * x : ℝ) : ℂ) ^ (rho₁ - 1) *
      ((N * y : ℝ) : ℂ) ^ (rho₂ - 1) *
      ((N * (1 - x - y) : ℝ) : ℂ) ^ (rho₃ - 1)) (Icc 0.001 (0.999 - x)) :=
    (simplex_cpow_continuousOn N hN rho₁ rho₂ rho₃).comp
      (f := fun y : ℝ => (x, y)) (s := Icc 0.001 (0.999 - x))
      (show ContinuousOn (fun y : ℝ => (x, y)) (Icc 0.001 (0.999 - x)) from
        (continuous_const.prodMk continuous_id).continuousOn)
      (fun y hy => show (x, y) ∈ triangle from ⟨hx, hy⟩)
  exact hc.intervalIntegrable_of_Icc (by linarith [hx.2])

theorem simplex_cpow_outer_intervalIntegrable (N : ℝ) (hN : 0 < N)
    (rho₁ rho₂ rho₃ : ℂ) :
    IntervalIntegrable (fun x : ℝ => ∫ y in (0.001 : ℝ)..(0.999 - x),
      ((N * x : ℝ) : ℂ) ^ (rho₁ - 1) *
      ((N * y : ℝ) : ℂ) ^ (rho₂ - 1) *
      ((N * (1 - x - y) : ℝ) : ℂ) ^ (rho₃ - 1)) volume 0.001 0.998 :=
  triangle_outer_intervalIntegrable _ (simplex_cpow_integrableOn N hN rho₁ rho₂ rho₃)

end LiuWang.Proof.SingularIntegral
