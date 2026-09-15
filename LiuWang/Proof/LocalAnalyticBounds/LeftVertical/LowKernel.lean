import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Integrand

/-!
# 低实部零点的实际居中核

先把完整差商识别为 `∫ x in 2.5..t, x^(rho-1)`，再估范数。
不拆出两个各含 `1/rho` 的项；即使零点靠近零也保留统一界。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

theorem real_centered_kernel_eq_integral {t : Real} {rho : Complex}
    (hrho : 0 < rho.re) :
    ((t : Complex) ^ rho - (2.5 : Complex) ^ rho) / rho =
      ∫ x : Real in (2.5 : Real)..t, (x : Complex) ^ (rho - 1) := by
  have h := integral_cpow (a := (2.5 : Real)) (b := t) (r := rho - 1)
    (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith))
  simpa only [sub_add_cancel, Complex.ofReal_ofNat, Complex.ofReal_ofScientific] using h.symm

theorem norm_real_centered_kernel_low_re_le {t : Real} (ht : 2.5 ≤ t)
    {rho : Complex} (hrho : 0 < rho.re) (hrhohi : rho.re ≤ (1 : Real) / 2) :
    ‖((t : Complex) ^ rho - (2.5 : Complex) ^ rho) / rho‖ ≤ 2 * Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  have hmajor := intervalIntegral.intervalIntegrable_rpow'
    (a := (2.5 : Real)) (b := t) (by norm_num : -(1 : Real) < -1 / 2)
  have hbound : ∀ x ∈ Set.Ioc (2.5 : Real) t,
      ‖(x : Complex) ^ (rho - 1)‖ ≤ x ^ (-(1 : Real) / 2) := by
    intro x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hx.1] : 1 ≤ x)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rw [real_centered_kernel_eq_integral hrho]
  calc
    _ ≤ ∫ x : Real in (2.5 : Real)..t, x ^ (-(1 : Real) / 2) :=
      intervalIntegral.norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall hbound) hmajor
    _ = 2 * (Real.sqrt t - Real.sqrt 2.5) := by
      rw [integral_rpow (Or.inl (by norm_num : -(1 : Real) < -1 / 2))]
      norm_num only [show -(1 : Real) / 2 + 1 = 1 / 2 by norm_num]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      ring
    _ ≤ 2 * Real.sqrt t := by linarith [Real.sqrt_nonneg (2.5 : Real)]

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
