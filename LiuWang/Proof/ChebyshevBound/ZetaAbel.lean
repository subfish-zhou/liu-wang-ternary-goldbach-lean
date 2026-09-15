import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation
import Mathlib.Tactic

/-!
# 实际 ζ 的显式低高度零区

从实际 Abel 延拓公式控制积分余项，不用存在常数的零区。
这只支付低高度解析前缀，不是原域上的尖锐 Chebyshev 总量界。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace LiuWang.Proof.ChebyshevBound

theorem norm_abel_integral_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ 1 / s.re := by
  calc
    _ ≤ ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) := by
      apply norm_integral_le_of_norm_le
        (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one)
      exact ZetaAbelFractKernel.ae_bound_Ioi s
    _ = _ := by
      simpa only [one_div] using integral_Ioi_rpow_neg_re_sub_one hs

theorem zeta_eq_pole_mul_abel {s : ℂ} (hs : 1 / 10 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) *
      (1 - (s - 1) * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u) := by
  rw [riemannZeta_eq_zetaAbelContinuationFormula s ⟨hs1, hs⟩,
    zetaAbelContinuationFormula]
  field_simp
  ring

theorem norm_zeta_pole_factor_sub_one_le {s : ℂ} (hs : 0 < s.re) :
    ‖(1 - (s - 1) * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u) - 1‖ ≤
      ‖s - 1‖ / s.re := by
  rw [sub_sub_cancel_left, norm_neg, norm_mul, div_eq_mul_inv]
  simpa only [one_div] using
    mul_le_mul_of_nonneg_left (norm_abel_integral_le hs) (norm_nonneg (s - 1))

theorem riemannZeta_ne_zero_of_norm_sub_one_lt_re {s : ℂ}
    (hs : ‖s - 1‖ < s.re) : riemannZeta s ≠ 0 := by
  by_cases hs1 : s = 1
  · exact hs1 ▸ riemannZeta_one_ne_zero
  have hre : 1 / 10 < s.re := by
    have h := Complex.re_le_norm (1 - s)
    rw [norm_sub_rev] at h
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have hs0 : 0 < s.re := by linarith
  have hsn : s ≠ 0 := by
    intro h
    simp [h] at hs0
  rw [zeta_eq_pole_mul_abel hre hs1]
  apply mul_ne_zero (div_ne_zero hsn (sub_ne_zero.mpr hs1))
  intro hzero
  have h := norm_zeta_pole_factor_sub_one_le hs0
  rw [hzero] at h
  norm_num only [zero_sub, norm_neg, norm_one] at h
  have hlt : ‖s - 1‖ / s.re < 1 := (div_lt_one hs0).2 hs
  linarith

theorem riemannZeta_ne_zero_of_im_sq_lt {s : ℂ}
    (hs : 1 + s.im ^ 2 < 2 * s.re) : riemannZeta s ≠ 0 := by
  apply riemannZeta_ne_zero_of_norm_sub_one_lt_re
  have hs0 : 0 < s.re := by nlinarith [sq_nonneg s.im]
  have hnorm : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using Complex.sq_norm (s - 1)
  nlinarith [norm_nonneg (s - 1)]

theorem riemannZeta_ne_zero_low_rectangle {s : ℂ}
    (hre : 3 / 4 ≤ s.re) (him : |s.im| ≤ 1 / 2) : riemannZeta s ≠ 0 := by
  apply riemannZeta_ne_zero_of_im_sq_lt
  have himsq : s.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg s.im) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 him
  nlinarith

end LiuWang.Proof.ChebyshevBound
