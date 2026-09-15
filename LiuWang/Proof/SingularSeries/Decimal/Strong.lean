import LiuWang.Proof.SingularSeries.Decimal.Consumer

/-!
# 保留解析母界与实际截断误差的强纯主项

主出口不把 π 近似、不把 P(N) 换成原阈值，也不先退到 0.6601。
数值下界仅是该解析出口的可读推论；原六叶保持不变。
-/

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SingularSeries.Decimal

theorem fixed_kernel_strong :
    (0.660125 : ℝ) ≤
      (8 / (3.141593 : ℝ) ^ 2) * smallRatio * (1 - (3 / 40000 : ℝ)) := by
  norm_num [smallRatio, oddPrimes_hundred, a, b]

theorem universalProduct_strong : (0.660125 : ℝ) ≤ universalProduct :=
  fixed_kernel_strong.trans (pi_comparison.trans universalProduct_analytic_lower_bound)

theorem series_strong {N : ℕ} (hodd : Odd N) : (1.32025 : ℝ) ≤ series N := by
  linarith [two_mul_universalProduct_le_series hodd, universalProduct_strong]

theorem re_I11_analytic_lower_bound {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    ((0.997 : ℝ) ^ 2 *
        ((8 / Real.pi ^ 2) * smallRatio * (1 - (3 / 40000 : ℝ))) -
      (0.997 : ℝ) ^ 2 / 2 * (44 / sourceP N) -
      62.04 / sourceP N) * (N : ℝ) ^ 2 ≤ (I11 N).re := by
  apply le_trans _ (Uniform.re_I11_arithmetic_errors_paid hN hodd)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left universalProduct_analytic_lower_bound
    (sq_nonneg (0.997 : ℝ))
  linarith

theorem strong_decimal_margin :
    (0.65617 : ℝ) ≤
      (0.997 : ℝ) ^ 2 * 0.660125 -
      (0.997 : ℝ) ^ 2 / 2 * ((1.5 : ℝ) * 10 ^ (-9 : ℤ)) -
      62.04 / (3100 : ℝ) ^ 3 := by norm_num

theorem re_I11_strong {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.65617 * (N : ℝ) ^ 2 ≤ (I11 N).re := by
  have ht : (44 : ℝ) / sourceP N ≤ (1.5 : ℝ) * 10 ^ (-9 : ℤ) := by
    calc
      _ ≤ 44 / (3100 : ℝ) ^ 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (Uniform.sourceP_lower hN)
      _ ≤ _ := by norm_num
  have hw : (62.04 : ℝ) / sourceP N ≤ 62.04 / (3100 : ℝ) ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (Uniform.sourceP_lower hN)
  have hu := mul_le_mul_of_nonneg_left (fixed_kernel_strong.trans pi_comparison)
    (sq_nonneg (0.997 : ℝ))
  have htail := mul_le_mul_of_nonneg_left ht
    (by positivity : (0 : ℝ) ≤ (0.997 : ℝ) ^ 2 / 2)
  apply le_trans _ (re_I11_analytic_lower_bound hN hodd)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  linarith [strong_decimal_margin]

end LiuWang.Proof.SingularSeries.Decimal
