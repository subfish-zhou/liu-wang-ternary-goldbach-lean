import LiuWang.Proof.SingularSeries.Decimal.Comparison
import Mathlib.Analysis.Real.Pi.Bounds

/-! The fixed 0..100 arithmetic kernel, after the unbounded analytic comparison. -/

set_option autoImplicit false
noncomputable section
open Finset

namespace LiuWang.Proof.SingularSeries.Decimal

theorem oddPrimes_hundred :
    oddPrimes 100 =
      {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
        61, 67, 71, 73, 79, 83, 89, 97} := by decide

theorem fixed_kernel :
    (0.6601 : ℝ) ≤ (8 / (3.141593 : ℝ) ^ 2) * smallRatio * (1 - (3 / 40000 : ℝ)) := by
  norm_num [smallRatio, oddPrimes_hundred, a, b]

theorem pi_comparison :
    (8 / (3.141593 : ℝ) ^ 2) * smallRatio * (1 - (3 / 40000 : ℝ)) ≤
      (8 / Real.pi ^ 2) * smallRatio * (1 - (3 / 40000 : ℝ)) := by
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ smallRatio_pos.le
  apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos Real.pi_pos)
  nlinarith [Real.pi_lt_d6, Real.pi_pos]

theorem universalProduct_decimal : (0.6601 : ℝ) ≤ universalProduct :=
  fixed_kernel.trans (pi_comparison.trans universalProduct_analytic_lower_bound)

end LiuWang.Proof.SingularSeries.Decimal
