import LiuWang.Proof.SingularSeries.Decimal.Kernel

/-!
# The original pure I11 decimal lower bound

The universal-product gate is discharged by an unconditional producer.
This concerns only the original J-cubed pure term, not the zero terms
of the full major arc or the ternary Goldbach theorem.
-/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SingularSeries.Decimal

theorem series_decimal_lower_bound {N : ℕ} (hodd : Odd N) :
    (1.3202 : ℝ) ≤ series N := by
  have h := two_mul_universalProduct_le_series hodd
  linarith [universalProduct_decimal]

theorem re_I11_decimal_lower_bound {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.656145 * (N : ℝ) ^ 2 ≤ (I11 N).re :=
  Uniform.re_I11_of_universal_decimal universalProduct_decimal hN hodd

end LiuWang.Proof.SingularSeries.Decimal
