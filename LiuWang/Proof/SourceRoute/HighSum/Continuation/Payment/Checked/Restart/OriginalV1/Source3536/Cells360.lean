import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.LocalPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem cell36_0_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 0 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 0 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_0_paid :
    (∫ s in (((start + 0 / 2) : ℚ) : ℝ)..((((start + 0 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 17383547210 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_0_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_1_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 1 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 1 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_1_paid :
    (∫ s in (((start + 1 / 2) : ℚ) : ℝ)..((((start + 1 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 13937310823 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_1_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_2_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 2 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 2 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_2_paid :
    (∫ s in (((start + 2 / 2) : ℚ) : ℝ)..((((start + 2 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 11057628181 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_2_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_3_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 3 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 3 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_3_paid :
    (∫ s in (((start + 3 / 2) : ℚ) : ℝ)..((((start + 3 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 8686394532 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_3_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_4_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 4 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 4 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_4_paid :
    (∫ s in (((start + 4 / 2) : ℚ) : ℝ)..((((start + 4 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 6759982981 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_4_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_5_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 5 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 5 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_5_paid :
    (∫ s in (((start + 5 / 2) : ℚ) : ℝ)..((((start + 5 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 5214316874 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_5_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_6_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 6 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 6 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_6_paid :
    (∫ s in (((start + 6 / 2) : ℚ) : ℝ)..((((start + 6 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 3988385313 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_6_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_7_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 7 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 7 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_7_paid :
    (∫ s in (((start + 7 / 2) : ℚ) : ℝ)..((((start + 7 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 3026445772 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_7_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
