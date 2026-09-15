import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.LocalPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem cell35_0_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA (((start + 0 / 2) : ℚ) : ℝ) (realPrimitive firstA (start + 0 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell35_0_paid :
    (∫ s in (((start + 0 / 2) : ℚ) : ℝ)..((((start + 0 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 125874837587 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell35_0_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell35_1_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA (((start + 1 / 2) : ℚ) : ℝ) (realPrimitive firstA (start + 1 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell35_1_paid :
    (∫ s in (((start + 1 / 2) : ℚ) : ℝ)..((((start + 1 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 97163141606 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell35_1_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell35_2_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA (((start + 2 / 2) : ℚ) : ℝ) (realPrimitive firstA (start + 2 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell35_2_paid :
    (∫ s in (((start + 2 / 2) : ℚ) : ℝ)..((((start + 2 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 74323404216 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell35_2_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell35_3_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA (((start + 3 / 2) : ℚ) : ℝ) (realPrimitive firstA (start + 3 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell35_3_paid :
    (∫ s in (((start + 3 / 2) : ℚ) : ℝ)..((((start + 3 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 56367533309 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell35_3_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell35_4_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA (((start + 4 / 2) : ℚ) : ℝ) (realPrimitive firstA (start + 4 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell35_4_paid :
    (∫ s in (((start + 4 / 2) : ℚ) : ℝ)..((((start + 4 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 42404705485 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell35_4_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell35_5_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA (((start + 5 / 2) : ℚ) : ℝ) (realPrimitive firstA (start + 5 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell35_5_paid :
    (∫ s in (((start + 5 / 2) : ℚ) : ℝ)..((((start + 5 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 31656906245 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell35_5_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell35_6_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA (((start + 6 / 2) : ℚ) : ℝ) (realPrimitive firstA (start + 6 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell35_6_paid :
    (∫ s in (((start + 6 / 2) : ℚ) : ℝ)..((((start + 6 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 23462105089 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell35_6_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell35_7_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA (((start + 7 / 2) : ℚ) : ℝ) (realPrimitive firstA (start + 7 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell35_7_paid :
    (∫ s in (((start + 7 / 2) : ℚ) : ℝ)..((((start + 7 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 17269201596 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell35_7_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
