import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.LocalPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem cell36_16_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 16 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 16 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_16_paid :
    (∫ s in (((start + 16 / 2) : ℚ) : ℝ)..((((start + 16 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 186979930 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_16_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_17_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 17 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 17 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_17_paid :
    (∫ s in (((start + 17 / 2) : ℚ) : ℝ)..((((start + 17 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 133443792 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_17_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_18_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 18 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 18 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_18_paid :
    (∫ s in (((start + 18 / 2) : ℚ) : ℝ)..((((start + 18 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 94789113 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_18_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_19_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 19 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 19 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_19_paid :
    (∫ s in (((start + 19 / 2) : ℚ) : ℝ)..((((start + 19 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 67028977 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_19_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_20_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 20 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 20 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_20_paid :
    (∫ s in (((start + 20 / 2) : ℚ) : ℝ)..((((start + 20 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 47194698 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_20_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_21_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 21 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 21 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_21_paid :
    (∫ s in (((start + 21 / 2) : ℚ) : ℝ)..((((start + 21 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 33092395 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_21_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_22_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 22 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 22 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_22_paid :
    (∫ s in (((start + 22 / 2) : ℚ) : ℝ)..((((start + 22 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 23112194 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_22_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_23_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 23 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 23 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_23_paid :
    (∫ s in (((start + 23 / 2) : ℚ) : ℝ)..((((start + 23 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 16080582 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_23_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
