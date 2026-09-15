import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.LocalPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem cell36_8_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 8 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 8 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_8_paid :
    (∫ s in (((start + 8 / 2) : ℚ) : ℝ)..((((start + 8 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 2279188822 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_8_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_9_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 9 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 9 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_9_paid :
    (∫ s in (((start + 9 / 2) : ℚ) : ℝ)..((((start + 9 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 1704131898 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_9_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_10_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 10 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 10 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_10_paid :
    (∫ s in (((start + 10 / 2) : ℚ) : ℝ)..((((start + 10 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 1265478470 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_10_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_11_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 11 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 11 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_11_paid :
    (∫ s in (((start + 11 / 2) : ℚ) : ℝ)..((((start + 11 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 933637513 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_11_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_12_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 12 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 12 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_12_paid :
    (∫ s in (((start + 12 / 2) : ℚ) : ℝ)..((((start + 12 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 684554546 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_12_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_13_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 13 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 13 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_13_paid :
    (∫ s in (((start + 13 / 2) : ℚ) : ℝ)..((((start + 13 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 498964850 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_13_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_14_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 14 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 14 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_14_paid :
    (∫ s in (((start + 14 / 2) : ℚ) : ℝ)..((((start + 14 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 361644737 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_14_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_15_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 15 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 15 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_15_paid :
    (∫ s in (((start + 15 / 2) : ℚ) : ℝ)..((((start + 15 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 260708798 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_15_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
