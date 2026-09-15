import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.LocalPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem cell36_24_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 24 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 24 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_24_paid :
    (∫ s in (((start + 24 / 2) : ℚ) : ℝ)..((((start + 24 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 11147461 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_24_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_25_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 25 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 25 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_25_paid :
    (∫ s in (((start + 25 / 2) : ℚ) : ℝ)..((((start + 25 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 7700629 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_25_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_26_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 26 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 26 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_26_paid :
    (∫ s in (((start + 26 / 2) : ℚ) : ℝ)..((((start + 26 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 5301659 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_26_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_27_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 27 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 27 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_27_paid :
    (∫ s in (((start + 27 / 2) : ℚ) : ℝ)..((((start + 27 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 3638219 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_27_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_28_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 28 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 28 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_28_paid :
    (∫ s in (((start + 28 / 2) : ℚ) : ℝ)..((((start + 28 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 2488920 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_28_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_29_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 29 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 29 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_29_paid :
    (∫ s in (((start + 29 / 2) : ℚ) : ℝ)..((((start + 29 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 1697573 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_29_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_30_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 30 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 30 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_30_paid :
    (∫ s in (((start + 30 / 2) : ℚ) : ℝ)..((((start + 30 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 1154489 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_30_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

theorem cell36_31_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual secondA (((start + 31 / 2) : ℚ) : ℝ) (realPrimitive secondA (start + 31 / 2)).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, secondA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

theorem cell36_31_paid :
    (∫ s in (((start + 31 / 2) : ℚ) : ℝ)..((((start + 31 / 2) : ℚ) : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase secondA s)) ≤ 782963 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA, secondA]) (by norm_num [start])
    cell36_31_residual (by
      norm_num [upperPrimitive, coefficient, firstA, secondA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, secondA, start, expUpper, taylor12,
    Finset.sum_range_succ]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
