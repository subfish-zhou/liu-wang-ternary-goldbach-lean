import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.LocalTaylor

set_option autoImplicit false
noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

def start : ℚ := 25329413 / 1000000
def firstA : ℚ := 3100 / (9645908801 / 1000000000)
def secondA : ℚ := (12 / 100) * 3100

def realPrimitive (A u : ℚ) : ℝ[X] := (upperPrimitive A u).map (Rat.castHom ℝ)

def cellValue (A u : ℚ) : ℚ :=
  (3100 : ℚ) ^ 4 * expUpper (u + A / u) *
    ((upperPrimitive A u).eval (1 / 2) - (upperPrimitive A u).eval 0)

def roundedCell (A u : ℚ) : ℚ := (⌈cellValue A u * 100000000000000⌉ : ℚ) / 100000000000000

theorem start_le_lower : (start : ℝ) ≤ lower 3100 := by
  change (start : ℝ) ≤ Real.log (3.36 * 3100 ^ 3)
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3.36 * 3100 ^ 3)).mpr
  have ht := Real.exp_bound' (x := (329413 / 1000000 : ℝ)) (by norm_num) (by norm_num)
    (n := 12) (by norm_num)
  have he : Real.exp (329413 / 1000000 : ℝ) ≤
      (∑ k ∈ Finset.range 12, (329413 / 1000000 : ℝ) ^ k / k.factorial) + 1 / 1000000000 := by
    have hr : (329413 / 1000000 : ℝ) ^ 12 * (12 + 1) / ((12 : ℕ).factorial * 12) ≤
        1 / 1000000000 := by norm_num
    linarith
  have hpow := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 25
  rw [← Real.exp_nat_mul] at hpow
  norm_num only [Nat.cast_ofNat, mul_one] at hpow
  have hh := mul_le_mul hpow he (Real.exp_pos _).le (by positivity)
  rw [← Real.exp_add] at hh
  norm_num [Finset.sum_range_succ] at hh
  norm_num [start]
  exact hh.trans (by norm_num)

theorem local_first_residual (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (odeResidual firstA start (realPrimitive firstA start).derivative).eval t := by
  norm_num [odeResidual, realPrimitive, upperPrimitive, firstA, start, coefficient,
    Finset.sum_range_succ, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring_nf
  nlinarith only [pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

#norm_num [roundedCell, cellValue, upperPrimitive, firstA, start, coefficient,
  expUpper, taylor12, Finset.sum_range_succ] : roundedCell firstA start

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
