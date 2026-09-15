import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Tangent bounds for the original low-height exponential factors

The logarithmic form of the original low-height integral has exponent
`c * z - a / z`, with `c = 1/2` or `c = -1/2`.  Its tangent is an upper
bound on the entire positive half-line.  The exact nonnegative remainder
below avoids introducing an unproved derivative or numerical hypothesis.

These lemmas do not certify the integral's `7.6e-6` budget.
-/

set_option autoImplicit false

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

/-- The tangent error is an explicit nonnegative quadratic remainder. -/
theorem linear_sub_div_tangent_remainder (a c z b : ℝ)
    (hz : z ≠ 0) (hb : b ≠ 0) :
    (c * b - a / b + (c + a / b ^ 2) * (z - b)) - (c * z - a / z) =
      a * (z - b) ^ 2 / (z * b ^ 2) := by
  field_simp
  ring

/-- A global tangent upper bound, with no upper restriction on `z`. -/
theorem linear_sub_div_le_tangent {a c z b : ℝ}
    (ha : 0 ≤ a) (hz : 0 < z) (hb : 0 < b) :
    c * z - a / z ≤ c * b - a / b + (c + a / b ^ 2) * (z - b) := by
  apply sub_nonneg.mp
  rw [linear_sub_div_tangent_remainder a c z b hz.ne' hb.ne']
  positivity

/-- A separable exponential upper bound for either original summand. -/
theorem exp_linear_sub_div_le_tangent {a c z b : ℝ}
    (ha : 0 ≤ a) (hz : 0 < z) (hb : 0 < b) :
    Real.exp (c * z - a / z) ≤
      Real.exp (c * b - a / b) * Real.exp ((c + a / b ^ 2) * (z - b)) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (linear_sub_div_le_tangent ha hz hb)

/-- Positivity of the exact original parameter, using only the original `L` domain. -/
theorem original_low_parameter_nonneg {L : ℝ} (hL : 3100 ≤ L) :
    0 ≤ (0.478 : ℝ) * (L + Real.log 0.001) := by
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1000 by norm_num)
  rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, Real.log_inv]
  apply mul_nonneg (by norm_num)
  linarith

/-- The original two exponent factors use `c = 1/2` and `c = -1/2`.
No extra numerical parameter assumption is introduced. -/
theorem original_low_exp_le_tangent {L c z b : ℝ}
    (hL : 3100 ≤ L) (hz : 0 < z) (hb : 0 < b) :
    Real.exp (c * z - 0.478 * (L + Real.log 0.001) / z) ≤
      Real.exp (c * b - 0.478 * (L + Real.log 0.001) / b) *
        Real.exp ((c + 0.478 * (L + Real.log 0.001) / b ^ 2) * (z - b)) :=
  exp_linear_sub_div_le_tangent (original_low_parameter_nonneg hL) hz hb

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
