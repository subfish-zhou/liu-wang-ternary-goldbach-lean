import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.LocalValues

set_option autoImplicit false
noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem realPrimitive_eval (A u t : ℚ) :
    (realPrimitive A u).eval (t : ℝ) = (↑((upperPrimitive A u).eval t) : ℝ) :=
  Polynomial.eval_map_apply (Rat.castHom ℝ) t

theorem realPrimitive_initial (A u : ℚ) : (realPrimitive A u).derivative.eval 0 = 1 := by
  norm_num [realPrimitive, upperPrimitive, Finset.sum_range_succ, coefficient,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]

theorem cell_integral_le_value {A u : ℚ} (hA : 0 ≤ A) (hu : 0 < u)
    (hres : ∀ t : ℝ, 0 ≤ t → 0 ≤ (odeResidual A u (realPrimitive A u).derivative).eval t)
    (hval : 0 ≤ (upperPrimitive A u).eval (1 / 2) - (upperPrimitive A u).eval 0) :
    (∫ s in (u : ℝ)..((u : ℝ) + 1 / 2), (3100 : ℝ) ^ 4 * Real.exp (phase A s)) ≤
      (cellValue A u : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have h := ode_integral_upper (A : ℝ) huR (by linarith : (u : ℝ) ≤ u + 1 / 2)
    (realPrimitive A u) (realPrimitive_initial A u) hres
  rw [add_sub_cancel_left,
    show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num,
    show (0 : ℝ) = ((0 : ℚ) : ℝ) by norm_num,
    realPrimitive_eval, realPrimitive_eval] at h
  have hphase : phase (A : ℝ) (u : ℝ) = -((u + A / u : ℚ) : ℝ) := by
    unfold phase
    push_cast
    ring
  have hx := exp_upper (x := u + A / u) (by positivity)
  rw [hphase] at h
  have hm := (h.trans (mul_le_mul_of_nonneg_right hx
    (by exact_mod_cast hval)))
  rw [intervalIntegral.integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 3100 ^ 4)
  convert! hh using 1
  · norm_num
  · unfold cellValue
    push_cast
    ring

theorem first_cell_paid :
    (∫ s in (start : ℝ)..((start : ℝ) + 1 / 2),
      (3100 : ℝ) ^ 4 * Real.exp (phase firstA s)) ≤ 125874837587 / 100000000000000 := by
  apply (cell_integral_le_value (by norm_num [firstA]) (by norm_num [start])
    local_first_residual (by
      norm_num [upperPrimitive, coefficient, firstA, start, Finset.sum_range_succ])).trans
  norm_num [cellValue, upperPrimitive, coefficient, firstA, start, expUpper, taylor12,
    Finset.sum_range_succ]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
