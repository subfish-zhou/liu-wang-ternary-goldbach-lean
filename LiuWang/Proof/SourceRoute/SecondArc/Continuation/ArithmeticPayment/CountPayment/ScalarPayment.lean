import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.ScalarDomain
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.ExponentialIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

theorem coupled_scalar_payment {L : ℝ} (hL : 3100 ≤ L) :
    L * (∫ z in (3.36 * L ^ (3 : ℕ))..scaledGate L,
      coupledKernel (L ^ (3 : ℕ)) (L + Real.log 0.001) z) ≤ 0.000006510372 := by
  have hs := scaling_bounds hL
  have hr : 0 < scaling L := by linarith
  have hLp : 0 < L := by linarith
  have hb := scaledGate_bounds hL
  have hA : 1 < 3.36 * L ^ (3 : ℕ) := by
    have hp : 1 ≤ L ^ (3 : ℕ) := one_le_pow₀ (by linarith : 1 ≤ L)
    linarith
  have hAB : 3.36 * L ^ (3 : ℕ) ≤ scaledGate L := by
    have hp : 0 ≤ L ^ (3 : ℕ) := by positivity
    linarith [hb.1]
  have hi := coupled_integral_upper (P := L ^ (3 : ℕ)) (H := L + Real.log 0.001)
    (by positivity) hA hAB (scaledGate_phase hL).1
  have hl := log_scaledGate_bounds hL
  have hB : 0 < scaledGate L := lt_of_lt_of_le (by positivity) hb.1
  have hcoef0 : 0 ≤ (2 / 9 : ℝ) * Real.log (scaledGate L) +
      2 * (L ^ (3 : ℕ) / scaledGate L) * (4 * Real.log (scaledGate L) + 30) := by
    have hl0 := hl.1.le
    positivity
  have he : Real.exp (-0.478 * (L + Real.log 0.001) / Real.log (scaledGate L)) ≤
      Real.exp (-40.39 * scaling L) := by
    apply Real.exp_le_exp.mpr
    have hh := (scaledGate_phase hL).2
    simp only [div_eq_mul_inv] at hh ⊢
    linarith
  calc
    _ ≤ L * (Real.sqrt (scaledGate L) *
        ((2 / 9 : ℝ) * Real.log (scaledGate L) +
          2 * (L ^ (3 : ℕ) / scaledGate L) * (4 * Real.log (scaledGate L) + 30)) *
            Real.exp (-0.478 * (L + Real.log 0.001) / Real.log (scaledGate L))) :=
      mul_le_mul_of_nonneg_left hi hLp.le
    _ ≤ L * ((86000000 * scaling L ^ (4 : ℕ)) * (8.14 * scaling L) *
        Real.exp (-40.39 * scaling L)) := by
      apply mul_le_mul_of_nonneg_left _ hLp.le
      exact mul_le_mul
        (mul_le_mul (scaledGate_sqrt_bound hL) (scaledGate_coefficient hL)
          hcoef0 (by positivity)) he (Real.exp_pos _).le (by positivity)
    _ = (3100 * 86000000 * 8.14) *
        (scaling L ^ (7 : ℕ) * Real.exp (-40.39 * scaling L)) := by
      nth_rw 1 [hs.2]
      ring
    _ ≤ (3100 * 86000000 * 8.14) * Real.exp (-40.39 : ℝ) :=
      mul_le_mul_of_nonneg_left (gate_exponential_absorbs hs.1) (by norm_num)
    _ ≤ (3100 * 86000000 * 8.14) * 0.000000000000000003 :=
      mul_le_mul_of_nonneg_left fixed_gate_exponential (by norm_num)
    _ = _ := by norm_num

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
