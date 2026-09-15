import LiuWang.Proof.Campaign20260915.Totient.RSPsiDifference
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Totient

def rsMainPrimitive (m : ℕ) (x : ℝ) : ℝ := x ^ (m + 1) / (m + 1).factorial

theorem rsMainPrimitive_deriv (m : ℕ) (x : ℝ) :
    HasDerivAt (rsMainPrimitive (m + 1)) (rsMainPrimitive m x) x := by
  have hd := (hasDerivAt_pow (m + 1 + 1) x).div_const
    ((m + 1 + 1).factorial : ℝ)
  convert! hd using 1
  dsimp [rsMainPrimitive]
  rw [Nat.factorial_succ (m + 1)]
  push_cast
  have hf : ((m + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

theorem rsMainPrimitive_difference (h : ℝ) (m : ℕ) (x : ℝ) :
    fwdDiff h (rsMainPrimitive (m + 1)) x =
      ∫ t in (0 : ℝ)..h, rsMainPrimitive m (x + t) := by
  rw [intervalIntegral.integral_comp_add_left, add_zero]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => rsMainPrimitive_deriv m y)
    (by apply Continuous.intervalIntegrable; unfold rsMainPrimitive; fun_prop)).symm

theorem rsMainPrimitive_finite_difference (h : ℝ) (m : ℕ) (x : ℝ) :
    (fwdDiff h)^[m] (rsMainPrimitive m) x =
      h ^ m * (x + (m : ℝ) * h / 2) := by
  induction m generalizing x with
  | zero => simp [rsMainPrimitive]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have he : fwdDiff h (rsMainPrimitive (m + 1)) =
        fun y => ∫ t in (0 : ℝ)..h, rsMainPrimitive m (y + t) :=
      funext (rsMainPrimitive_difference h m)
    rw [he, rs_difference_integral h
      (fun a b => (by
        apply Continuous.intervalIntegrable
        unfold rsMainPrimitive
        fun_prop : IntervalIntegrable (rsMainPrimitive m) volume a b))]
    simp_rw [ih]
    have hlin : (∫ t in (0 : ℝ)..h, x + t) = h * x + h ^ 2 / 2 := by
      calc
        _ = (∫ _t in (0 : ℝ)..h, x) + ∫ t in (0 : ℝ)..h, t :=
          intervalIntegral.integral_add intervalIntegrable_const
            (continuous_id.intervalIntegrable _ _)
        _ = _ := by simp
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (by
        exact (continuous_const.add continuous_id).intervalIntegrable _ _)
        intervalIntegrable_const, hlin]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    push_cast
    rw [pow_succ]
    ring

theorem rsMainPrimitive_normalized_difference {h : ℝ} (hh : 0 < h)
    (m : ℕ) (x : ℝ) :
    (fwdDiff h)^[m] (rsMainPrimitive m) x / h ^ m = x + (m : ℝ) * h / 2 := by
  rw [rsMainPrimitive_finite_difference]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hh.ne')

theorem rsMainPrimitive_original_two_sided {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x)
    (m : ℕ) :
    (fwdDiff (δ * x))^[m] (rsMainPrimitive m) x / (δ * x) ^ m =
        x + (m : ℝ) * δ * x / 2 ∧
      (fwdDiff (δ * x))^[m] (rsMainPrimitive m) (x - (m : ℝ) * (δ * x)) /
        (δ * x) ^ m = x - (m : ℝ) * δ * x / 2 := by
  rw [rsMainPrimitive_normalized_difference (mul_pos hδ hx),
    rsMainPrimitive_normalized_difference (mul_pos hδ hx)]
  constructor <;> ring

#print axioms rsMainPrimitive_deriv
#print axioms rsMainPrimitive_difference
#print axioms rsMainPrimitive_finite_difference
#print axioms rsMainPrimitive_normalized_difference
#print axioms rsMainPrimitive_original_two_sided

end LiuWang.Proof.Campaign20260915.Totient
