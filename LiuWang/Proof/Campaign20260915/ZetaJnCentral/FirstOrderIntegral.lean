import LiuWang.Proof.Campaign20260915.ZetaJnCentral.FirstOrderRemainder
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem power_gaussian_third (n : ℕ) (y : ℝ) :
    |y| ^ n * Real.exp (-Real.pi / 3 * y ^ 2) ≤
      3 * (n.factorial : ℝ) * Real.exp (-Real.pi / 6 * y ^ 2) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp |y| (abs_nonneg y) n)
  have hx : |y| - Real.pi / 3 * y ^ 2 ≤ 1 - Real.pi / 6 * y ^ 2 := by
    nlinarith [sq_nonneg (|y| - 2), sq_abs y,
      mul_nonneg (show 0 ≤ Real.pi - 2 by linarith [Real.two_le_pi]) (sq_nonneg y)]
  calc
    _ ≤ (n.factorial : ℝ) * (Real.exp |y| * Real.exp (-Real.pi / 3 * y ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hp (Real.exp_pos (-Real.pi / 3 * y ^ 2)).le]
    _ ≤ (n.factorial : ℝ) * Real.exp (1 + (-Real.pi / 6 * y ^ 2)) := by
      rw [← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hf.le
    _ ≤ _ := by
      rw [Real.exp_add]
      nlinarith [mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
        (mul_nonneg hf.le (Real.exp_pos (-Real.pi / 6 * y ^ 2)).le)]

def firstOrderGaussianConstant (sigma : ℝ) : ℝ :=
  3 * (3 / 2 * |sigma - 1| * (1 + 1 / (Real.sqrt 2 * Real.pi)) +
    4 * Real.pi / 3 * (6 + 2 / (Real.sqrt 2 * Real.pi)))

theorem firstOrderGaussianConstant_nonneg (sigma : ℝ) :
    0 ≤ firstOrderGaussianConstant sigma := by
  unfold firstOrderGaussianConstant
  positivity

theorem firstOrderPolynomial_gaussian (sigma y : ℝ) :
    firstOrderPolynomial sigma y * (|y| + 1 / (Real.sqrt 2 * Real.pi)) *
        Real.exp (-Real.pi / 3 * y ^ 2) ≤
      firstOrderGaussianConstant sigma * Real.exp (-Real.pi / 6 * y ^ 2) := by
  have h0 := power_gaussian_third 0 y
  have h1 := power_gaussian_third 1 y
  have h2 := power_gaussian_third 2 y
  have h3 := power_gaussian_third 3 y
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, pow_zero, pow_one,
    one_mul, mul_one, sq_abs] at h0 h1 h2 h3
  have hy3 : |y| ^ 3 = y ^ 2 * |y| := by rw [pow_succ, sq_abs]
  rw [hy3] at h3
  have ha : 0 ≤ 3 / 2 * |sigma - 1| := by positivity
  have hb : 0 ≤ 4 * Real.pi / 3 := by positivity
  have hc : 0 ≤ 1 / (Real.sqrt 2 * Real.pi) := by positivity
  have hh0 := mul_le_mul_of_nonneg_left h0 (mul_nonneg ha hc)
  have hh1 := mul_le_mul_of_nonneg_left h1 ha
  have hh2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hb hc)
  have hh3 := mul_le_mul_of_nonneg_left h3 hb
  unfold firstOrderPolynomial firstOrderGaussianConstant
  linear_combination hh0 + hh1 + hh2 + hh3

theorem gaussian_interval_le_full {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b) :
    (∫ y : ℝ in a..b, Real.exp (-c * y ^ 2)) ≤ Real.sqrt (Real.pi / c) := by
  rw [intervalIntegral.integral_of_le hab, ← integral_gaussian c]
  exact setIntegral_le_integral (integrable_exp_neg_mul_sq hc)
    (Filter.Eventually.of_forall (fun y => (Real.exp_pos (-c * y ^ 2)).le))

def firstOrderJnConstant (sigma : ℝ) : ℝ :=
  Real.exp (3 / 4 * |sigma - 1|) * firstOrderGaussianConstant sigma * Real.sqrt 6

theorem jn_one_source_order (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m 1 y‖ ≤
      firstOrderJnConstant sigma / eta := by
  rw [intervalIntegral.integral_symm (-eta / 2) (eta / 2), norm_neg]
  have hC : 0 ≤ Real.exp (3 / 4 * |sigma - 1|) / eta *
      firstOrderGaussianConstant sigma :=
    mul_nonneg (by positivity) (firstOrderGaussianConstant_nonneg sigma)
  have hb (y : ℝ) (hy : y ∈ Icc (-eta / 2) (eta / 2)) :
      ‖rsJnIntegrand sigma eta m 1 y‖ ≤
        (Real.exp (3 / 4 * |sigma - 1|) / eta * firstOrderGaussianConstant sigma) *
          Real.exp (-Real.pi / 6 * y ^ 2) := by
    have hy' : |y| ≤ eta / 2 := abs_le.mpr (by simpa only [mem_Icc, neg_div] using hy)
    apply (jn_one_pointwise sigma he hy' hm0 hm1).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (firstOrderPolynomial_gaussian sigma y)
      (by positivity : 0 ≤ Real.exp (3 / 4 * |sigma - 1|) / eta)
  have hi : IntervalIntegrable (fun y : ℝ =>
      (Real.exp (3 / 4 * |sigma - 1|) / eta * firstOrderGaussianConstant sigma) *
        Real.exp (-Real.pi / 6 * y ^ 2)) volume (-eta / 2) (eta / 2) :=
    (by fun_prop : Continuous (fun y : ℝ =>
      (Real.exp (3 / 4 * |sigma - 1|) / eta * firstOrderGaussianConstant sigma) *
        Real.exp (-Real.pi / 6 * y ^ 2))).intervalIntegrable _ _
  calc
    _ ≤ ∫ y : ℝ in (-eta / 2)..(eta / 2),
        (Real.exp (3 / 4 * |sigma - 1|) / eta * firstOrderGaussianConstant sigma) *
          Real.exp (-Real.pi / 6 * y ^ 2) :=
      intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Filter.Eventually.of_forall (fun y hy => hb y ⟨hy.1.le, hy.2⟩)) hi
    _ = (Real.exp (3 / 4 * |sigma - 1|) / eta * firstOrderGaussianConstant sigma) *
        (∫ y : ℝ in (-eta / 2)..(eta / 2), Real.exp (-Real.pi / 6 * y ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (Real.exp (3 / 4 * |sigma - 1|) / eta * firstOrderGaussianConstant sigma) *
        Real.sqrt (Real.pi / (Real.pi / 6)) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [neg_div] using gaussian_interval_le_full
          (by positivity : 0 < Real.pi / 6) (by linarith : -eta / 2 ≤ eta / 2)) hC
    _ = _ := by
      rw [show Real.pi / (Real.pi / 6) = 6 by field_simp]
      unfold firstOrderJnConstant
      ring

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
