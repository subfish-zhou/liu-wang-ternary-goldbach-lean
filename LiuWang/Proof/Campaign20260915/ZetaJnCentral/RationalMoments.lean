import LiuWang.Proof.Campaign20260915.ZetaJnCentral.ExactGaussian
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

def rationalGaussianMoment : ℕ → ℝ
  | 0 => 1
  | 1 => 50 / 157
  | n + 2 => ((n : ℝ) + 1) * (25 / 157) * rationalGaussianMoment n

theorem rationalGaussianMoment_nonneg : ∀ n, 0 ≤ rationalGaussianMoment n
  | 0 => by norm_num [rationalGaussianMoment]
  | 1 => by norm_num [rationalGaussianMoment]
  | n + 2 => by
    rw [rationalGaussianMoment]
    exact mul_nonneg (by positivity) (rationalGaussianMoment_nonneg n)

theorem gaussianAbsoluteMoment_rational :
    ∀ n, gaussianAbsoluteMoment Real.pi n ≤ rationalGaussianMoment n
  | 0 => by
    rw [gaussianAbsoluteMoment_zero Real.pi_pos, div_self Real.pi_pos.ne', Real.sqrt_one]
    rfl
  | 1 => by
    rw [gaussianAbsoluteMoment_one, rationalGaussianMoment, div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_d2]
  | n + 2 => by
    rw [gaussianAbsoluteMoment_step Real.pi_pos, rationalGaussianMoment]
    apply mul_le_mul ?_ (gaussianAbsoluteMoment_rational n)
      (gaussianAbsoluteMoment_nonneg Real.pi_pos n) (by positivity)
    have hp : 1 / (2 * Real.pi) ≤ 25 / 157 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi)]
      linarith [Real.pi_gt_d2]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ n + 1)

theorem inverse_descent_constant_rational :
    1 / (Real.sqrt 2 * Real.pi) ≤ 250 / 1099 := by
  have hs : 7 / 5 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hp : 157 / 50 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hm := mul_le_mul hs hp (by norm_num : (0 : ℝ) ≤ 157 / 50) (Real.sqrt_nonneg 2)
  rw [div_le_iff₀ (by positivity : 0 < Real.sqrt 2 * Real.pi)]
  linarith

theorem exactGaussianBudget_rational (n : ℕ) :
    exactGaussianBudget Real.pi n ≤
      rationalGaussianMoment (n + 1) + (250 / 1099) * rationalGaussianMoment n := by
  unfold exactGaussianBudget
  apply add_le_add (gaussianAbsoluteMoment_rational (n + 1))
  rw [div_eq_mul_one_div, mul_comm]
  exact mul_le_mul inverse_descent_constant_rational (gaussianAbsoluteMoment_rational n)
    (gaussianAbsoluteMoment_nonneg Real.pi_pos n) (by norm_num)

theorem exactGaussianBudget_eleven :
    exactGaussianBudget Real.pi 11 ≤ 1 / 5 := by
  apply (exactGaussianBudget_rational 11).trans
  norm_num [rationalGaussianMoment]

theorem exactGaussian_seven_corrections :
    22 / 5 * exactGaussianBudget Real.pi 6 +
      (32 / 5 / 44) * exactGaussianBudget Real.pi 7 +
      31 / 20 * exactGaussianBudget Real.pi 8 +
      (17 / 4 / 44) * exactGaussianBudget Real.pi 9 +
      (31 / 4 / 44 ^ 2) * exactGaussianBudget Real.pi 10 ≤ 51 / 100 := by
  have h6 := mul_le_mul_of_nonneg_left (exactGaussianBudget_rational 6) (by norm_num : (0 : ℝ) ≤ 22 / 5)
  have h7 := mul_le_mul_of_nonneg_left (exactGaussianBudget_rational 7)
    (by norm_num : (0 : ℝ) ≤ 32 / 5 / 44)
  have h8 := mul_le_mul_of_nonneg_left (exactGaussianBudget_rational 8) (by norm_num : (0 : ℝ) ≤ 31 / 20)
  have h9 := mul_le_mul_of_nonneg_left (exactGaussianBudget_rational 9)
    (by norm_num : (0 : ℝ) ≤ 17 / 4 / 44)
  have h10 := mul_le_mul_of_nonneg_left (exactGaussianBudget_rational 10)
    (by norm_num : (0 : ℝ) ≤ 31 / 4 / 44 ^ 2)
  apply (add_le_add (add_le_add (add_le_add (add_le_add h6 h7) h8) h9) h10).trans
  norm_num [rationalGaussianMoment]

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
