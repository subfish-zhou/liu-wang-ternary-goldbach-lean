import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorPolynomialBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem exterior_exp_large {eta : ℝ} (he : 10 ≤ eta) :
    1200000 * eta ^ 3 ≤ Real.exp (Real.pi * eta ^ 2 / 8) := by
  have he0 : 0 ≤ eta := by linarith
  have h17 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) he 17
  have hm := mul_le_mul_of_nonneg_right h17 (pow_nonneg he0 3)
  have h20 : (10 : ℝ) ^ 17 * eta ^ 3 ≤ eta ^ 20 := by
    simpa only [← pow_add] using hm
  calc
    _ ≤ ((3 / 8 : ℝ) ^ 10 / 3628800 * 10 ^ 17) * eta ^ 3 := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg he0 3)
    _ ≤ ((3 / 8 : ℝ) ^ 10 / 3628800) * eta ^ 20 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h20 (by positivity)
    _ = ((3 * eta ^ 2 / 8) ^ 10) / ((10 : ℕ).factorial : ℝ) := by norm_num; ring
    _ ≤ ((Real.pi * eta ^ 2 / 8) ^ 10) / ((10 : ℕ).factorial : ℝ) := by
      gcongr
      exact Real.pi_gt_three.le
    _ ≤ _ := Real.pow_div_factorial_le_exp _ (by positivity) 10

theorem exterior_large_scalar {eta : ℝ} (he : 10 ≤ eta) :
    120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) ≤ 1 / (10 * eta ^ 4) := by
  have he0 : 0 < eta := by linarith
  calc
    _ = 120000 / (eta * Real.exp (Real.pi * eta ^ 2 / 8)) := by
      rw [show -Real.pi * eta ^ 2 / 8 = -(Real.pi * eta ^ 2 / 8) by ring, Real.exp_neg]
      ring
    _ ≤ 120000 / (eta * (1200000 * eta ^ 3)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (exterior_exp_large he) he0.le
    _ = _ := by field_simp; ring

theorem exterior_seven_large {eta : ℝ} (he : 10 ≤ eta)
    {m : ℕ} (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand (1 / 2) eta m 7 y‖) ≤
      1 / (10 * eta ^ 4) :=
  (exterior_seven_norm_budget (by linarith) h0 h1).trans (exterior_large_scalar he)

theorem exterior_one_le_seven_scalar {eta : ℝ} (he : 0 < eta) :
    4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4) ≤
      120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) := by
  apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity)
  · rw [div_le_div_iff₀ (mul_pos Real.pi_pos he) he]
    nlinarith [Real.pi_gt_three]
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg eta)]

theorem exterior_one_large (sigma : ℝ) {eta : ℝ} (he : 10 ≤ eta)
    {m : ℕ} (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand sigma eta m 1 y‖) ≤
      1 / (10 * eta ^ 4) :=
  (exterior_one_norm_budget sigma (by linarith) h0 h1).trans
    ((exterior_one_le_seven_scalar (by linarith)).trans (exterior_large_scalar he))

theorem exterior_eta_original_height {t : ℝ} (ht : 16 < t) :
    1 ≤ Real.sqrt (t / (2 * Real.pi)) := by
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ t / (2 * Real.pi))
  have hl : 1 ≤ t / (2 * Real.pi) := (le_div_iff₀ (by positivity)).mpr (by linarith [Real.pi_lt_four])
  exact (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)).mp (by nlinarith)

theorem exterior_floor_one (sigma : ℝ) {eta : ℝ} (he : 1 ≤ eta) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ 1 y‖) ≤
      4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4) :=
  exterior_one_norm_budget sigma he (Nat.zero_le_self_sub_floor (by linarith))
    (Nat.self_sub_floor_lt_one eta).le

theorem exterior_floor_seven {eta : ℝ} (he : 1 ≤ eta) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y‖) ≤
      120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) :=
  exterior_seven_norm_budget he (Nat.zero_le_self_sub_floor (by linarith))
    (Nat.self_sub_floor_lt_one eta).le

theorem exterior_R0_height (sigma : ℝ) {eta : ℝ} (he : 0 ≤ eta) (ht : 125 < eta ^ 2) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ 1 y‖) ≤
      1 / (10 * eta ^ 4) := by
  have h10 : 10 ≤ eta := (sq_le_sq₀ (by norm_num) he).mp (by nlinarith)
  exact exterior_one_large sigma h10 (Nat.zero_le_self_sub_floor he) (Nat.self_sub_floor_lt_one eta).le

theorem exterior_R2_height {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y‖) ≤
      1 / (10 * eta ^ 4) := by
  have h10 : 10 ≤ eta := (sq_le_sq₀ (by norm_num) he).mp (by nlinarith)
  exact exterior_seven_large h10 (Nat.zero_le_self_sub_floor he) (Nat.self_sub_floor_lt_one eta).le

end LiuWang.Proof.Campaign20260915.ZetaMordell
