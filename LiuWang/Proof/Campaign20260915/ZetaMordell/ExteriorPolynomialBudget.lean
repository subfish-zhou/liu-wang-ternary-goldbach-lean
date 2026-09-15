import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorGaussianTail

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem exterior_div_pow_norm (a : ℂ) {eta : ℝ} (he : 1 ≤ eta) (n : ℕ) :
    ‖a / (eta : ℂ) ^ n‖ ≤ ‖a‖ := by
  rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact div_le_self (norm_nonneg a) (one_le_pow₀ he)

theorem exterior_coefficient_bound {eta : ℝ} (he : 1 ≤ eta) {n : ℕ} (hn : n < 7) :
    ‖rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ ≤ 16 := by
  have he0 : 0 < eta := by linarith
  have hp := Real.pi_lt_four
  have hp0 := Real.pi_pos
  interval_cases n
  · rw [sourceSaddle_scaled_zero, norm_one]
    norm_num
  · rw [sourceSaddle_scaled_one he0,
      show -1 / (2 * (eta : ℂ)) = (-1 / 2 : ℂ) / (eta : ℂ) ^ 1 by ring]
    exact (exterior_div_pow_norm _ he 1).trans (by norm_num)
  · rw [sourceSaddle_scaled_two he0,
      show 3 / (8 * (eta : ℂ) ^ 2) = (3 / 8 : ℂ) / (eta : ℂ) ^ 2 by ring]
    exact (exterior_div_pow_norm _ he 2).trans (by norm_num)
  · rw [sourceSaddle_scaled_three he0,
      show 2 * Real.pi * I / (3 * (eta : ℂ)) = (2 * Real.pi * I / 3) / (eta : ℂ) ^ 1 by ring,
      show 5 / (16 * (eta : ℂ) ^ 3) = (5 / 16 : ℂ) / (eta : ℂ) ^ 3 by ring]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (exterior_div_pow_norm _ he 1) (exterior_div_pow_norm _ he 3)).trans
    norm_num [norm_div, norm_mul, abs_of_pos hp0]
    linarith
  · rw [sourceSaddle_scaled_four he0,
      show -(5 * Real.pi * I) / (6 * (eta : ℂ) ^ 2) = (-(5 * Real.pi * I) / 6) / (eta : ℂ) ^ 2 by ring,
      show 35 / (128 * (eta : ℂ) ^ 4) = (35 / 128 : ℂ) / (eta : ℂ) ^ 4 by ring]
    apply (norm_add_le _ _).trans
    apply (add_le_add (exterior_div_pow_norm _ he 2) (exterior_div_pow_norm _ he 4)).trans
    norm_num [norm_div, norm_mul, abs_of_pos hp0]
    linarith
  · rw [sourceSaddle_scaled_five he0,
      show 9 * Real.pi * I / (10 * (eta : ℂ) ^ 3) = (9 * Real.pi * I / 10) / (eta : ℂ) ^ 3 by ring,
      show 63 / (256 * (eta : ℂ) ^ 5) = (63 / 256 : ℂ) / (eta : ℂ) ^ 5 by ring]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (exterior_div_pow_norm _ he 3) (exterior_div_pow_norm _ he 5)).trans
    norm_num [norm_div, norm_mul, abs_of_pos hp0]
    linarith
  · rw [sourceSaddle_scaled_six he0,
      show -(2 * Real.pi ^ 2) / (9 * (eta : ℂ) ^ 2) = (-(2 * Real.pi ^ 2) / 9) / (eta : ℂ) ^ 2 by ring,
      show 223 * Real.pi * I / (240 * (eta : ℂ) ^ 4) = (223 * Real.pi * I / 240) / (eta : ℂ) ^ 4 by ring,
      show 231 / (1024 * (eta : ℂ) ^ 6) = (231 / 1024 : ℂ) / (eta : ℂ) ^ 6 by ring]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    apply (add_le_add
      (add_le_add (exterior_div_pow_norm _ he 2) (exterior_div_pow_norm _ he 4))
      (exterior_div_pow_norm _ he 6)).trans
    norm_num [norm_div, norm_mul, norm_pow, abs_of_pos hp0]
    nlinarith [sq_nonneg (Real.pi - 4)]

theorem exterior_coefficient_sum {eta : ℝ} (he : 1 ≤ eta) :
    (∑ n ∈ Finset.range 7,
      ‖rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ *
        (n.factorial : ℝ)) ≤ 13984 := by
  calc
    _ ≤ ∑ n ∈ Finset.range 7, 16 * (n.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (exterior_coefficient_bound he (Finset.mem_range.mp hn))
        (by positivity)
    _ = _ := by norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exterior_one_norm_budget (sigma : ℝ) {eta : ℝ} (he : 1 ≤ eta)
    {m : ℕ} (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand sigma eta m 1 y‖) ≤
      4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4) := by
  have hb (y : ℝ) (hy : eta / 2 ≤ |y|) :
      ‖rsLocalPolynomialIntegrand sigma eta m 1 y‖ ≤ 2 * Real.exp (-Real.pi * y ^ 2) := by
    simpa only [rsLocalPolynomialIntegrand, Finset.sum_range_succ, Finset.sum_range_zero,
      rsSaddle_coefficient_zero, pow_zero, mul_one, zero_add, norm_mul,
      rsDescentDirection_norm, one_mul] using
      exterior_gaussian_bound_half eta m (by linarith : 1 / 2 ≤ |y|) h0 h1
  have h := exterior_norm_integral_bound (exterior_polynomial_measurable sigma eta m 1)
    (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos (by linarith : 0 < eta / 2) hb
  rw [show -Real.pi * (eta / 2) ^ 2 = -Real.pi * eta ^ 2 / 4 by ring] at h
  convert h using 1
  · rw [neg_div]
  · ring

theorem exterior_seven_norm_budget {eta : ℝ} (he : 1 ≤ eta)
    {m : ℕ} (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand (1 / 2) eta m 7 y‖) ≤
      120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) := by
  apply (exterior_polynomial_general_budget (1 / 2) he h0 h1 7).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have he0 : 0 < eta := by linarith
  apply (div_le_iff₀ (mul_pos Real.pi_pos he0)).mpr
  have hsum := exterior_coefficient_sum he
  have hcancel : (120000 / eta) * (Real.pi * eta) = 120000 * Real.pi := by
    field_simp
  rw [hcancel]
  linarith [Real.pi_gt_three]

theorem exterior_one_budget (sigma : ℝ) {eta : ℝ} (he : 1 ≤ eta)
    {m : ℕ} (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, rsLocalPolynomialIntegrand sigma eta m 1 y‖ ≤
      4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4) :=
  (norm_integral_le_integral_norm _).trans (exterior_one_norm_budget sigma he h0 h1)

theorem exterior_seven_budget {eta : ℝ} (he : 1 ≤ eta)
    {m : ℕ} (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y‖ ≤
      120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) :=
  (norm_integral_le_integral_norm _).trans (exterior_seven_norm_budget he h0 h1)

end LiuWang.Proof.Campaign20260915.ZetaMordell
