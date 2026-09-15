import LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.HankelPrefactor

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem left_exp_scalar {eta : ℝ} (he : 10 ≤ eta) :
    3 * Real.exp (-Real.pi * eta ^ 2 / 4) ≤ 1 / (10 * eta ^ 4) := by
  have he0 : 0 < eta := by linarith
  have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) he 4
  have h8 : (10 : ℝ) ^ 4 * eta ^ 4 ≤ eta ^ 8 := by
    simpa only [← pow_add] using mul_le_mul_of_nonneg_right h4 (pow_nonneg he0.le 4)
  have hexp : 30 * eta ^ 4 ≤ Real.exp (Real.pi * eta ^ 2 / 4) := by
    calc
      _ ≤ ((3 / 4 : ℝ) ^ 4 / 24 * 10 ^ 4) * eta ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg he0.le 4)
      _ ≤ ((3 / 4 : ℝ) ^ 4 / 24) * eta ^ 8 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = (3 * eta ^ 2 / 4) ^ 4 / ((4 : ℕ).factorial : ℝ) := by norm_num; ring
      _ ≤ (Real.pi * eta ^ 2 / 4) ^ 4 / ((4 : ℕ).factorial : ℝ) := by
        gcongr
        exact Real.pi_gt_three.le
      _ ≤ _ := Real.pow_div_factorial_le_exp _ (by positivity) 4
  calc
    _ = 3 / Real.exp (Real.pi * eta ^ 2 / 4) := by
      rw [show -Real.pi * eta ^ 2 / 4 = -(Real.pi * eta ^ 2 / 4) by ring,
        Real.exp_neg]
      ring
    _ ≤ 3 / (30 * eta ^ 4) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hexp
    _ = _ := by ring

theorem left_hankel_exponential {s : ℂ} {eta : ℝ} {m : ℕ}
    (he : 10 ≤ eta) (hmL : eta - 1 ≤ m) (hmU : (m : ℝ) ≤ eta)
    (hs : s.re = 1 / 2) (ht : s.im = 2 * Real.pi * eta ^ 2) :
    ‖rsHankelPrefactor s * ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta m r‖ ≤
      3 * Real.exp (-Real.pi * eta ^ 2 / 4) := by
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta m r‖ :=
      mul_le_mul_of_nonneg_right (critical_hankel_prefactor_norm_le_one hs) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact left_integral_budget he hmL hmU (by linarith) ht

theorem left_hankel_floor_budget {s : ℂ} {eta : ℝ}
    (he : 10 ≤ eta) (hs : s.re = 1 / 2) (ht : s.im = 2 * Real.pi * eta ^ 2) :
    ‖rsHankelPrefactor s * ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta ⌊eta⌋₊ r‖ ≤
      1 / (10 * eta ^ 4) := by
  have hL : eta - 1 ≤ (⌊eta⌋₊ : ℝ) := by
    linarith [Nat.self_sub_floor_lt_one eta]
  have hU : (⌊eta⌋₊ : ℝ) ≤ eta := by
    linarith [Nat.zero_le_self_sub_floor (by linarith : 0 ≤ eta)]
  exact (left_hankel_exponential he hL hU hs ht).trans (left_exp_scalar he)

theorem left_scalar_original_scale {eta a : ℝ} (he : 1 ≤ eta) (ha : -2 ≤ a) :
    1 / (10 * eta ^ 4) ≤ 1 / 10 * (eta ^ 2) ^ a := by
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show 1 ≤ eta ^ 2 by nlinarith) ha
  have hid : (eta ^ 2) ^ (-2 : ℝ) = (eta ^ 4)⁻¹ := by
    rw [Real.rpow_neg (sq_nonneg _), Real.rpow_two]
    congr 1
    ring
  rw [hid] at hpow
  simpa only [div_eq_mul_inv, one_mul, mul_inv_rev, mul_comm] using
    mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 1 / 10)

theorem left_hankel_R0 {s : ℂ} {eta : ℝ} (he : 0 ≤ eta) (hR : 125 < eta ^ 2)
    (hs : s.re = 1 / 2) (ht : s.im = 2 * Real.pi * eta ^ 2) :
    ‖rsHankelPrefactor s * ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta ⌊eta⌋₊ r‖ ≤
      1 / 10 * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have h10 : 10 ≤ eta := (sq_le_sq₀ (by norm_num) he).mp (by nlinarith)
  exact (left_hankel_floor_budget h10 hs ht).trans
    (left_scalar_original_scale (by linarith) (by norm_num))

theorem left_hankel_R2 {s : ℂ} {eta : ℝ} (he : 0 ≤ eta) (hR : 2000 < eta ^ 2)
    (hs : s.re = 1 / 2) (ht : s.im = 2 * Real.pi * eta ^ 2) :
    ‖rsHankelPrefactor s * ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta ⌊eta⌋₊ r‖ ≤
      1 / 10 * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have h10 : 10 ≤ eta := (sq_le_sq₀ (by norm_num) he).mp (by nlinarith)
  exact (left_hankel_floor_budget h10 hs ht).trans
    (left_scalar_original_scale (by linarith) (by norm_num))

end LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
