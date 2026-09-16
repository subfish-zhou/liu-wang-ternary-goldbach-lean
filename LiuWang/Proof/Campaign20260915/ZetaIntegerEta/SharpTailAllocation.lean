import LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.OriginalScale
import LiuWang.Proof.Campaign20260915.ZetaC2RightTail.SourceError

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
open LiuWang.Proof.Campaign20260915.ZetaC2RightTail

theorem left_tail_thousandth_scalar {eta : ℝ} (he : 10 ≤ eta) :
    3 * Real.exp (-Real.pi * eta ^ 2 / 4) ≤ 1 / (1000 * eta ^ 4) := by
  have he0 : 0 < eta := by linarith
  have h8 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) he 8
  have h12 : (10 : ℝ) ^ 8 * eta ^ 4 ≤ eta ^ 12 := by
    simpa only [← pow_add] using mul_le_mul_of_nonneg_right h8 (pow_nonneg he0.le 4)
  have hx : 3000 * eta ^ 4 ≤ Real.exp (Real.pi * eta ^ 2 / 4) := by
    calc
      _ ≤ ((3 / 4 : ℝ) ^ 6 / 720 * 10 ^ 8) * eta ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg he0.le 4)
      _ ≤ ((3 / 4 : ℝ) ^ 6 / 720) * eta ^ 12 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h12 (by positivity)
      _ = (3 * eta ^ 2 / 4) ^ 6 / ((6 : ℕ).factorial : ℝ) := by norm_num; ring
      _ ≤ (Real.pi * eta ^ 2 / 4) ^ 6 / ((6 : ℕ).factorial : ℝ) := by
        gcongr
        exact Real.pi_gt_three.le
      _ ≤ _ := Real.pow_div_factorial_le_exp _ (by positivity) 6
  calc
    _ = 3 / Real.exp (Real.pi * eta ^ 2 / 4) := by
      rw [show -Real.pi * eta ^ 2 / 4 = -(Real.pi * eta ^ 2 / 4) by ring, Real.exp_neg]
      ring
    _ ≤ 3 / (3000 * eta ^ 4) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hx
    _ = _ := by ring

theorem right_tail_thousandth_scalar {eta : ℝ} (he : 10 ≤ eta) :
    Real.exp (-((rsSaddleScale * eta) ^ 2) / 11) ≤ 1 / (2000 * eta ^ 2) := by
  have he0 : 0 < eta := by linarith
  have h6 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) he 6
  have h8 : (10 : ℝ) ^ 6 * eta ^ 2 ≤ eta ^ 8 := by
    simpa only [← pow_add] using mul_le_mul_of_nonneg_right h6 (sq_nonneg eta)
  have harg : eta ^ 2 / 2 ≤ (rsSaddleScale * eta) ^ 2 / 11 := by
    rw [mul_pow, rsSaddleScale_sq]
    nlinarith [mul_nonneg (show 0 ≤ Real.pi - 3 by linarith [Real.pi_gt_three]) (sq_nonneg eta)]
  have hx : 2000 * eta ^ 2 ≤ Real.exp ((rsSaddleScale * eta) ^ 2 / 11) := by
    calc
      _ ≤ ((1 / 384 : ℝ) * 10 ^ 6) * eta ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg eta)
      _ ≤ (1 / 384 : ℝ) * eta ^ 8 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = (eta ^ 2 / 2) ^ 4 / ((4 : ℕ).factorial : ℝ) := by norm_num; ring
      _ ≤ ((rsSaddleScale * eta) ^ 2 / 11) ^ 4 / ((4 : ℕ).factorial : ℝ) := by gcongr
      _ ≤ _ := Real.pow_div_factorial_le_exp _ (by positivity) 4
  rw [neg_div, Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) hx

theorem source_error_scale {eta : ℝ} (he : 0 < eta) (k : ℕ) :
    eta ^ (-(1 / 2 : ℝ)) / eta ^ k = eta ^ (-(1 / 2 : ℝ) - k) := by
  rw [Real.rpow_sub he, Real.rpow_natCast]

theorem source_error_scale_original {eta : ℝ} (he : 0 < eta) (k : ℕ) :
    eta ^ (-(1 / 2 : ℝ)) / eta ^ k =
      (eta ^ 2) ^ ((-(1 / 2 : ℝ) - k) / 2) := by
  rw [source_error_scale he, ← Real.rpow_natCast eta 2, ← Real.rpow_mul he.le]
  congr 1
  push_cast
  ring

theorem left_tail_source_allocation {eta : ℝ} {s : ℂ} (he : 10 ≤ eta)
    (hs : s.re = 1 / 2) (ht : s.im = 2 * Real.pi * eta ^ 2) :
    ‖rsHankelPrefactor s *
      ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta ⌊eta⌋₊ r‖ ≤
      (1 / 1000) * (eta ^ (-(1 / 2 : ℝ)) / eta ^ 3) := by
  have he0 : 0 < eta := by linarith
  have h := (left_hankel_exponential he
    (by linarith [Nat.lt_floor_add_one eta] : eta - 1 ≤ (⌊eta⌋₊ : ℝ))
    (Nat.floor_le he0.le) hs ht).trans (left_tail_thousandth_scalar he)
  have hp := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ eta by linarith)
    (show (-4 : ℝ) ≤ -(1 / 2 : ℝ) - (3 : ℕ) by norm_num)
  rw [Real.rpow_neg he0.le, Real.rpow_ofNat, ← source_error_scale he0 3] at hp
  apply h.trans
  simpa only [one_div, mul_inv_rev, mul_comm] using
    mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1 / 1000)

theorem right_tail_source_allocation {eta : ℝ} (he : 10 ≤ eta) :
    ‖rsHankelPrefactor ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) *
      (∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand
        ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta ⌊eta⌋₊ y)‖ ≤
      (1 / 1000) * (eta ^ (-(1 / 2 : ℝ)) / eta ^ 3) := by
  have he0 : 0 < eta := by linarith
  have hc : 11 / (2 * Real.pi) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  apply (critical_prefactored_right_tail_effective (by linarith : 1 ≤ eta)
    (Nat.lt_floor_add_one eta).le).trans
  calc
    _ ≤ (2 * eta ^ (-(3 / 2 : ℝ))) * (1 / (2000 * eta ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg he0.le _))
        (right_tail_thousandth_scalar he) (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [show -(3 / 2 : ℝ) = -(1 / 2 : ℝ) - 1 by norm_num,
        Real.rpow_sub he0, Real.rpow_one]
      field_simp
      ring

theorem source_error_scale_three_le_one {eta : ℝ} (he : 1 ≤ eta) :
    eta ^ (-(1 / 2 : ℝ)) / eta ^ 3 ≤ eta ^ (-(1 / 2 : ℝ)) / eta := by
  have he0 : 0 < eta := by linarith
  rw [source_error_scale he0 3]
  have h1 := source_error_scale he0 1
  simp only [pow_one] at h1
  rw [h1]
  exact Real.rpow_le_rpow_of_exponent_le he (by norm_num)

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
