import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorPolynomialBudget

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def scaledCoefficient (eta : ℝ) (n : ℕ) : ℂ :=
  rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n

theorem scaled_four_weighted {eta : ℝ} (he : 1 ≤ eta) :
    ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 4‖ ≤ 16 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 2 * scaledCoefficient eta 4 =
      -(5 * Real.pi * I) / 6 + (35 / 128 : ℂ) / (eta : ℂ) ^ 2 := by
    rw [scaledCoefficient, sourceSaddle_scaled_four he0]
    field_simp
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add le_rfl (exterior_div_pow_norm _ he 2)).trans
  norm_num [norm_div, norm_mul, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_four]

theorem scaled_five_weighted {eta : ℝ} (he : 1 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 5‖ ≤ 16 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 3 * scaledCoefficient eta 5 =
      9 * Real.pi * I / 10 - (63 / 256 : ℂ) / (eta : ℂ) ^ 2 := by
    rw [scaledCoefficient, sourceSaddle_scaled_five he0]
    field_simp
  rw [hid]
  apply (norm_sub_le _ _).trans
  apply (add_le_add le_rfl (exterior_div_pow_norm _ he 2)).trans
  norm_num [norm_div, norm_mul, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_four]

theorem scaled_six_weighted {eta : ℝ} (he : 1 ≤ eta) :
    ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 6‖ ≤ 16 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 2 * scaledCoefficient eta 6 =
      -(2 * Real.pi ^ 2) / 9 -
        (223 * Real.pi * I / 240) / (eta : ℂ) ^ 2 +
        (231 / 1024 : ℂ) / (eta : ℂ) ^ 4 := by
    rw [scaledCoefficient, sourceSaddle_scaled_six he0]
    field_simp
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add le_rfl (exterior_div_pow_norm _ he 2))
    (exterior_div_pow_norm _ he 4)).trans
  norm_num [norm_div, norm_mul, norm_pow, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_lt_four, Real.pi_pos, sq_nonneg (Real.pi - 4)]

theorem scaled_seven_weighted {eta : ℝ} (he : 1 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 7‖ ≤ 34 := by
  have hr := sourceSaddle_scaled_recurrence (1 / 2) (by linarith : 0 < eta) 4
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, ofReal_div, ofReal_one, ofReal_ofNat] at hr
  change 7 * (eta : ℂ) * scaledCoefficient eta 7 =
    -(13 / 2) * scaledCoefficient eta 6 + (2 * Real.pi * I) * scaledCoefficient eta 4 at hr
  have hid : 7 * ((eta : ℂ) ^ 3 * scaledCoefficient eta 7) =
      (-13 / 2 : ℂ) * ((eta : ℂ) ^ 2 * scaledCoefficient eta 6) +
        (2 * Real.pi * I) * ((eta : ℂ) ^ 2 * scaledCoefficient eta 4) := by
    linear_combination (eta : ℂ) ^ 2 * hr
  have hnorm := norm_add_le
    ((-13 / 2 : ℂ) * ((eta : ℂ) ^ 2 * scaledCoefficient eta 6))
    ((2 * Real.pi * I) * ((eta : ℂ) ^ 2 * scaledCoefficient eta 4))
  rw [← hid] at hnorm
  norm_num [norm_mul, norm_div, norm_pow, abs_of_pos (show 0 < eta by linarith),
    abs_of_pos Real.pi_pos] at hnorm
  have h6 := scaled_six_weighted he
  have h4 := scaled_four_weighted he
  norm_num only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < eta by linarith)] at h6 h4 ⊢
  have hp := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * Real.pi)
  nlinarith [Real.pi_lt_four]

theorem scaled_weight_drop {eta : ℝ} (he : 1 ≤ eta) (z : ℂ) :
    ‖(eta : ℂ) ^ 2 * z‖ ≤ ‖(eta : ℂ) ^ 3 * z‖ := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 2 * z = ((eta : ℂ) ^ 3 * z) / (eta : ℂ) ^ 1 := by
    field_simp
  rw [hid]
  exact exterior_div_pow_norm _ he 1

theorem scaled_eight_weighted {eta : ℝ} (he : 1 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 8‖ ≤ 48 := by
  have hr := sourceSaddle_scaled_recurrence (1 / 2) (by linarith : 0 < eta) 5
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, ofReal_div, ofReal_one, ofReal_ofNat] at hr
  change 8 * (eta : ℂ) * scaledCoefficient eta 8 =
    -(15 / 2) * scaledCoefficient eta 7 + (2 * Real.pi * I) * scaledCoefficient eta 5 at hr
  have hid : 8 * ((eta : ℂ) ^ 3 * scaledCoefficient eta 8) =
      (-15 / 2 : ℂ) * ((eta : ℂ) ^ 2 * scaledCoefficient eta 7) +
        (2 * Real.pi * I) * ((eta : ℂ) ^ 2 * scaledCoefficient eta 5) := by
    linear_combination (eta : ℂ) ^ 2 * hr
  have hnorm := norm_add_le
    ((-15 / 2 : ℂ) * ((eta : ℂ) ^ 2 * scaledCoefficient eta 7))
    ((2 * Real.pi * I) * ((eta : ℂ) ^ 2 * scaledCoefficient eta 5))
  rw [← hid] at hnorm
  norm_num [norm_mul, norm_div, norm_pow, abs_of_pos (show 0 < eta by linarith),
    abs_of_pos Real.pi_pos] at hnorm
  have h7 := (scaled_weight_drop he (scaledCoefficient eta 7)).trans (scaled_seven_weighted he)
  have h5 := (scaled_weight_drop he (scaledCoefficient eta 5)).trans (scaled_five_weighted he)
  norm_num only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < eta by linarith)] at h7 h5 ⊢
  have hp := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 2 * Real.pi)
  nlinarith [Real.pi_lt_four]

theorem scaled_seven_bound {eta : ℝ} (he : 1 ≤ eta) :
    ‖scaledCoefficient eta 7‖ ≤ 34 / eta ^ 3 := by
  rw [le_div_iff₀ (by positivity : 0 < eta ^ 3)]
  have h := scaled_seven_weighted he
  simpa [norm_mul, norm_pow, abs_of_pos (show 0 < eta by linarith), mul_comm] using h

theorem scaled_eight_bound {eta : ℝ} (he : 1 ≤ eta) :
    ‖scaledCoefficient eta 8‖ ≤ 48 / eta ^ 3 := by
  rw [le_div_iff₀ (by positivity : 0 < eta ^ 3)]
  have h := scaled_eight_weighted he
  simpa [norm_mul, norm_pow, abs_of_pos (show 0 < eta by linarith), mul_comm] using h

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
