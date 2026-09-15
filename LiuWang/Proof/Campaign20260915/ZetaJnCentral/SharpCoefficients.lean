import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SeventhCoefficients
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.RationalMoments

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem norm_div_eta_pow {eta : ℝ} (he : 44 ≤ eta) (z : ℂ) (k : ℕ) :
    ‖z / (eta : ℂ) ^ k‖ ≤ ‖z‖ / (44 : ℝ) ^ k := by
  rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < eta)]
  exact div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)
    (pow_le_pow_left₀ (by norm_num) he k)

theorem sharp_scaled_four {eta : ℝ} (he : 44 ≤ eta) :
    ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 4‖ ≤ 21 / 8 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 2 * scaledCoefficient eta 4 =
      -(5 * Real.pi * I) / 6 + (35 / 128 : ℂ) / (eta : ℂ) ^ 2 := by
    rw [scaledCoefficient, sourceSaddle_scaled_four he0]
    field_simp
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add le_rfl (norm_div_eta_pow he _ 2)).trans
  norm_num [norm_div, norm_mul, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_d4]

theorem sharp_scaled_five {eta : ℝ} (he : 44 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 5‖ ≤ 17 / 6 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 3 * scaledCoefficient eta 5 =
      9 * Real.pi * I / 10 - (63 / 256 : ℂ) / (eta : ℂ) ^ 2 := by
    rw [scaledCoefficient, sourceSaddle_scaled_five he0]
    field_simp
  rw [hid]
  apply (norm_sub_le _ _).trans
  apply (add_le_add le_rfl (norm_div_eta_pow he _ 2)).trans
  norm_num [norm_div, norm_mul, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_d4]

theorem sharp_scaled_six {eta : ℝ} (he : 44 ≤ eta) :
    ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 6‖ ≤ 11 / 5 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 2 * scaledCoefficient eta 6 =
      -(2 * Real.pi ^ 2) / 9 - (223 * Real.pi * I / 240) / (eta : ℂ) ^ 2 +
        (231 / 1024 : ℂ) / (eta : ℂ) ^ 4 := by
    rw [scaledCoefficient, sourceSaddle_scaled_six he0]
    field_simp
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add le_rfl (norm_div_eta_pow he _ 2))
    (norm_div_eta_pow he _ 4)).trans
  norm_num [norm_div, norm_mul, norm_pow, abs_of_pos Real.pi_pos]
  have hsq := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 2
  norm_num at hsq
  nlinarith [Real.pi_lt_d4]

theorem scaled_recurrence_weighted {eta : ℝ} (he : 0 < eta) (n k : ℕ) :
    ((n : ℝ) + 3) * ‖(eta : ℂ) ^ (k + 1) * scaledCoefficient eta (n + 3)‖ ≤
      ((n : ℝ) + 5 / 2) * ‖(eta : ℂ) ^ k * scaledCoefficient eta (n + 2)‖ +
        (2 * Real.pi) * ‖(eta : ℂ) ^ k * scaledCoefficient eta n‖ := by
  have hr := sourceSaddle_scaled_recurrence (1 / 2) he n
  change ((n + 3 : ℕ) : ℂ) * eta * scaledCoefficient eta (n + 3) =
    -(((n + 3 : ℕ) : ℂ) - (1 / 2 : ℝ)) * scaledCoefficient eta (n + 2) +
      (2 * Real.pi * I) * scaledCoefficient eta n at hr
  have hid : (((n : ℝ) + 3 : ℝ) : ℂ) *
      ((eta : ℂ) ^ (k + 1) * scaledCoefficient eta (n + 3)) =
      -(((n : ℝ) + 5 / 2 : ℝ) : ℂ) *
          ((eta : ℂ) ^ k * scaledCoefficient eta (n + 2)) +
        (2 * Real.pi * I) * ((eta : ℂ) ^ k * scaledCoefficient eta n) := by
    push_cast at hr ⊢
    rw [pow_succ]
    linear_combination (eta : ℂ) ^ k * hr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnorm := norm_add_le
    (-(((n : ℝ) + 5 / 2 : ℝ) : ℂ) * ((eta : ℂ) ^ k * scaledCoefficient eta (n + 2)))
    ((2 * Real.pi * I) * ((eta : ℂ) ^ k * scaledCoefficient eta n))
  rw [← hid] at hnorm
  simpa only [norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) + 3),
    abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) + 5 / 2),
    norm_ofNat, norm_I, abs_of_pos Real.pi_pos, mul_one] using hnorm

theorem sharp_scaled_seven {eta : ℝ} (he : 44 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 7‖ ≤ 22 / 5 := by
  have h := scaled_recurrence_weighted (by linarith : 0 < eta) 4 2
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h4 := mul_le_mul_of_nonneg_left (sharp_scaled_four he) (by positivity : 0 ≤ 2 * Real.pi)
  have h6 := sharp_scaled_six he
  nlinarith [Real.pi_lt_d4]

theorem sharp_scaled_eight {eta : ℝ} (he : 44 ≤ eta) :
    ‖(eta : ℂ) ^ 4 * scaledCoefficient eta 8‖ ≤ 32 / 5 := by
  have h := scaled_recurrence_weighted (by linarith : 0 < eta) 5 3
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h5 := mul_le_mul_of_nonneg_left (sharp_scaled_five he) (by positivity : 0 ≤ 2 * Real.pi)
  have h7 := sharp_scaled_seven he
  nlinarith [Real.pi_lt_d4]

theorem sharp_scaled_nine {eta : ℝ} (he : 44 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 9‖ ≤ 31 / 20 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have h8 : ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 8‖ ≤ (32 / 5) / (44 : ℝ) ^ 2 := by
    have hid : (eta : ℂ) ^ 2 * scaledCoefficient eta 8 =
        ((eta : ℂ) ^ 4 * scaledCoefficient eta 8) / (eta : ℂ) ^ 2 := by field_simp
    rw [hid]
    exact (norm_div_eta_pow he _ 2).trans
      (div_le_div_of_nonneg_right (sharp_scaled_eight he) (by positivity))
  have h := scaled_recurrence_weighted he0 6 2
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h6 := mul_le_mul_of_nonneg_left (sharp_scaled_six he) (by positivity : 0 ≤ 2 * Real.pi)
  nlinarith [Real.pi_lt_d4]

theorem sharp_scaled_ten {eta : ℝ} (he : 44 ≤ eta) :
    ‖(eta : ℂ) ^ 4 * scaledCoefficient eta 10‖ ≤ 17 / 4 := by
  have h := scaled_recurrence_weighted (by linarith : 0 < eta) 7 3
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h7 := mul_le_mul_of_nonneg_left (sharp_scaled_seven he) (by positivity : 0 ≤ 2 * Real.pi)
  have h9 := sharp_scaled_nine he
  nlinarith [Real.pi_lt_d4]

theorem sharp_scaled_eleven {eta : ℝ} (he : 44 ≤ eta) :
    ‖(eta : ℂ) ^ 5 * scaledCoefficient eta 11‖ ≤ 31 / 4 := by
  have h := scaled_recurrence_weighted (by linarith : 0 < eta) 8 4
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h8 := mul_le_mul_of_nonneg_left (sharp_scaled_eight he) (by positivity : 0 ≤ 2 * Real.pi)
  have h10 := sharp_scaled_ten he
  nlinarith [Real.pi_lt_d4]

theorem scaled_weighted_to_norm {eta C : ℝ} (he : 0 < eta) (n k : ℕ)
    (h : ‖(eta : ℂ) ^ k * scaledCoefficient eta n‖ ≤ C) :
    ‖scaledCoefficient eta n‖ ≤ C / eta ^ k := by
  rw [le_div_iff₀ (pow_pos he k)]
  simpa only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos he, mul_comm] using h

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
