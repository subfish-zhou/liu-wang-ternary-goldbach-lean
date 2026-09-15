import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SharpCoefficients

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem norm_div_eta_pow_lower {eta a : ℝ} (ha : 0 < a) (he : a ≤ eta) (z : ℂ) (k : ℕ) :
    ‖z / (eta : ℂ) ^ k‖ ≤ ‖z‖ / a ^ k := by
  rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans_le he)]
  exact div_le_div_of_nonneg_left (norm_nonneg z) (pow_pos ha k) (pow_le_pow_left₀ ha.le he k)

theorem first_scaled_one {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) * scaledCoefficient eta 1‖ ≤ 1 / 2 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) * scaledCoefficient eta 1 = -1 / 2 := by
    rw [scaledCoefficient, sourceSaddle_scaled_one he0]
    field_simp
  rw [hid]
  norm_num

theorem first_scaled_two {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 2‖ ≤ 3 / 8 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 2 * scaledCoefficient eta 2 = 3 / 8 := by
    rw [scaledCoefficient, sourceSaddle_scaled_two he0]
    field_simp
  rw [hid]
  norm_num

theorem first_scaled_three {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) * scaledCoefficient eta 3‖ ≤ 21 / 10 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) * scaledCoefficient eta 3 =
      2 * Real.pi * I / 3 - (5 / 16 : ℂ) / (eta : ℂ) ^ 2 := by
    rw [scaledCoefficient, sourceSaddle_scaled_three he0]
    field_simp
  rw [hid]
  apply (norm_sub_le _ _).trans
  apply (add_le_add le_rfl (norm_div_eta_pow_lower (by norm_num : (0 : ℝ) < 11) he _ 2)).trans
  norm_num [norm_div, norm_mul, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_d4]

theorem first_scaled_four {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 4‖ ≤ 21 / 8 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 2 * scaledCoefficient eta 4 =
      -(5 * Real.pi * I) / 6 + (35 / 128 : ℂ) / (eta : ℂ) ^ 2 := by
    rw [scaledCoefficient, sourceSaddle_scaled_four he0]
    field_simp
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add le_rfl (norm_div_eta_pow_lower (by norm_num : (0 : ℝ) < 11) he _ 2)).trans
  norm_num [norm_div, norm_mul, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_d4]

theorem first_scaled_five {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 5‖ ≤ 17 / 6 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ 3 * scaledCoefficient eta 5 =
      9 * Real.pi * I / 10 - (63 / 256 : ℂ) / (eta : ℂ) ^ 2 := by
    rw [scaledCoefficient, sourceSaddle_scaled_five he0]
    field_simp
  rw [hid]
  apply (norm_sub_le _ _).trans
  apply (add_le_add le_rfl (norm_div_eta_pow_lower (by norm_num : (0 : ℝ) < 11) he _ 2)).trans
  norm_num [norm_div, norm_mul, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_d4]

theorem first_scaled_six {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 6‖ ≤ 20 / 9 := by
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
  apply (add_le_add (add_le_add le_rfl
    (norm_div_eta_pow_lower (by norm_num : (0 : ℝ) < 11) he _ 2))
    (norm_div_eta_pow_lower (by norm_num : (0 : ℝ) < 11) he _ 4)).trans
  norm_num [norm_div, norm_mul, norm_pow, abs_of_pos Real.pi_pos]
  have hsq := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 2
  norm_num at hsq
  nlinarith [Real.pi_lt_d4]

theorem first_scaled_seven {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 7‖ ≤ 89 / 20 := by
  have h := scaled_recurrence_weighted (by linarith : 0 < eta) 4 2
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h4 := mul_le_mul_of_nonneg_left (first_scaled_four he) (by positivity : 0 ≤ 2 * Real.pi)
  have h6 := first_scaled_six he
  nlinarith [Real.pi_lt_d4]

theorem first_scaled_eight {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 4 * scaledCoefficient eta 8‖ ≤ 32 / 5 := by
  have h := scaled_recurrence_weighted (by linarith : 0 < eta) 5 3
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h5 := mul_le_mul_of_nonneg_left (first_scaled_five he) (by positivity : 0 ≤ 2 * Real.pi)
  have h7 := first_scaled_seven he
  nlinarith [Real.pi_lt_d4]

theorem first_scaled_nine {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 3 * scaledCoefficient eta 9‖ ≤ 13 / 8 := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have h8 : ‖(eta : ℂ) ^ 2 * scaledCoefficient eta 8‖ ≤ (32 / 5) / (11 : ℝ) ^ 2 := by
    have hid : (eta : ℂ) ^ 2 * scaledCoefficient eta 8 =
        ((eta : ℂ) ^ 4 * scaledCoefficient eta 8) / (eta : ℂ) ^ 2 := by field_simp
    rw [hid]
    exact (norm_div_eta_pow_lower (by norm_num : (0 : ℝ) < 11) he _ 2).trans
      (div_le_div_of_nonneg_right (first_scaled_eight he) (by positivity))
  have h := scaled_recurrence_weighted he0 6 2
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h6 := mul_le_mul_of_nonneg_left (first_scaled_six he) (by positivity : 0 ≤ 2 * Real.pi)
  nlinarith [Real.pi_lt_d4]

theorem first_scaled_ten {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 4 * scaledCoefficient eta 10‖ ≤ 35 / 8 := by
  have h := scaled_recurrence_weighted (by linarith : 0 < eta) 7 3
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h7 := mul_le_mul_of_nonneg_left (first_scaled_seven he) (by positivity : 0 ≤ 2 * Real.pi)
  have h9 := first_scaled_nine he
  nlinarith [Real.pi_lt_d4]

theorem first_scaled_eleven {eta : ℝ} (he : 11 ≤ eta) :
    ‖(eta : ℂ) ^ 5 * scaledCoefficient eta 11‖ ≤ 63 / 8 := by
  have h := scaled_recurrence_weighted (by linarith : 0 < eta) 8 4
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have h8 := mul_le_mul_of_nonneg_left (first_scaled_eight he) (by positivity : 0 ≤ 2 * Real.pi)
  have h10 := first_scaled_ten he
  nlinarith [Real.pi_lt_d4]

def firstCoefficientEnvelope : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => (3 / 8) / 11
  | 2 => 21 / 10
  | 3 => (21 / 8) / 11
  | 4 => (17 / 6) / 11 ^ 2
  | 5 => (20 / 9) / 11
  | 6 => (89 / 20) / 11 ^ 2
  | 7 => (32 / 5) / 11 ^ 3
  | 8 => (13 / 8) / 11 ^ 2
  | 9 => (35 / 8) / 11 ^ 3
  | 10 => (63 / 8) / 11 ^ 4
  | _ => 0

theorem firstCoefficientEnvelope_nonneg (n : ℕ) : 0 ≤ firstCoefficientEnvelope n := by
  unfold firstCoefficientEnvelope
  split <;> norm_num

theorem first_weighted_drop {eta C : ℝ} (he : 11 ≤ eta) (n hi : ℕ)
    (h : ‖(eta : ℂ) ^ (hi + 1) * scaledCoefficient eta n‖ ≤ C) :
    ‖(eta : ℂ) * scaledCoefficient eta n‖ ≤ C / (11 : ℝ) ^ hi := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) * scaledCoefficient eta n =
      ((eta : ℂ) ^ (hi + 1) * scaledCoefficient eta n) / (eta : ℂ) ^ hi := by
    rw [pow_succ]
    field_simp
  rw [hid]
  exact (norm_div_eta_pow_lower (by norm_num : (0 : ℝ) < 11) he _ hi).trans
    (div_le_div_of_nonneg_right h (by positivity))

theorem firstCoefficientEnvelope_bound {eta : ℝ} (he : 11 ≤ eta) (n : ℕ) (hn : n < 11) :
    ‖(eta : ℂ) * scaledCoefficient eta (n + 1)‖ ≤ firstCoefficientEnvelope n := by
  interval_cases n
  · exact first_scaled_one he
  · simpa only [firstCoefficientEnvelope, pow_one] using first_weighted_drop he 2 1 (first_scaled_two he)
  · exact first_scaled_three he
  · simpa only [firstCoefficientEnvelope, pow_one] using first_weighted_drop he 4 1 (first_scaled_four he)
  · exact first_weighted_drop he 5 2 (first_scaled_five he)
  · simpa only [firstCoefficientEnvelope, pow_one] using first_weighted_drop he 6 1 (first_scaled_six he)
  · exact first_weighted_drop he 7 2 (first_scaled_seven he)
  · exact first_weighted_drop he 8 3 (first_scaled_eight he)
  · exact first_weighted_drop he 9 2 (first_scaled_nine he)
  · exact first_weighted_drop he 10 3 (first_scaled_ten he)
  · exact first_weighted_drop he 11 4 (first_scaled_eleven he)

theorem first_correction_scalar :
    (∑ n ∈ Finset.range 11, firstCoefficientEnvelope n * exactGaussianBudget Real.pi n) ≤ 77 / 125 := by
  apply (Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left
    (exactGaussianBudget_rational n) (firstCoefficientEnvelope_nonneg n))).trans
  norm_num [Finset.sum_range_succ, firstCoefficientEnvelope, rationalGaussianMoment]

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
