import LiuWang.Proof.Campaign20260915.Parent.RealNormalizationAudit
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SourceLocalBudgets

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem original_scale_zero {eta : ℝ} (he : 0 < eta) :
    (eta ^ 2) ^ (-(3 / 4 : ℝ)) = eta ^ (-(1 / 2 : ℝ)) / eta := by
  rw [← Real.rpow_natCast eta 2, ← Real.rpow_mul he.le]
  have h := Real.rpow_sub he (-(1 / 2 : ℝ)) 1
  rw [Real.rpow_one] at h
  rw [← h]
  norm_num

theorem original_scale_two {eta : ℝ} (he : 0 < eta) :
    (eta ^ 2) ^ (-(7 / 4 : ℝ)) = eta ^ (-(1 / 2 : ℝ)) / eta ^ 3 := by
  rw [← Real.rpow_natCast eta 2, ← Real.rpow_mul he.le,
    ← Real.rpow_natCast eta 3, ← Real.rpow_sub he]
  norm_num

theorem right_power_scale {eta : ℝ} (he : 0 < eta) :
    eta ^ (-(3 / 2 : ℝ)) = eta ^ (-(1 / 2 : ℝ)) / eta := by
  have h := Real.rpow_sub he (-(1 / 2 : ℝ)) 1
  rw [Real.rpow_one] at h
  rw [← h]
  norm_num

theorem sourceTime_lower {eta : ℝ} (_he : 0 ≤ eta) :
    6 * eta ^ 2 ≤ sourceTime eta := by
  rw [sourceTime_eq]
  nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg eta)]

theorem exp_neg_quadratic_bound {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 2 / x ^ 2 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 2
  norm_num at h
  rw [Real.exp_neg, inv_eq_one_div]
  calc
    _ ≤ 1 / (x ^ 2 / 2) := one_div_le_one_div_of_le (by positivity) h
    _ = _ := by ring

theorem source_phase_exponential_scalar {eta : ℝ} (he : 0 < eta) :
    Real.exp (-Real.pi * sourceTime eta) ≤ 1 / (162 * eta ^ 4) := by
  have ht := sourceTime_pos he
  have hx : 18 * eta ^ 2 ≤ Real.pi * sourceTime eta := by
    have h := sourceTime_lower he.le
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le ht.le]
  have hs : 324 * eta ^ 4 ≤ (Real.pi * sourceTime eta) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 18 * eta ^ 2) hx 2
    nlinarith [show (18 * eta ^ 2) ^ 2 = 324 * eta ^ 4 by ring]
  rw [neg_mul]
  exact (exp_neg_quadratic_bound (mul_pos Real.pi_pos ht)).trans
    ((div_le_div_of_nonneg_left (by norm_num) (by positivity) hs).trans_eq (by ring))

theorem source_real_phase_scalar {eta : ℝ} (he : 0 < eta) :
    sourceRealPhaseBudget eta ≤ 1 / (100 * eta ^ 4) := by
  have hs : 36 * eta ^ 4 ≤ sourceTime eta ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 6 * eta ^ 2) (sourceTime_lower he.le) 2
    nlinarith [show (6 * eta ^ 2) ^ 2 = 36 * eta ^ 4 by ring]
  have hq := source_phase_exponential_scalar he
  have hd : 49 / (512 * sourceTime eta ^ 2) ≤ 49 / (18432 * eta ^ 4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  apply (sourceRealPhaseBudget_uniform he).trans
  apply (add_le_add hd hq).trans
  field_simp
  norm_num

theorem source_imaginary_phase_scalar {eta : ℝ} (he : 1 ≤ eta) :
    sourcePhaseBudget eta ≤ 2 / (25 * eta ^ 2) := by
  have he0 : 0 < eta := by linarith
  have ht := sourceTime_lower he0.le
  have hq := source_phase_exponential_scalar he0
  have hs : eta ^ 2 ≤ eta ^ 4 := by
    nlinarith [sq_nonneg (eta ^ 2 - 1), show 1 ≤ eta ^ 2 by nlinarith]
  have hq' : Real.exp (-Real.pi * sourceTime eta) ≤ 1 / (162 * eta ^ 2) :=
    hq.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith))
  have hd : 7 / (16 * sourceTime eta) ≤ 7 / (96 * eta ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  apply (sourcePhaseBudget_uniform he0).trans
  apply (add_le_add hd hq').trans
  field_simp
  norm_num

theorem original_right_zero {eta : ℝ} (he : 11 ≤ eta) :
    |sourceRightNormalized eta| ≤ (1 / 10) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have he0 : 0 < eta := by linarith
  have ht : 20 ≤ sourceTime eta / 11 := by
    have h := sourceTime_lower he0.le
    nlinarith
  have hE : 20 ≤ Real.exp (sourceTime eta / 11) := by
    linarith [Real.add_one_le_exp (sourceTime eta / 11)]
  have hq : Real.exp (-sourceTime eta / 11) ≤ 1 / 20 := by
    rw [neg_div, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hE
  have hc : 11 / (2 * Real.pi) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hb := Parent.RealNormalizationAudit.actual_normalized_right (by linarith : 1 ≤ eta)
  rw [original_scale_zero he0]
  rw [right_power_scale he0] at hb
  apply hb.trans
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ eta ^ (-(1 / 2 : ℝ)) / eta))
    hq (Real.exp_pos _).le (by positivity : 0 ≤ 2 * (eta ^ (-(1 / 2 : ℝ)) / eta))
  nlinarith

theorem original_right_two {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    |sourceRightNormalized eta| ≤ (1 / 10) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have he0 : 0 < eta := by nlinarith
  have hx : eta ^ 2 / 2 ≤ sourceTime eta / 11 := by
    have h := sourceTime_lower he
    nlinarith
  have hE : 20 * eta ^ 2 ≤ Real.exp (sourceTime eta / 11) := by
    have h := Real.quadratic_le_exp_of_nonneg (by nlinarith : 0 ≤ sourceTime eta / 11)
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ eta ^ 2 / 2) hx 2
    nlinarith [sq_nonneg (eta ^ 2 - 2000)]
  have hq : Real.exp (-sourceTime eta / 11) ≤ 1 / (20 * eta ^ 2) := by
    rw [neg_div, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hE
  have hc : 11 / (2 * Real.pi) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hb := Parent.RealNormalizationAudit.actual_normalized_right (by nlinarith : 1 ≤ eta)
  rw [original_scale_two he0]
  rw [right_power_scale he0] at hb
  apply hb.trans
  apply (mul_le_mul
    (mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ eta ^ (-(1 / 2 : ℝ)) / eta))
    hq (Real.exp_pos _).le (by positivity : 0 ≤ 2 * (eta ^ (-(1 / 2 : ℝ)) / eta))).trans_eq
  ring

theorem original_left_zero {eta : ℝ} (he : 11 ≤ eta) :
    |sourceLeftNormalized eta| ≤ (1 / 10) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) :=
  (Parent.RealNormalizationAudit.actual_normalized_left (by linarith)).trans
    (ZetaC2LeftTail.left_scalar_original_scale (by linarith) (by norm_num))

theorem original_left_two {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    |sourceLeftNormalized eta| ≤ (1 / 10) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) :=
  (Parent.RealNormalizationAudit.actual_normalized_left (by nlinarith : 10 ≤ eta)).trans
    (ZetaC2LeftTail.left_scalar_original_scale (by nlinarith) (by norm_num))

#print axioms source_real_phase_scalar
#print axioms source_imaginary_phase_scalar
#print axioms original_right_zero
#print axioms original_right_two

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
