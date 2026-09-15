import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5Scalar
import LiuWang.Proof.Campaign20260915.ThirdBudgets.EndpointTable
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ScalarDomain

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem endpoint_density_rational_certificate :
    (16 * 7.56 * 500000 * 59.78 ^ 6 / (250 * 3100 ^ 2) : ℝ) *
        Real.exp (-24.73) ≤ 0.022449 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 24
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  have hs := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.73)
  have h := mul_le_mul hp hs (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at h
  norm_num only [show (24 : ℝ) + 0.73 = 24.73 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num at h ⊢
  linarith only [h]

theorem endpoint_density_log_scale {L : ℝ} (hL : 3100 ≤ L) :
    Real.log (10 * Real.pi * L ^ 7) ^ 6 / L *
        Real.exp (-0.478 * (L - 7) / Real.log (10 * Real.pi * L ^ 7)) ≤
      (59.78 ^ 6 / 3100 : ℝ) * Real.exp (-24.73) := by
  let r := Real.sqrt (L / 3100)
  let s := Real.log (10 * Real.pi * L ^ 7)
  have hL0 : 0 < L := by linarith
  have hr : 1 ≤ r := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ L / 3100 by linarith)
    simpa only [Real.sqrt_one] using h
  have hr0 : 0 < r := by linarith
  have hr2 : r ^ 2 = L / 3100 := Real.sq_sqrt (by positivity)
  have hid : L = 3100 * r ^ 2 := by linarith
  have hs0 : 0 < s := (M6Certificate.original_log_interval hL).1
  have hs : s ≤ 59.78 * r := by
    have hlog : Real.log L = Real.log 3100 + 2 * Real.log r := by
      rw [hid, Real.log_mul (by norm_num : (3100 : ℝ) ≠ 0) (pow_pos hr0 2).ne',
        Real.log_pow]
      norm_num
    dsimp only [s]
    rw [Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0)
      (pow_pos hL0 7).ne', Real.log_pow]
    simp only [Nat.cast_ofNat]
    rw [hlog]
    linarith [log_3100_bounds.2, Real.log_le_sub_one_of_pos hr0,
      LiuWang.Proof.SourceRoute.SecondArc.Continuation.log_ten_pi_le_35]
  have hexponent : -0.478 * (L - 7) / s ≤ -24.73 * r := by
    apply (div_le_iff₀ hs0).mpr
    have hm := mul_le_mul_of_nonneg_left hs hr0.le
    nlinarith [sq_nonneg (r - 1)]
  have hpow := pow_le_pow_left₀ hs0.le hs 6
  rw [mul_pow] at hpow
  have hratio : s ^ 6 / L ≤ (59.78 ^ 6 / 3100 : ℝ) * r ^ 4 := by
    apply (div_le_iff₀ hL0).mpr
    rw [hid]
    nlinarith only [hpow]
  have htail : r ^ 4 * Real.exp (-24.73 * r) ≤ Real.exp (-24.73) := by
    have hrExp : r ≤ Real.exp (r - 1) := by linarith [Real.add_one_le_exp (r - 1)]
    have hp := pow_le_pow_left₀ hr0.le hrExp 4
    rw [← Real.exp_nat_mul] at hp
    have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-24.73 * r)).le
    rw [← Real.exp_add] at hm
    exact hm.trans (Real.exp_le_exp.mpr (by norm_num; linarith))
  have h := mul_le_mul hratio (Real.exp_le_exp.mpr hexponent)
    (Real.exp_pos _).le (by positivity : 0 ≤ (59.78 ^ 6 / 3100 : ℝ) * r ^ 4)
  have hh := mul_le_mul_of_nonneg_left htail
    (by norm_num : (0 : ℝ) ≤ 59.78 ^ 6 / 3100)
  change s ^ 6 / L * Real.exp (-0.478 * (L - 7) / s) ≤ _
  nlinarith only [h, hh]

theorem endpoint_density_scalar_paid {L : ℝ} (hL : 3100 ≤ L) :
    (16 * 7.56 / (250 * 3100) : ℝ) / L *
        (500000 * Real.log (10 * Real.pi * L ^ 7) ^ 6 *
          Real.exp (-0.478 * (L - 7) / Real.log (10 * Real.pi * L ^ 7))) ≤
      0.022449 := by
  have h := mul_le_mul_of_nonneg_left (endpoint_density_log_scale hL)
    (by norm_num : (0 : ℝ) ≤ 16 * 7.56 * 500000 / (250 * 3100))
  calc
    _ ≤ (16 * 7.56 * 500000 * 59.78 ^ 6 / (250 * 3100 ^ 2) : ℝ) *
        Real.exp (-24.73) := by
      norm_num at h ⊢
      simp only [div_eq_mul_inv] at h ⊢
      nlinarith only [h]
    _ ≤ _ := endpoint_density_rational_certificate

#print axioms endpoint_density_scalar_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
