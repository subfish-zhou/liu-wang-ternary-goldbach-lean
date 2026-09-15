import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Reduction
import LiuWang.Proof.WeightedLowZeros.Continuation.LogBudget

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate

theorem log_ten_pi_bounds :
    3.4 ≤ Real.log (10 * Real.pi) ∧ Real.log (10 * Real.pi) ≤ 4 := by
  have hp : 0 < 10 * Real.pi := by positivity
  constructor
  · apply (Real.le_log_iff_exp_le hp).mpr
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 17
    rw [← Real.exp_nat_mul] at he
    norm_num only [Nat.cast_ofNat, mul_one] at he
    have hpow : Real.exp 3.4 ^ (5 : ℕ) ≤ (30 : ℝ) ^ 5 := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat, show (5 : ℝ) * 3.4 = 17 by norm_num]
      exact he.trans (by norm_num)
    have h := (pow_le_pow_iff_left₀ (Real.exp_pos _).le
      (by norm_num : (0 : ℝ) ≤ 30) (by norm_num : (5 : ℕ) ≠ 0)).mp hpow
    linarith [Real.pi_gt_three]
  · apply (Real.log_le_iff_le_exp hp).mpr
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
      (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1) 4
    rw [← Real.exp_nat_mul] at he
    norm_num at he
    linarith [Real.pi_lt_four]

theorem exp_euler_le_two : Real.exp Real.eulerMascheroniConstant ≤ 2 := by
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le
    (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 2
  rw [← Real.exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat, mul_one] at he
  have hpow : Real.exp Real.eulerMascheroniConstant ^ (3 : ℕ) ≤ (2 : ℝ) ^ 3 := by
    rw [← Real.exp_nat_mul]
    calc
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by
        norm_num
        linarith [Real.eulerMascheroniConstant_lt_two_thirds])
      _ ≤ _ := he.trans (by norm_num)
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le
    (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).mp hpow

theorem source_loglog_bounds {L : ℝ} (hL : 3100 ≤ L) :
    3 ≤ Real.log (Real.log (L ^ 6)) ∧
      Real.log (Real.log (L ^ 6)) ≤ 4 * (L / 3100) := by
  have hL0 : 0 < L := by linarith
  have hr : 1 ≤ L / 3100 := by linarith
  have hr0 : 0 < L / 3100 := by positivity
  have hl : 8 ≤ Real.log L :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hu := (div_le_iff₀ hL0).mp (log_over_self_bound hL)
  have hu' : 6 * Real.log L ≤ 48.24 * (L / 3100) := by linarith
  have hc : Real.log (48.24 : ℝ) ≤ 4 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 48.24)).mpr
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
      (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1) 4
    rw [← Real.exp_nat_mul] at he
    norm_num at he ⊢
    linarith
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor
  · apply (Real.le_log_iff_exp_le (by linarith : 0 < 6 * Real.log L)).mpr
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
    rw [← Real.exp_nat_mul] at he
    norm_num at he
    linarith
  · have h := Real.log_le_log (by linarith : 0 < 6 * Real.log L) hu'
    rw [Real.log_mul (by norm_num : (48.24 : ℝ) ≠ 0) hr0.ne'] at h
    linarith [Real.log_le_sub_one_of_pos hr0]

theorem sourceNu_sixth_bounds {L : ℝ} (hL : 3100 ≤ L) :
    0 ≤ sourceNu (L ^ 6) ∧ sourceNu (L ^ 6) ≤ 9 * (L / 3100) := by
  have hl := source_loglog_bounds hL
  have hr : 1 ≤ L / 3100 := by linarith
  have hd : 2.50637 / Real.log (Real.log (L ^ 6)) ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (Real.log (L ^ 6)))).mpr
    linarith
  have hp := mul_le_mul exp_euler_le_two hl.2 (by linarith) (by norm_num)
  have hl0 : 0 ≤ Real.log (Real.log (L ^ 6)) := by linarith
  unfold sourceNu
  constructor
  · positivity
  · nlinarith only [hp, hd, hr]

theorem original_log_interval {L : ℝ} (hL : 3100 ≤ L) :
    0 < Real.log (10 * Real.pi * L ^ 7) ∧
      Real.log (10 * Real.pi * L ^ 7) ≤ Real.log (L ^ 21) := by
  have hL0 : 0 < L := by linarith
  have hl : 8 ≤ Real.log L :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  rw [Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0) (pow_pos hL0 7).ne',
    Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith [log_ten_pi_bounds.1, log_ten_pi_bounds.2]

theorem endpoint_rational_certificate :
    (700000 / 3100 : ℝ) * Real.exp (-24.76) ≤ 6 / 1000000000 := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.71)
    (by linarith [Real.exp_one_gt_d9] : (2.71 : ℝ) ≤ Real.exp 1) 24
  rw [← Real.exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat, mul_one] at he
  have ht := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.76)
  have h := mul_le_mul he ht (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at h
  norm_num only [show (24 : ℝ) + 0.76 = 24.76 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num at h ⊢
  linarith only [h]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate
