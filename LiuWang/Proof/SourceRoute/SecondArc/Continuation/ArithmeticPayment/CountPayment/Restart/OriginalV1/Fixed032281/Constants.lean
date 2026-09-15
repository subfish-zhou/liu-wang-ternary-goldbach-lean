import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.EulerConstant

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

theorem exp_euler_upper : Real.exp Real.eulerMascheroniConstant ≤ 1.7810725 := by
  have he := Real.exp_bound' (x := (0.57721568 : ℝ)) (by norm_num) (by norm_num)
    (n := 16) (by norm_num)
  norm_num [Finset.sum_range_succ] at he
  have hm := Real.exp_le_exp.mpr euler_upper
  linarith only [he, hm]

theorem exp_phase_upper : Real.exp (4 * (0.478 : ℝ)) ≤ 6.76661 := by
  have he := Real.exp_bound' (x := (0.956 : ℝ)) (by norm_num) (by norm_num)
    (n := 16) (by norm_num)
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 2
  rw [← Real.exp_nat_mul] at hp
  norm_num [Finset.sum_range_succ] at hp
  norm_num only [mul_assoc] at hp ⊢
  linarith only [hp]

theorem log_31_32_bounds :
    -0.031748699 ≤ Real.log (31 / 32 : ℝ) ∧ Real.log (31 / 32 : ℝ) ≤ -0.031748697 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 32 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith

theorem log_3100_interval :
    8.039157387 ≤ Real.log (3100 : ℝ) ∧ Real.log (3100 : ℝ) ≤ 8.039157395 := by
  have he : Real.log (3100 : ℝ) =
      7 * Real.log 2 + 2 * Real.log 5 + Real.log (31 / 32 : ℝ) := by
    rw [show (3100 : ℝ) = 2 ^ (7 : ℕ) * 5 ^ (2 : ℕ) * (31 / 32) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
    Real.log_five_gt_d9, Real.log_five_lt_d9, log_31_32_bounds.1, log_31_32_bounds.2]

theorem window_H_lower :
    3093.092244719 ≤ (3100 : ℝ) + Real.log 0.001 := by
  have he : Real.log (0.001 : ℝ) = -3 * (Real.log 2 + Real.log 5) := by
    rw [show (0.001 : ℝ) = ((2 * 5) ^ (3 : ℕ))⁻¹ by norm_num,
      Real.log_inv, Real.log_pow, Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [he]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem loglog_interval :
    3.182936 ≤ Real.log (Real.log ((3100 : ℝ) ^ (3 : ℕ))) ∧
      Real.log (Real.log ((3100 : ℝ) ^ (3 : ℕ))) ≤ 3.182937 := by
  have hlog := log_3100_interval
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hp : 0 < 3 * Real.log (3100 : ℝ) := by linarith
  constructor
  · apply (Real.le_log_iff_exp_le hp).mpr
    have he := Real.exp_bound' (x := (3.182936 / 4 : ℝ)) (by norm_num) (by norm_num)
      (n := 16) (by norm_num)
    have hb := pow_le_pow_left₀ (Real.exp_pos _).le he 4
    rw [← Real.exp_nat_mul] at hb
    norm_num [Finset.sum_range_succ] at hb
    apply hb.trans
    linarith
  · apply (Real.log_le_iff_le_exp hp).mpr
    have he := Real.sum_le_exp_of_nonneg (x := (3.182937 / 4 : ℝ)) (by norm_num) 16
    have hb := pow_le_pow_left₀ (by positivity) he 4
    rw [← Real.exp_nat_mul] at hb
    norm_num [Finset.sum_range_succ] at hb
    apply le_trans _ hb
    linarith

theorem sourceNu_fixed_upper :
    sourceNu ((3100 : ℝ) ^ (3 : ℕ)) ≤
      1.7810725 * 3.182937 + 2.50637 / 3.182936 :=
  FixedIntegral.sourceNu_upper_of_intervals exp_euler_upper (by norm_num)
    loglog_interval.1 loglog_interval.2

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
