import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.EulerConstant

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

theorem log_ten_billion_bounds :
    (23.02585 : ℝ) ≤ Real.log 10000000000 ∧
      Real.log 10000000000 ≤ 23.025851 := by
  rw [show (10000000000 : ℝ) = (2 * 5) ^ 10 by norm_num, Real.log_pow,
    Real.log_mul (by norm_num) (by norm_num)]
  constructor <;> norm_num <;>
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]

theorem loglog_ten_billion_bounds :
    (3.136617 : ℝ) ≤ Real.log (Real.log 10000000000) ∧
      Real.log (Real.log 10000000000) ≤ 3.136618 := by
  have h24 : (3.1780538294 : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ 3.1780538312 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    constructor <;> norm_num <;>
      linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9]
  constructor
  · have h := Real.log_div_le_sum_range_add
      (show (0 : ℝ) ≤ (24 - 23.02585) / (24 + 23.02585) by norm_num)
      (show ((24 - 23.02585) / (24 + 23.02585) : ℝ) < 1 by norm_num) 2
    have he : ((1 + (24 - 23.02585) / (24 + 23.02585)) /
        (1 - (24 - 23.02585) / (24 + 23.02585)) : ℝ) = 24 / 23.02585 := by norm_num
    rw [he, Real.log_div (by norm_num) (by norm_num)] at h
    norm_num [Finset.sum_range_succ] at h
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 23.02585)
      log_ten_billion_bounds.1
    linarith [h24.1]
  · have h := Real.sum_range_le_log_div
      (show (0 : ℝ) ≤ (24 - 23.025851) / (24 + 23.025851) by norm_num)
      (show ((24 - 23.025851) / (24 + 23.025851) : ℝ) < 1 by norm_num) 2
    have he : ((1 + (24 - 23.025851) / (24 + 23.025851)) /
        (1 - (24 - 23.025851) / (24 + 23.025851)) : ℝ) = 24 / 23.025851 := by norm_num
    rw [he, Real.log_div (by norm_num) (by norm_num)] at h
    norm_num [Finset.sum_range_succ] at h
    have hl := Real.log_le_log (Real.log_pos (by norm_num : (1 : ℝ) < 10000000000))
      log_ten_billion_bounds.2
    linarith [h24.2]

theorem nu_ten_billion_le : nu 10000000000 ≤ 6.38563 := by
  have hu : 0 ≤ Real.log (Real.log (10000000000 : ℝ)) := by
    linarith [loglog_ten_billion_bounds.1]
  have h := mul_le_mul exp_gamma_le_decimal loglog_ten_billion_bounds.2 hu (by norm_num)
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2.50637)
    (by norm_num : (0 : ℝ) < 3.136617) loglog_ten_billion_bounds.1
  unfold nu
  norm_num at h hd ⊢
  linarith

theorem ten_billion_power_ge : (6.38565 : ℝ) ≤ (10000000000 : ℝ) ^ (0.080521 : ℝ) := by
  have he : (1.85406 : ℝ) ≤ Real.log 10000000000 * 0.080521 := by
    linarith [log_ten_billion_bounds.1]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.85406) 10
  have hprod := mul_le_mul Real.exp_one_gt_d9.le h (by positivity) (Real.exp_pos 1).le
  rw [← Real.exp_add] at hprod
  norm_num [Finset.sum_range_succ, Nat.factorial] at hprod
  rw [Real.rpow_def_of_pos (by norm_num)]
  exact (by linarith : (6.38565 : ℝ) ≤ Real.exp 1.85406).trans (Real.exp_le_exp.mpr he)

theorem nu_le_source_power {x : ℝ} (hx : 10000000000 ≤ x) :
    nu x ≤ x ^ (0.080521 : ℝ) := by
  have hg := nu_growth (x := 10000000000) (a := 0.080521) (by norm_num) hx (by
    have ht := log_ten_billion_bounds.1
    have hu := loglog_ten_billion_bounds.1
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log (10000000000 : ℝ) - 23)
      (by linarith : 0 ≤ Real.log (Real.log (10000000000 : ℝ)) - 3)])
  calc
    nu x ≤ nu 10000000000 * (x / 10000000000) ^ (0.080521 : ℝ) := hg
    _ ≤ (10000000000 : ℝ) ^ (0.080521 : ℝ) *
        (x / 10000000000) ^ (0.080521 : ℝ) :=
      mul_le_mul_of_nonneg_right (nu_ten_billion_le.trans
        ((by norm_num : (6.38563 : ℝ) ≤ 6.38565).trans ten_billion_power_ge))
        (Real.rpow_nonneg (by linarith) _)
    _ = _ := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      congr 1
      ring

theorem exp_tail_anchor : (5280000 : ℝ) ≤ Real.exp 15.48 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.48) 6
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 15
  have hprod := mul_le_mul hp h (by positivity) (by positivity)
  rw [← Real.exp_nat_mul, ← Real.exp_add] at hprod
  norm_num [Finset.sum_range_succ, Nat.factorial] at hprod
  linarith

theorem source_power_tail_endpoint :
    (10000000000 : ℝ) ^ (1 / 6 - 1 + 2 * 0.080521 : ℝ) ≤ 1 / 5280000 := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have he : Real.log (10000000000 : ℝ) * (1 / 6 - 1 + 2 * 0.080521) ≤ -15.48 := by
    linarith [log_ten_billion_bounds.1]
  apply (Real.exp_le_exp.mpr he).trans
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) exp_tail_anchor

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
