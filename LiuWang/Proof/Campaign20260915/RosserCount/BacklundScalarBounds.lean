import LiuWang.Proof.Campaign20260915.RosserCount.BacklundCenterNumeric

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_jensen_log_lower : (113 / 200 : ℝ) ≤ Real.log (44 / 25) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 19 / 69)
    (by norm_num : (19 / 69 : ℝ) < 1) 4
  rw [show (1 + (19 / 69 : ℝ)) / (1 - 19 / 69) = 44 / 25 by norm_num] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem backlund_log_two_pi_lower : (183 / 100 : ℝ) ≤ Real.log (2 * Real.pi) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 21 / 29)
    (by norm_num : (21 / 29 : ℝ) < 1) 10
  rw [show (1 + (21 / 29 : ℝ)) / (1 - 21 / 29) = 25 / 4 by norm_num] at h
  norm_num [Finset.sum_range_succ] at h
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 25 / 4)
    (show (25 / 4 : ℝ) ≤ 2 * Real.pi by linarith [Real.pi_gt_d2])
  linarith

theorem backlund_shifted_log_bounds {T : ℝ} (hT : 1000 ≤ T) :
    1 ≤ Real.log T ∧
      Real.log (T + 33 / 25) ≤ Real.log T + 1 / 500 ∧
      Real.log (Real.log (T + 33 / 25)) ≤ Real.log (Real.log T) + 1 / 500 ∧
      Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) ≤ 1 / 100000 := by
  have hT0 : 0 < T := by linarith
  have hY : 0 < T + 33 / 25 := by linarith
  have hlogT : 1 ≤ Real.log T := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (show (3 : ℝ) ≤ T by linarith)
    linarith [Real.log_three_gt_d9]
  have hlogY0 : 0 < Real.log (T + 33 / 25) := Real.log_pos (by linarith)
  have hshift : Real.log (T + 33 / 25) ≤ Real.log T + 1 / 500 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hY hT0)
    rw [Real.log_div hY.ne' hT0.ne'] at h
    have hq : (T + 33 / 25) / T ≤ (501 / 500 : ℝ) := by
      rw [div_le_iff₀ hT0]
      linarith
    linarith
  have hdouble : Real.log (Real.log (T + 33 / 25)) ≤ Real.log (Real.log T) + 1 / 500 := by
    have hlogT0 : 0 < Real.log T := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos hlogY0 hlogT0)
    rw [Real.log_div hlogY0.ne' hlogT0.ne'] at h
    have hq : Real.log (T + 33 / 25) / Real.log T ≤ (501 / 500 : ℝ) := by
      rw [div_le_iff₀ hlogT0]
      linarith
    linarith
  refine ⟨hlogT, hshift, hdouble, ?_⟩
  have hden : 0 < (T - 33 / 25) ^ 2 - 4 := by nlinarith
  have hnum : 0 < (T - 33 / 25) ^ 2 := by nlinarith
  have h := Real.log_le_sub_one_of_pos (div_pos hnum hden)
  have hq : (T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4) ≤ (100001 / 100000 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

#print axioms backlund_jensen_log_lower
#print axioms backlund_log_two_pi_lower
#print axioms backlund_shifted_log_bounds

end LiuWang.Proof.Campaign20260915.RosserCount
