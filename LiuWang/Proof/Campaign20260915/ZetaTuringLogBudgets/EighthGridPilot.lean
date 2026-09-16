import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.EighthGridCertificates

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem eighth_grid_row_10 : realLogZeta (((10 : ℕ) : ℝ) / 8) ≤ (15274147 / 10000000 : ℝ) := by
  exact eighth_grid_log_certificate (k := 10) (by norm_num) (15274147 / 10000000 : ℝ)
    (by norm_num [eighthZetaUpper, negativeEighthBound, Finset.sum_range_succ])

theorem eighth_grid_row_11 : realLogZeta (((11 : ℕ) : ℝ) / 8) ≤ (5929379 / 5000000 : ℝ) := by
  exact eighth_grid_log_certificate (k := 11) (by norm_num) (5929379 / 5000000 : ℝ)
    (by norm_num [eighthZetaUpper, negativeEighthBound, Finset.sum_range_succ])

theorem eighth_grid_row_12 : realLogZeta (((12 : ℕ) : ℝ) / 8) ≤ (9612863 / 10000000 : ℝ) := by
  exact eighth_grid_log_certificate (k := 12) (by norm_num) (9612863 / 10000000 : ℝ)
    (by norm_num [eighthZetaUpper, negativeEighthBound, Finset.sum_range_succ])

theorem eighth_grid_row_13 : realLogZeta (((13 : ℕ) : ℝ) / 8) ≤ (499353 / 625000 : ℝ) := by
  exact eighth_grid_log_certificate (k := 13) (by norm_num) (499353 / 625000 : ℝ)
    (by norm_num [eighthZetaUpper, negativeEighthBound, Finset.sum_range_succ])

theorem eighth_grid_sum_10_14_upper :
    (∑ k ∈ Finset.Ico (10 : ℕ) 14, realLogZeta ((k : ℝ) / 8)) ≤
      (5591927 / 1250000 : ℝ) := by
  have h10 := eighth_grid_row_10
  have h11 := eighth_grid_row_11
  have h12 := eighth_grid_row_12
  have h13 := eighth_grid_row_13
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h10, h11, h12, h13]

#print axioms eighth_grid_sum_10_14_upper

theorem eighth_grid_sum_12_14_upper :
    (∑ k ∈ Finset.Ico (12 : ℕ) 14, realLogZeta ((k : ℝ) / 8)) ≤
      (17602511 / 10000000 : ℝ) := by
  have h12 := eighth_grid_row_12
  have h13 := eighth_grid_row_13
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h12, h13]

#print axioms eighth_grid_sum_12_14_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
