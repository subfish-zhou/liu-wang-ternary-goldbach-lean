import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.FiniteLogBudgets

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem log_source_K_upper : Real.log (253 / 100 : ℝ) ≤ 9283 / 10000 := by
  exact log_real_upper_certificate (by norm_num)
    (by norm_num [Finset.sum_range_succ])

theorem source_real_integral_budget_upper :
    realLogTail (5 / 4) - unitShiftRealBudget +
      3 / 8 * (Real.log (253 / 100 : ℝ) + realLogZeta (5 / 4)) ≤
      (35219 / 10000 : ℝ) := by
  linarith [realLogTail_sub_unitShift_numeric_upper, log_source_K_upper,
    realLogZeta_fiveFourths_upper]

#print axioms log_source_K_upper
#print axioms source_real_integral_budget_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
