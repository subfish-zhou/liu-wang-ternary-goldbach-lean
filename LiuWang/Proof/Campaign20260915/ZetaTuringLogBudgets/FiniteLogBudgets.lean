import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.EighthGridBlock03

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem eighth_grid_sum_10_128_upper :
    (∑ k ∈ Finset.Ico (10 : ℕ) 128, realLogZeta ((k : ℝ) / 8)) ≤
      (51435287 / 5000000 : ℝ) := by
  have hp := eighth_grid_sum_10_14_upper
  have h0 := eighth_grid_sum_14_46_upper
  have h1 := eighth_grid_sum_46_78_upper
  have h2 := eighth_grid_sum_78_110_upper
  have h3 := eighth_grid_sum_110_128_upper
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 10 ≤ 14)] at hp
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 14 ≤ 46)] at h0
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 46 ≤ 78)] at h1
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 78 ≤ 110)] at h2
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 110 ≤ 128)] at h3
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 10 ≤ 128)]
  linarith

theorem eighth_grid_sum_12_20_upper :
    (∑ k ∈ Finset.Ico (12 : ℕ) 20, realLogZeta ((k : ℝ) / 8)) ≤
      (46594557 / 10000000 : ℝ) := by
  have hp := eighth_grid_sum_12_14_upper
  have h0 := eighth_grid_sum_14_20_upper
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 12 ≤ 14)] at hp
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 14 ≤ 20)] at h0
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 12 ≤ 20)]
  linarith

theorem eighth_grid_sum_40_128_upper :
    (∑ k ∈ Finset.Ico (40 : ℕ) 128, realLogZeta ((k : ℝ) / 8)) ≤
      (2072087 / 5000000 : ℝ) := by
  have h0 := eighth_grid_sum_40_46_upper
  have h1 := eighth_grid_sum_46_78_upper
  have h2 := eighth_grid_sum_78_110_upper
  have h3 := eighth_grid_sum_110_128_upper
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 40 ≤ 46)] at h0
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 46 ≤ 78)] at h1
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 78 ≤ 110)] at h2
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 110 ≤ 128)] at h3
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 40 ≤ 128)]
  linarith

theorem logGridUpper_eighth_eq_sum (a b : ℕ) :
    logGridUpper ((a : ℝ) / 8) (1 / 8) (b - a) =
      (∑ k ∈ Finset.Ico a b, realLogZeta ((k : ℝ) / 8)) / 8 := by
  rw [logGridUpper, Finset.sum_Ico_eq_sum_range, mul_comm, mul_one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  push_cast
  ring

theorem upper_eighth_grid_budget :
    logGridUpper (5 / 4) (1 / 8) 118 ≤ (51435287 / 40000000 : ℝ) := by
  have he := logGridUpper_eighth_eq_sum 10 128
  norm_num at he
  rw [he]
  linarith [eighth_grid_sum_10_128_upper]

theorem unitShift_eighth_grid_budget :
    unitShiftGridCost 4 ≤ (105208037 / 80000000 : ℝ) := by
  have he1 := logGridUpper_eighth_eq_sum 12 20
  have he2 := logGridUpper_eighth_eq_sum 20 24
  have he3 := logGridUpper_eighth_eq_sum 40 128
  norm_num at he1 he2 he3
  unfold unitShiftGridCost
  norm_num
  rw [he1, he2, he3]
  linarith [eighth_grid_sum_12_20_upper, eighth_grid_sum_20_24_upper,
    eighth_grid_sum_40_128_upper]

theorem realLogTail_fiveFourths_upper :
    realLogTail (5 / 4) ≤ (154345861 / 120000000 : ℝ) := by
  have hi := (logGrid_integral_bounds (by norm_num : (1 : ℝ) < 5 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 8) 118).2
  norm_num at hi
  rw [realLogTail_split (by norm_num : (1 : ℝ) < 5 / 4) (by norm_num : (1 : ℝ) < 16)]
  linarith [upper_eighth_grid_budget, realLogTail_sixteen_budget.2]

theorem unitShiftRealBudget_numeric_lower :
    -(315664111 / 240000000 : ℝ) ≤ unitShiftRealBudget := by
  have h := unitShiftRealBudget_grid_lower (by norm_num : 0 < 4)
  linarith [unitShift_eighth_grid_budget]

theorem realLogTail_sub_unitShift_numeric_upper :
    realLogTail (5 / 4) - unitShiftRealBudget ≤ (208118611 / 80000000 : ℝ) := by
  linarith [realLogTail_fiveFourths_upper, unitShiftRealBudget_numeric_lower]

theorem horizontalLogMass_numeric_upper {T : ℝ} (hT : T ≠ 0) :
    horizontalLogMass T ≤
      (∫ x in (1 / 2 : ℝ)..(5 / 4), Real.log ‖riemannZeta (horizontalAt T x)‖) +
        (154345861 / 120000000 : ℝ) := by
  have h := horizontalLogMass_grid_upper hT (by norm_num : 0 < 2)
  norm_num at h
  linarith [upper_eighth_grid_budget]

theorem horizontalLogMass_numeric_lower {T : ℝ} (hT : T ≠ 0) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2),
      Real.log ‖riemannZeta (horizontalAt T x) /
        riemannZeta (horizontalAt T (x + 1))‖) -
      (315664111 / 240000000 : ℝ) ≤ horizontalLogMass T := by
  have h := horizontalLogMass_grid_lower hT (by norm_num : 0 < 4)
  linarith [unitShift_eighth_grid_budget]

#print axioms realLogTail_fiveFourths_upper
#print axioms unitShiftRealBudget_numeric_lower
#print axioms realLogTail_sub_unitShift_numeric_upper
#print axioms horizontalLogMass_numeric_upper
#print axioms horizontalLogMass_numeric_lower

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
