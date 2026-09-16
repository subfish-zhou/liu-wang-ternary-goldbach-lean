import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesCertificates

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_1 :
    ((999999 / 1000000) : ℝ) ≤ (1 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 1 ≤ 0 := by
  have hlog : Real.log ((1 : ℕ) : ℝ) ≤ 0 := by
    apply log_nat_upper_certificate 1 0 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 1 (by norm_num)
    1 (1000001 / 1000000) 0 (999999 / 1000000) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_2 :
    ((552427 / 1562500) : ℝ) ≤ (2 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 2 ≤ (4901293 / 20000000) := by
  have hlog : Real.log ((2 : ℕ) : ℝ) ≤ (433217 / 625000) := by
    apply log_nat_upper_certificate 2 1 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 2 (by norm_num)
    (1414213 / 1000000) (707107 / 500000) (433217 / 625000) (552427 / 1562500) (4901293 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_3 :
    ((9622503 / 50000000) : ℝ) ≤ (3 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 3 ≤ (10571407 / 50000000) := by
  have hlog : Real.log ((3 : ℕ) : ℝ) ≤ (10986123 / 10000000) := by
    apply log_nat_upper_certificate 3 1 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 3 (by norm_num)
    (34641 / 20000) (1732051 / 1000000) (10986123 / 10000000) (9622503 / 50000000) (10571407 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_4 :
    ((12499993 / 100000000) : ℝ) ≤ (4 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 4 ≤ (433217 / 2500000) := by
  have hlog : Real.log ((4 : ℕ) : ℝ) ≤ (433217 / 312500) := by
    apply log_nat_upper_certificate 4 2 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 4 (by norm_num)
    2 (2000001 / 1000000) (433217 / 312500) (12499993 / 100000000) (433217 / 2500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

#print axioms threeHalves_row_4

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
