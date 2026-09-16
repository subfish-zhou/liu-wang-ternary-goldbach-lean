import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.SourceRealBudget
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBudget

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

def originalTuringScalarConstant : ℝ :=
  realLogTail (5 / 4) - unitShiftRealBudget +
    3 / 8 * (Real.log (253 / 100 : ℝ) + realLogZeta (5 / 4)) +
    37 / 25 * (-(logDeriv riemannZeta (3 / 2 : ℂ)).re) -
    6 / 25 * Real.log (2 * Real.pi) + 3 / 12500

def originalTuringScalarSlope : ℝ :=
  ((3 / 32 : ℝ) + (37 / 25 - 1) / 2) / Real.pi

theorem original_error_fees_identity :
    (37 / 25 : ℝ) * (1 / 10000) + 9 / 100000 + 1 / 500000 = 3 / 12500 := by
  norm_num

theorem original_reference_gamma_log_identity {T : ℝ} (hT : 0 < T) :
    (37 / 25 : ℝ) * (Real.log (T / (2 * Real.pi)) / 2) -
      Real.log (T / 2) / 2 + Real.log Real.pi / 2 =
        6 / 25 * Real.log T - 6 / 25 * Real.log (2 * Real.pi) := by
  rw [Real.log_div hT.ne' (by positivity), Real.log_div hT.ne' (by norm_num)]
  simp only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

theorem log_two_pi_lower : (5 / 3 : ℝ) ≤ Real.log (2 * Real.pi) := by
  have hp := Real.log_le_log (Real.exp_pos 1)
    (Real.exp_one_lt_three.le.trans Real.pi_gt_three.le)
  rw [Real.log_exp] at hp
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  linarith [Real.log_two_gt_d9]

theorem originalTuringScalarConstant_upper :
    originalTuringScalarConstant ≤ (267551 / 50000 : ℝ) := by
  unfold originalTuringScalarConstant
  linarith [source_real_integral_budget_upper, real_logDeriv_threeHalves_upper,
    log_two_pi_lower]

theorem originalTuringScalarConstant_div_pi_upper :
    originalTuringScalarConstant / Real.pi < (171 / 100 : ℝ) := by
  rw [div_lt_iff₀ Real.pi_pos]
  linarith [originalTuringScalarConstant_upper, Real.pi_gt_d2]

theorem originalTuringScalarSlope_upper :
    originalTuringScalarSlope < (57 / 500 : ℝ) := by
  unfold originalTuringScalarSlope
  rw [div_lt_iff₀ Real.pi_pos]
  linarith [Real.pi_gt_three]

theorem originalTuringScalar_affine_upper {T : ℝ} (hT : 1 ≤ T) :
    originalTuringScalarConstant / Real.pi + originalTuringScalarSlope * Real.log T <
      (171 / 100 : ℝ) + 57 / 500 * Real.log T := by
  have h := mul_le_mul_of_nonneg_right originalTuringScalarSlope_upper.le (Real.log_nonneg hT)
  linarith [originalTuringScalarConstant_div_pi_upper]

#print axioms original_reference_gamma_log_identity
#print axioms originalTuringScalarConstant_div_pi_upper
#print axioms originalTuringScalarSlope_upper
#print axioms originalTuringScalar_affine_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
