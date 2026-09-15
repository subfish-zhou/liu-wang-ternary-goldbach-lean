import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.RightMean

/-! A legal-window obstruction to paying Chen's all-height right-line input
by scalar comparison with the existing majorant. This is not a lower bound
for the actual detector mean. -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Density

theorem right_mean_witness_in_source_domain :
    10000 * Real.log 6 ≤ Real.exp 10 := by
  have h6 : Real.log 6 ≤ 2 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he 10
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

theorem moving_sharp_majorant_exceeds_chen14_at_legal_window :
    (67.929 + 0.0003 * 10000) * Real.log (Real.exp 10) ^ (5 : ℕ) <
      (6 * (Real.exp 10 * 10000) / (Real.exp 10 - 1)) *
          Real.log (Real.exp 10) ^ (2 : ℕ) +
        132 * Real.log (Real.exp 10) ^ (4 : ℕ) := by
  have he : 1 < Real.exp (10 : ℝ) :=
    Real.one_lt_exp_iff.mpr (by norm_num)
  have hf : (60000 : ℝ) < 6 * (Real.exp 10 * 10000) / (Real.exp 10 - 1) := by
    apply (lt_div_iff₀ (by linarith : 0 < Real.exp 10 - 1)).mpr
    linarith
  rw [Real.log_exp]
  norm_num at *
  linarith

#print axioms right_mean_witness_in_source_domain
#print axioms moving_sharp_majorant_exceeds_chen14_at_legal_window

end LiuWang.Proof.Campaign20260915.Density
