import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Expression

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

theorem log_thousand_lower : (6.9 : ℝ) ≤ Real.log 1000 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 1000)).mpr
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le
    (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 69
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat, mul_one] at h
  have he : Real.exp 6.9 ^ (10 : ℕ) ≤ (1000 : ℝ) ^ 10 := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat, show (10 : ℝ) * 6.9 = 69 by norm_num]
    exact h.trans (by norm_num)
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num)
    (by norm_num : (10 : ℕ) ≠ 0)).mp he

theorem original_low_coefficient : lowCoefficient (59 / 60) ≤ (1.01581 : ℝ) := by
  have hp : (0.001 : ℝ) ^ (59 / 60 : ℝ) =
      0.001 * Real.exp (Real.log 1000 / 60) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 0.001)]
    have hl : Real.log (0.001 : ℝ) = -Real.log 1000 := by
      rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hl, show -Real.log (1000 : ℝ) * (59 / 60) =
      -Real.log 1000 + Real.log 1000 / 60 by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 1000)]
    norm_num
  have he := Real.exp_le_exp.mpr
    (show (0.115 : ℝ) ≤ Real.log 1000 / 60 by linarith [log_thousand_lower])
  have hq := (Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.115)).trans he
  unfold lowCoefficient
  rw [hp]
  norm_num at hq ⊢
  linarith

theorem original_power_constant : (10 : ℝ) ^ (4 / 15 : ℝ) ≤ 1.84786 := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num)
    (by norm_num : (15 : ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

theorem original_decimal_coefficients :
    lowCoefficient (59 / 60) ≤ (1.0159 : ℝ) ∧
      lowCoefficient (59 / 60) * (10 : ℝ) ^ (4 / 15 : ℝ) ≤ 1.8771 := by
  refine ⟨original_low_coefficient.trans (by norm_num), ?_⟩
  have h := mul_le_mul original_low_coefficient original_power_constant
    (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  exact h.trans (by norm_num)

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
