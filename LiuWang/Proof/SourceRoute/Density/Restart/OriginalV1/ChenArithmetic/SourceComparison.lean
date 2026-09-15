import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.CriticalMean
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

theorem source_height_lower {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    17917.5 ≤ y := by
  have h6 : 1.79175 ≤ Real.log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  linarith

private theorem source_anchor_log :
    Real.log (17917.5 : ℝ) ≤ 9.794 := by
  have h18000 : Real.log (18000 : ℝ) ≤ 9.7982 := by
    rw [show (18000 : ℝ) = (2 ^ 4 * 3 ^ 2) * 5 ^ 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    simp only [Real.log_pow]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 17917.5 / 18000)
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  linarith

theorem sqrt_boundary_scalar {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    1.216 * Real.sqrt y + Real.log y + 2.4 ≤ 1.3071 * Real.sqrt y := by
  have hyb := source_height_lower hy
  have hy0 : 0 < y := by linarith
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hb0 : 0 < Real.sqrt (17917.5 : ℝ) := by positivity
  have hsb : (133.856 : ℝ) ≤ Real.sqrt 17917.5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17917.5)]
  have heb : Real.exp 2 ≤ (17917.5 : ℝ) := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)) 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hmono := Real.log_div_sqrt_antitoneOn heb (heb.trans hyb) hyb
  have hinv := one_div_le_one_div_of_le hb0 (Real.sqrt_le_sqrt hyb)
  have hb : (Real.log (17917.5 : ℝ) + 2.4) / Real.sqrt 17917.5 ≤ 0.0911 := by
    apply (div_le_iff₀ hb0).mpr
    linarith [source_anchor_log]
  have h : (Real.log y + 2.4) / Real.sqrt y ≤ 0.0911 := by
    rw [add_div] at hb ⊢
    have hi := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2.4)
    simp only [mul_one_div] at hi
    linarith
  have hf := (div_le_iff₀ hs0).mp h
  linarith

theorem harmonic_boundary_scalar {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    0.608 * Real.log y + 5.608 ≤ 1.19 * Real.log y := by
  have hl := (source_height_log_bounds hy).2
  linarith

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
