import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.Third
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.Domain

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases

theorem exp_two_lower : (7 : ℝ) ≤ Real.exp 2 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
    ((by norm_num : (2.7 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 2
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

theorem exp_three_lower : (19 : ℝ) ≤ Real.exp 3 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
    ((by norm_num : (2.7 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 3
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

theorem weighted_exp_compare {a b t k C D : ℝ}
    (hgap : k ≤ (a - b) * t) (hD : 0 ≤ D) (hc : C ≤ D * Real.exp k) :
    C * Real.exp (-a * t) ≤ D * Real.exp (-b * t) := by
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap) hD
  have hh := mul_le_mul_of_nonneg_right (hc.trans he) (Real.exp_pos (-a * t)).le
  rw [mul_assoc, ← Real.exp_add, show (a - b) * t + -a * t = -b * t by ring] at hh
  exact hh

theorem negative_exp_antitone {a b t : ℝ} (hab : a ≤ b) (ht : 0 ≤ t) :
    Real.exp (-b * t) ≤ Real.exp (-a * t) :=
  Real.exp_le_exp.mpr (by nlinarith)

theorem second_leading_absorption {t : ℝ} (ht : 20 ≤ t) :
    2 * Real.exp (-0.12 * t) + 11 * Real.exp (-0.2743 * t) ≤
      2 * Real.exp (-(1 / c1) * t) := by
  have hc : (1 / c1 : ℝ) ≤ 0.104 := by norm_num [c1]
  have h1 := weighted_exp_compare (a := 0.2743) (b := 0.12) (t := t) (k := 3)
    (C := 11) (D := 0.6) (by nlinarith) (by norm_num)
    (by linarith [exp_three_lower])
  have h2 := weighted_exp_compare (a := 0.12) (b := 1 / c1) (t := t) (k := 0.32)
    (C := 2.6) (D := 2) (by nlinarith) (by norm_num)
    (by linarith [Real.add_one_le_exp (0.32 : ℝ)])
  linarith

theorem third_leading_absorption {t : ℝ} (ht : 20 ≤ t) :
    2 * Real.exp (-0.15 * t) + 2 * Real.exp (-0.2067 * t) +
      9 * Real.exp (-0.26213 * t) ≤ 2 * Real.exp (-(1 / c1) * t) := by
  have hc : (1 / c1 : ℝ) ≤ 0.104 := by norm_num [c1]
  have h1 := weighted_exp_compare (a := 0.15) (b := 1 / c1) (t := t) (k := 0.8)
    (C := 2) (D := 1.2) (by nlinarith) (by norm_num)
    (by linarith [Real.add_one_le_exp (0.8 : ℝ)])
  have h2 := weighted_exp_compare (a := 0.2067) (b := 1 / c1) (t := t) (k := 2)
    (C := 2) (D := 0.3) (by nlinarith) (by norm_num)
    (by linarith [exp_two_lower])
  have h3 := weighted_exp_compare (a := 0.26213) (b := 1 / c1) (t := t) (k := 3)
    (C := 9) (D := 0.5) (by nlinarith) (by norm_num)
    (by linarith [exp_three_lower])
  linarith

theorem profile36_le_profile35 {L s : ℝ} (ht : 20 ≤ L / s) :
    profile36 L s ≤ profile35 L s := by
  have ht0 : 0 ≤ L / s := by linarith
  have h1 := negative_exp_antitone (by norm_num : (0.2743 : ℝ) ≤ 0.28) ht0
  have h2 := negative_exp_antitone (by norm_num : (0.2743 : ℝ) ≤ 0.3) ht0
  have h3 := negative_exp_antitone (by norm_num : (0.2743 : ℝ) ≤ 0.31) ht0
  have h4 := negative_exp_antitone (by norm_num : (0.2743 : ℝ) ≤ 0.32) ht0
  have hp := second_leading_absorption ht
  have he (a : ℝ) : -a * L / s = -a * (L / s) := by ring
  have hf : -L / (c1 * s) = -(1 / c1) * (L / s) := by ring
  unfold profile36 profile35
  simp only [he, hf]
  linarith [Real.exp_pos (-0.3221 * (L / s))]

theorem third_le_profile35 {L s : ℝ} (hL : 0 < L) (hs : 0 < s)
    (ht : 20 ≤ L / s) :
    thirdTableEnvelope L s ≤ profile35 L s := by
  have ht0 : 0 ≤ L / s := by linarith
  have h1 := negative_exp_antitone (by norm_num : (0.26213 : ℝ) ≤ 0.27) ht0
  have h2 := negative_exp_antitone (by norm_num : (0.26213 : ℝ) ≤ 0.28) ht0
  have h3 := negative_exp_antitone (by norm_num : (0.26213 : ℝ) ≤ 0.3) ht0
  have h4 := negative_exp_antitone (by norm_num : (0.26213 : ℝ) ≤ 0.31) ht0
  have h5 := negative_exp_antitone (by norm_num : (0.26213 : ℝ) ≤ 0.32) ht0
  have hp := third_leading_absorption ht
  have he (a : ℝ) : -a * L / s = -a * (L / s) := by ring
  have hf : -L / (c1 * s) = -(1 / c1) * (L / s) := by ring
  rw [third_table_bridge hL hs]
  unfold profile35
  simp only [he, hf]
  linarith [Real.exp_pos (-0.3221 * (L / s))]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases
