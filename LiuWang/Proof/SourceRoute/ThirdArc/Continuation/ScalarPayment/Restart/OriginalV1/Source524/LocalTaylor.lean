import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Expression

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

theorem exp_nat_add_upper (n m : ℕ) {u b : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hm : 0 < m)
    (hb : (2.7182818286 : ℝ) ^ n *
      ((∑ i ∈ Finset.range m, u ^ i / i.factorial) + u ^ m * (m + 1) / (m.factorial * m)) ≤ b) :
    Real.exp (n + u) ≤ b := by
  have hn := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n
  rw [← Real.exp_nat_mul, mul_one] at hn
  have h := mul_le_mul hn (Real.exp_bound' hu hu1 hm)
    (Real.exp_pos u).le (by positivity)
  rw [← Real.exp_add] at h
  exact h.trans hb

theorem exp_nat_add_lower (n m : ℕ) {u b : ℝ} (hu : 0 ≤ u)
    (hb : b ≤ (2.7182818283 : ℝ) ^ n * (∑ i ∈ Finset.range m, u ^ i / i.factorial)) :
    b ≤ Real.exp (n + u) := by
  have hn := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le n
  rw [← Real.exp_nat_mul, mul_one] at hn
  have hs := Real.sum_le_exp_of_nonneg hu m
  have h := mul_le_mul hn hs (Finset.sum_nonneg fun i _ => by positivity) (Real.exp_pos _).le
  rw [← Real.exp_add] at h
  exact hb.trans h

theorem log_3100_precise :
    (8.03915738 : ℝ) ≤ Real.log 3100 ∧ Real.log 3100 ≤ (8.03915740 : ℝ) := by
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3100)).mpr
    have h := exp_nat_add_upper 8 7 (u := 0.03915738) (b := 3100)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
    norm_num at h ⊢
    exact h
  · apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3100)).mpr
    have h := exp_nat_add_lower 8 7 (u := 0.03915740) (b := 3100)
      (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
    norm_num at h ⊢
    exact h

theorem log_48_precise :
    (3.8760837 : ℝ) ≤ Real.log (6 * Real.log 3100) ∧
      Real.log (6 * Real.log 3100) ≤ (3.8760838 : ℝ) := by
  have hs := log_3100_precise
  have hs0 : 0 < 6 * Real.log (3100 : ℝ) := by linarith [hs.1]
  constructor
  · apply (Real.le_log_iff_exp_le hs0).mpr
    have h := exp_nat_add_upper 3 13 (u := 0.8760837) (b := 48.23494428)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
    norm_num at h
    linarith only [h, hs.1]
  · apply (Real.log_le_iff_le_exp hs0).mpr
    have h := exp_nat_add_lower 3 13 (u := 0.8760838) (b := 48.2349444)
      (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial_succ])
    norm_num at h
    linarith only [h, hs.2]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
