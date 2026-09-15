import LiuWang.Proof.ChebyshevBound.HighHeight.ZeroTail

/-! # 原 log x≥3100 域的六高度分层数值证书，不使用数值采样。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.ChebyshevBound.HighHeight

theorem exp_lower_nat_add (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (2718 / 1000 : ℝ) ^ n * (1 + r + r ^ 2 / 2) ≤ Real.exp ((n : ℝ) + r) := by
  have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718 / 1000) he n
  have hrb := Real.sum_le_exp_of_nonneg hr 3
  norm_num [Finset.sum_range_succ] at hrb
  rw [Real.exp_add]
  have hn : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hn]
  exact mul_le_mul hp (by linarith) (by positivity) (by positivity)

theorem exp_four_ge_fifty_four : (54 : ℝ) ≤ Real.exp 4 := by
  have h := exp_lower_nat_add 4 (r := 0) le_rfl
  norm_num at h
  linarith

theorem log_exp_height_le {u : ℝ} (hu : 4 ≤ u) :
    Real.log (Real.exp u + 2) ≤ u + 1 / 10 := by
  have hexp : 54 ≤ Real.exp u := exp_four_ge_fifty_four.trans (Real.exp_le_exp.mpr hu)
  apply (Real.log_le_iff_le_exp (by positivity)).2
  rw [Real.exp_add]
  have h := Real.add_one_le_exp (1 / 10)
  nlinarith

theorem exp_neg_budget {a c r : ℝ} (n : ℕ) (hr : 0 ≤ r) (hc : 0 < c)
    (ha : (n : ℝ) + r ≤ a)
    (hnum : c ≤ (2718 / 1000 : ℝ) ^ n * (1 + r + r ^ 2 / 2)) :
    Real.exp (-a) ≤ 1 / c := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hc
    ((hnum.trans (exp_lower_nat_add n hr)).trans (Real.exp_le_exp.mpr ha))

theorem zero_exp_budget_four :
    Real.exp (-(3100 / (20 * (4 + 21 / 10 : ℝ)))) ≤ 1 / 10000000000 := by
  exact exp_neg_budget 24 (r := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem zero_exp_budget_eight :
    Real.exp (-(3100 / (20 * (8 + 21 / 10 : ℝ)))) ≤ 1 / 4000000 := by
  exact exp_neg_budget 15 (r := 3 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem zero_exp_budget_twelve :
    Real.exp (-(3100 / (20 * (12 + 21 / 10 : ℝ)))) ≤ 1 / 50000 := by
  exact exp_neg_budget 10 (r := 9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem zero_exp_budget_sixteen :
    Real.exp (-(3100 / (20 * (16 + 21 / 10 : ℝ)))) ≤ 1 / 5000 := by
  exact exp_neg_budget 8 (r := 11 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem zero_exp_budget_twenty :
    Real.exp (-(3100 / (20 * (20 + 21 / 10 : ℝ)))) ≤ 1 / 1000 := by
  exact exp_neg_budget 7 (r := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem xiHeightTail_exp_sum_le (k : ℕ) (hk : 1 ≤ k) :
    (∑' p, xiHeightTail (Real.exp (4 * (k : ℝ))) p) ≤ (8 * (k : ℝ) + 2) / 54 ^ k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he4 : 54 ≤ Real.exp (4 * (k : ℝ)) :=
    exp_four_ge_fifty_four.trans (Real.exp_le_exp.mpr (by linarith))
  have hpow : (54 : ℝ) ^ k ≤ Real.exp (4 * (k : ℝ)) := by
    rw [mul_comm 4, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) exp_four_ge_fifty_four k
  have h := xiHeightTail_sum_le (T := Real.exp (4 * (k : ℝ))) (by linarith)
  rw [Real.log_exp] at h
  calc
    _ ≤ (8 * (k : ℝ) + 2) / Real.exp (4 * (k : ℝ)) := by
      convert h using 1; ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow

end LiuWang.Proof.ChebyshevBound.HighHeight
