import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.RealDirichletBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem rpow_three_halves_eq_sqrt (n : ℕ) :
    (n : ℝ) ^ (-3 / 2 : ℝ) = 1 / ((n : ℝ) * Real.sqrt n) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [show (-3 / 2 : ℝ) = -1 / 2 - 1 by norm_num, Real.rpow_sub_one hn',
      neg_div, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
    ring

theorem log_nat_upper_certificate (n k : ℕ) (hn : 0 < n) (hk : 2 ^ k ≤ n)
    (R : ℝ)
    (hR : (k : ℝ) * (6931471808 / 10000000000) +
      2 * ((∑ i ∈ Finset.range 8,
        (((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k)) ^ (2 * i + 1) / (2 * i + 1)) +
        (((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k)) ^ 17 /
          (1 - (((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k)) ^ 2)) ≤ R) :
    Real.log n ≤ R := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (2 : ℝ) ^ k ≤ n := by exact_mod_cast hk
  have hd : 0 < (n : ℝ) + 2 ^ k := by positivity
  have hr0 : 0 ≤ ((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k) := by positivity
  have hr1 : ((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k) < 1 := by
    rw [div_lt_one hd]
    linarith [show (0 : ℝ) < 2 ^ k by positivity]
  have h := Real.log_div_le_sum_range_add hr0 hr1 8
  have he : (1 + ((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k)) /
      (1 - ((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k)) = (n : ℝ) / 2 ^ k := by
    field_simp
    ring
  rw [he, Real.log_div hn'.ne' (by positivity), Real.log_pow] at h
  have hlog := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  norm_num only [show (2 * 8 + 1 : ℕ) = 17 by norm_num] at h
  linarith

theorem threeHalves_term_certificate (n : ℕ) (hn : 0 < n)
    (l r R L U : ℝ) (hl : 0 < l) (hr : 0 ≤ r)
    (hl2 : l ^ 2 ≤ n) (hr2 : (n : ℝ) ≤ r ^ 2)
    (hlog : Real.log n ≤ R) (hL : L ≤ 1 / ((n : ℝ) * r))
    (hU : R / ((n : ℝ) * l) ≤ U) :
    L ≤ (n : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm n ≤ U := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hls : l ≤ Real.sqrt n := by nlinarith [Real.sq_sqrt hn'.le]
  have hsr : Real.sqrt n ≤ r := by nlinarith [Real.sq_sqrt hn'.le]
  have hR : 0 ≤ R := (Real.log_natCast_nonneg n).trans hlog
  rw [rpow_three_halves_eq_sqrt]
  constructor
  · exact hL.trans (one_div_le_one_div_of_le (mul_pos hn' hs)
      (mul_le_mul_of_nonneg_left hsr hn'.le))
  · unfold logPowerTerm
    rw [rpow_three_halves_eq_sqrt, mul_one_div]
    exact ((div_le_div_of_nonneg_right hlog (mul_nonneg hn'.le hs.le)).trans
      (div_le_div_of_nonneg_left hR (mul_pos hn' hl)
        (mul_le_mul_of_nonneg_left hls hn'.le))).trans hU

#print axioms log_nat_upper_certificate
#print axioms threeHalves_term_certificate

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
