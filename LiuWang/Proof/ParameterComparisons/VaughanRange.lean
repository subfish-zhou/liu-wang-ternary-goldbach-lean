import LiuWang.Proof.ParameterComparisons.VaughanRangeHelpers.Scales

/-!
# 原文末页的完整远次弧标量范围

对真实参数 `sourceP1 N ≤ q ≤ sourceQ N`，同时控制随 `q` 变化的两项，
再支付与 `q` 无关的误差。这里不涉及指数和 `S`，也不假设或宣称
Proposition 6.1 已获证明。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ParameterComparisons

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

theorem vaughan_variable_pair_le {N : ℕ} {q : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ q) (hqU : q ≤ sourceQ N) :
    (0.28 : ℝ) * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤
      (0.29 : ℝ) * (N : ℝ) / sourceL N := by
  have hL := sourceL_pos hN
  have hNp := natCast_pos_of_exp_le hN
  have hqp := (sourceP1_pos hN).trans_le hqL
  have hH := Real.rpow_pos_of_pos hNp ((1 : ℝ) / 2)
  have hA := Real.rpow_pos_of_pos hL ((13 : ℝ) / 2)
  have hqhalf := Real.rpow_pos_of_pos hqp ((1 : ℝ) / 2)
  have hNhalf : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast hNp.le]
    norm_num
  have hsplit : sourceL N ^ ((13 : ℝ) / 2) =
      sourceL N ^ ((7 : ℝ) / 2) * sourceL N ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (sourceL N) 3, ← Real.rpow_add hL]
    norm_num
  have hcoeff : sourceL N ^ ((13 : ℝ) / 2) =
      sourceL N ^ ((5 : ℝ) / 2) * sourceL N ^ (3 : ℕ) * sourceL N := by
    rw [hsplit]
    have he : sourceL N ^ ((7 : ℝ) / 2) =
        sourceL N ^ ((5 : ℝ) / 2) * sourceL N := by
      rw [← Real.rpow_add_one hL.ne']
      norm_num
    rw [he]
    ring
  have hleft : sourceL N ^ (3 : ℕ) ≤ q ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (sourceP1_pos hN).le hqL
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    unfold sourceP1 at h
    rw [← Real.rpow_natCast_mul hL.le] at h
    norm_num at h
    exact h
  have hright : q ^ ((1 : ℝ) / 2) ≤
      (N : ℝ) ^ ((1 : ℝ) / 2) / sourceL N ^ ((7 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow hqp.le hqU (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [sourceQ_eq_div, Real.div_rpow hNp.le (pow_nonneg hL.le _),
      ← Real.rpow_natCast_mul hL.le] at h
    norm_num at h
    exact h
  let R := sourceL N ^ ((13 : ℝ) / 2) / (N : ℝ) ^ ((1 : ℝ) / 2)
  let t := q ^ ((1 : ℝ) / 2) / sourceL N ^ (3 : ℕ)
  have hR : 0 < R := div_pos hA hH
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (pow_pos hL 3)).2
    simpa using hleft
  have htu : t ≤ 1 / R := by
    dsimp [t, R]
    rw [one_div_div, hsplit, ← div_div]
    exact div_le_div_of_nonneg_right hright (pow_nonneg hL.le _)
  have hpair := vaughan_normalized_pair_le hR (sourceL_thirteen_halves_ratio_le hN) ht htu
  have hfirst :
      (0.28 : ℝ) * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) =
        ((N : ℝ) / sourceL N) * (0.28 / t) := by
    rw [show (-1 : ℝ) / 2 = -(1 / 2) by norm_num, Real.rpow_neg hqp.le]
    dsimp [t]
    field_simp
  have hthird :
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) =
        ((N : ℝ) / sourceL N) * (0.09 * R * t) := by
    dsimp [R, t]
    rw [hcoeff]
    field_simp
    nlinarith only [hNhalf]
  calc
    _ = ((N : ℝ) / sourceL N) * (0.28 / t + 0.09 * R * t) := by
      rw [hfirst, hthird, mul_add]
    _ ≤ ((N : ℝ) / sourceL N) * 0.29 :=
      mul_le_mul_of_nonneg_left hpair (div_pos hNp hL).le
    _ = (0.29 : ℝ) * (N : ℝ) / sourceL N := by ring

/-- 原文的三个实幂项，在整个闭区间上的较强预算。 -/
theorem vaughan_scalar_range_margin {N : ℕ} {q : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ q) (hqU : q ≤ sourceQ N) :
    (0.28 : ℝ) * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤
      (0.294 : ℝ) * (N : ℝ) / sourceL N := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hp := vaughan_variable_pair_le h2000 hqL hqU
  have hm := vaughan_middle_term_le h2000
  have he : (0.294 : ℝ) * (N : ℝ) / sourceL N =
      (0.29 : ℝ) * (N : ℝ) / sourceL N +
        (0.004 : ℝ) * (N : ℝ) / sourceL N := by ring
  rw [he]
  linarith

/-- 174 页、文本 2174--2181 行的字面标量比较；不声称指数和估计。 -/
theorem vaughan_scalar_range {N : ℕ} {q : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ q) (hqU : q ≤ sourceQ N) :
    (0.28 : ℝ) * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤
      (0.3 : ℝ) * (N : ℝ) / sourceL N := by
  apply (vaughan_scalar_range_margin hN hqL hqU).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg N))
    (sourceL_pos (exp_2000_le_of_exp_3100_le hN)).le

/-- 自然模数的直接专门化，不引入额外的正性或标量估计前提。 -/
theorem vaughan_scalar_range_nat {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    (0.28 : ℝ) * (N : ℝ) * (q : ℝ) ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * (q : ℝ) ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) ≤
      (0.3 : ℝ) * (N : ℝ) / sourceL N :=
  vaughan_scalar_range hN hqL hqU

end LiuWang.Proof.ParameterComparisons
