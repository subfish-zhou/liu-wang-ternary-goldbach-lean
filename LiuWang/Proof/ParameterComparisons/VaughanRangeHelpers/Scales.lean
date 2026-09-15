import LiuWang.Proof.ParameterComparisons.VaughanScalar

/-! 远次弧标量比较所需的实幂尺度；参数沿用原始接口定义。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ParameterComparisons

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

theorem sourceL_eighth_lt_natCast_half {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    sourceL N ^ (8 : ℕ) < (N : ℝ) ^ ((1 : ℝ) / 2) := by
  have hL := sourceL_pos hN
  have h16 := pow_sixteen_lt_exp (sourceL_ge_2000 hN)
  rw [exp_sourceL (nat_pos_of_exp_le hN)] at h16
  have hs : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast (natCast_pos_of_exp_le hN).le]
    norm_num
  have hsq : (sourceL N ^ (8 : ℕ)) ^ (2 : ℕ) <
      ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
    rw [hs, ← pow_mul]
    exact h16
  nlinarith [pow_nonneg hL.le 8,
    Real.rpow_pos_of_pos (natCast_pos_of_exp_le hN) ((1 : ℝ) / 2)]

theorem sourceL_thirteen_halves_ratio_le {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    sourceL N ^ ((13 : ℝ) / 2) / (N : ℝ) ^ ((1 : ℝ) / 2) ≤
      (1 / 100 : ℝ) := by
  have hL := sourceL_pos hN
  have hpow : sourceL N ^ ((13 : ℝ) / 2) ≤ sourceL N ^ (7 : ℕ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (one_le_sourceL hN)
      (show (13 : ℝ) / 2 ≤ 7 by norm_num)
  have hsmall : 100 * sourceL N ^ ((13 : ℝ) / 2) <
      (N : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      100 * sourceL N ^ ((13 : ℝ) / 2) ≤ 100 * sourceL N ^ (7 : ℕ) :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ sourceL N * sourceL N ^ (7 : ℕ) :=
        mul_le_mul_of_nonneg_right (by linarith [sourceL_ge_2000 hN])
          (pow_nonneg hL.le _)
      _ = sourceL N ^ (8 : ℕ) := by ring
      _ < (N : ℝ) ^ ((1 : ℝ) / 2) := sourceL_eighth_lt_natCast_half hN
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (natCast_pos_of_exp_le hN) _)).2
  linarith

theorem sourceL_twelve_fifths_small {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    1000 * sourceL N ^ ((12 : ℝ) / 5) < (N : ℝ) ^ ((1 : ℝ) / 5) := by
  have hp : sourceL N ^ ((12 : ℝ) / 5) ≤ sourceL N ^ (3 : ℕ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (one_le_sourceL hN)
      (show (12 : ℝ) / 5 ≤ 3 by norm_num)
  have he : (N : ℝ) ^ ((1 : ℝ) / 5) = Real.exp (sourceL N / 5) := by
    rw [Real.rpow_def_of_pos (natCast_pos_of_exp_le hN)]
    congr 1
    unfold sourceL
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans_lt
    (thousand_mul_cube_lt_exp_fifth (sourceL_ge_2000 hN))

theorem vaughan_middle_term_le {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) ≤
      (0.004 : ℝ) * (N : ℝ) / sourceL N := by
  have hL := sourceL_pos hN
  have hNp := natCast_pos_of_exp_le hN
  have h := sourceL_twelve_fifths_small hN
  have hNpow : (N : ℝ) ^ ((4 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 5) =
      (N : ℝ) := by
    rw [← Real.rpow_add hNp]
    norm_num
  have hLpow : sourceL N ^ ((7 : ℝ) / 5) * sourceL N =
      sourceL N ^ ((12 : ℝ) / 5) := by
    rw [← Real.rpow_add_one hL.ne']
    norm_num
  apply (le_div_iff₀ hL).2
  have hm := mul_le_mul_of_nonneg_left
    (show 4 * sourceL N ^ ((12 : ℝ) / 5) ≤
      (0.004 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 5) by linarith)
    (Real.rpow_pos_of_pos hNp ((4 : ℝ) / 5)).le
  calc
    4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) * sourceL N =
        (N : ℝ) ^ ((4 : ℝ) / 5) * (4 * sourceL N ^ ((12 : ℝ) / 5)) := by
      rw [← hLpow]
      ring
    _ ≤ (N : ℝ) ^ ((4 : ℝ) / 5) *
        ((0.004 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 5)) := hm
    _ = (0.004 : ℝ) * (N : ℝ) := by
      rw [mul_left_comm, hNpow]

theorem vaughan_normalized_pair_le {R t : ℝ}
    (hR : 0 < R) (hRsmall : R ≤ 1 / 100) (ht : 1 ≤ t) (htu : t ≤ 1 / R) :
    (0.28 : ℝ) / t + 0.09 * R * t ≤ 0.29 := by
  apply inverse_linear_le_of_endpoints (l := 1) (u := 1 / R)
    (by positivity) (by norm_num) ht htu
  · norm_num
    linarith
  · have he : (0.28 : ℝ) / (1 / R) + 0.09 * R * (1 / R) =
        0.28 * R + 0.09 := by
      field_simp
    rw [he]
    linarith

end LiuWang.Proof.ParameterComparisons
