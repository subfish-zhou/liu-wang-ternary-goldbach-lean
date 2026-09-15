import LiuWang.Proof.VaughanTypeII.Dyadic

/-! 原式 (6.22) 所需的两个 `2 + √2` 有限几何级数界。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeII

open Finset Interfaces Parameters ArithmeticBounds
open scoped BigOperators

theorem sum_sqrt_dyadic_le_next (N k : ℕ) :
    (∑ j ∈ range k, Real.sqrt (dyadicScale N j)) ≤
      (1 + Real.sqrt 2) * Real.sqrt (dyadicScale N k) := by
  induction k with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ k ih =>
    rw [sum_range_succ, dyadicScale_succ, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ (1 + Real.sqrt 2) * Real.sqrt (dyadicScale N k) +
          Real.sqrt (dyadicScale N k) := add_le_add ih le_rfl
      _ = _ := by ring_nf; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

theorem dyadicScale_count_lt_twice_upper {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    dyadicScale N (dyadicCount N) < 2 * ((N : ℝ) / sourceVaughanU N) := by
  have hk := dyadicCount_pos hN
  have hlast := dyadicScale_lt_upper hN (j := dyadicCount N - 1) (by omega)
  have he : dyadicScale N (dyadicCount N) =
      2 * dyadicScale N (dyadicCount N - 1) := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ dyadicCount N by omega)] using
      dyadicScale_succ N (dyadicCount N - 1)
  rw [he]
  linarith

theorem sum_sqrt_dyadic_le {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∑ j ∈ range (dyadicCount N), Real.sqrt (dyadicScale N j)) ≤
      (2 + Real.sqrt 2) * Real.sqrt ((N : ℝ) / sourceVaughanU N) := by
  calc
    _ ≤ (1 + Real.sqrt 2) * Real.sqrt (dyadicScale N (dyadicCount N)) :=
      sum_sqrt_dyadic_le_next N _
    _ ≤ (1 + Real.sqrt 2) * Real.sqrt (2 * ((N : ℝ) / sourceVaughanU N)) :=
      mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (dyadicScale_count_lt_twice_upper hN).le) (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem sum_inv_sqrt_dyadic_add_tail {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (k : ℕ) :
    (∑ j ∈ range k, 1 / Real.sqrt (dyadicScale N j)) +
        (2 + Real.sqrt 2) / Real.sqrt (dyadicScale N k) =
      (2 + Real.sqrt 2) / Real.sqrt (sourceVaughanV N) := by
  induction k with
  | zero => simp [dyadicScale_zero]
  | succ k ih =>
    rw [sum_range_succ, dyadicScale_succ, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      add_assoc]
    have hs := Real.sqrt_pos.mpr (dyadicScale_pos hN k)
    have htwo := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    have he : 1 / Real.sqrt (dyadicScale N k) +
        (2 + Real.sqrt 2) / (Real.sqrt 2 * Real.sqrt (dyadicScale N k)) =
          (2 + Real.sqrt 2) / Real.sqrt (dyadicScale N k) := by
      field_simp
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rwa [he]

theorem sum_inv_sqrt_dyadic_le {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∑ j ∈ range (dyadicCount N), 1 / Real.sqrt (dyadicScale N j)) ≤
      (2 + Real.sqrt 2) / Real.sqrt (sourceVaughanV N) := by
  have he := sum_inv_sqrt_dyadic_add_tail hN (dyadicCount N)
  have ht : 0 ≤ (2 + Real.sqrt 2) / Real.sqrt (dyadicScale N (dyadicCount N)) := by
    positivity
  linarith

theorem dyadicCount_lt_sourceL_bound {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (dyadicCount N : ℝ) <
      1 + (sourceL N + 3 * Real.log (sourceL N)) / (5 * Real.log 2) := by
  have hlog : Real.log ((N : ℝ) / (sourceVaughanU N * sourceVaughanV N)) =
      (sourceL N + 3 * Real.log (sourceL N)) / 5 := by
    rw [Real.log_div (natCast_pos_of_exp_le hN).ne'
      (mul_pos (sourceVaughanU_pos hN) (sourceVaughanV_pos hN)).ne',
      Real.log_mul (sourceVaughanU_pos hN).ne' (sourceVaughanV_pos hN).ne',
      log_sourceVaughanU hN, log_sourceVaughanV hN]
    unfold sourceL
    ring
  have h := dyadicCount_lt_log_bound hN
  rw [hlog] at h
  convert h using 1
  ring

end LiuWang.Proof.VaughanTypeII
