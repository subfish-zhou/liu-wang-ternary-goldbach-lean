import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.TailIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

theorem linearPrefactor_le : linearPrefactor ≤ 1.7376 := by
  have hroot (x : ℝ) (hx : 0 ≤ x) (s : ℝ) :
      (x ^ s) ^ 3 = x ^ (s * 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hc : linearPrefactor ^ 3 =
      27 * (3.36 / (5 * Real.pi)) * (2.994006 / Real.pi) ^ 2 := by
    unfold linearPrefactor
    rw [mul_pow, mul_pow, hroot _ (by positivity), hroot _ (by positivity)]
    norm_num
  have hp : (3.141592 : ℝ) ≤ Real.pi := Real.pi_gt_d6.le
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3.36)
    (by norm_num : (0 : ℝ) < 5 * 3.141592) (mul_le_mul_of_nonneg_left hp (by norm_num))
  have ha := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2.994006)
    (by norm_num : (0 : ℝ) < 3.141592) hp
  have hcube : linearPrefactor ^ 3 ≤ (1.7376 : ℝ) ^ 3 := by
    rw [hc]
    calc
      _ ≤ 27 * (3.36 / (5 * 3.141592)) * (2.994006 / 3.141592) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num))
          (pow_le_pow_left₀ (by positivity) ha 2) (by positivity) (by norm_num)
      _ ≤ _ := by norm_num
  exact (pow_le_pow_iff_left₀ (by unfold linearPrefactor; positivity)
    (by norm_num) (by decide : 3 ≠ 0)).mp hcube

theorem high_tail_div_P_le {P : ℝ} (hP : 10000000000 ≤ P) :
    nu P ^ 2 * (P ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) / P ≤ 1 / 5280000 := by
  have hP0 : 0 < P := by linarith
  have he : (P ^ (0.080521 : ℝ)) ^ 2 = P ^ (2 * 0.080521 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
    norm_num
  calc
    _ ≤ nu P ^ 2 * P ^ (1 / 6 : ℝ) / P := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_self _
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) _)) (sq_nonneg _)) hP0.le
    _ ≤ (P ^ (0.080521 : ℝ)) ^ 2 * P ^ (1 / 6 : ℝ) / P := by
      apply div_le_div_of_nonneg_right _ hP0.le
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (nu_pos (by linarith)).le (nu_le_source_power hP) 2)
        (Real.rpow_nonneg hP0.le _)
    _ = P ^ (1 / 6 - 1 + 2 * 0.080521 : ℝ) := by
      rw [he, ← Real.rpow_add hP0,
        show (1 / 6 - 1 + 2 * 0.080521 : ℝ) = (2 * 0.080521 + 1 / 6) - 1 by ring,
        Real.rpow_sub hP0, Real.rpow_one]
    _ ≤ (10000000000 : ℝ) ^ (1 / 6 - 1 + 2 * 0.080521 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hP (by norm_num)
    _ ≤ _ := source_power_tail_endpoint

theorem source423_scalar {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    linearPrefactor *
      (0.0194 * 3.2868 + (5 * 0.0126 / sourceL N ^ 3) *
        (8864 + 6 * nu (sourceP N) ^ 2 *
          ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)))) ≤ 0.1108 := by
  have hP := sourceP_ge_ten_billion hN
  have hP0 : 0 < sourceP N := by linarith
  have hsmall := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8864)
    (by norm_num : (0 : ℝ) < 10000000000) hP
  have htail := high_tail_div_P_le hP
  have hinner :
      0.0194 * 3.2868 + (5 * 0.0126 / sourceL N ^ 3) *
        (8864 + 6 * nu (sourceP N) ^ 2 *
          ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ))) ≤
        0.0194 * 3.2868 + 0.063 * (8864 / 10000000000 + 6 / 5280000) := by
    change 0.0194 * 3.2868 + (5 * 0.0126 / sourceP N) * _ ≤ _
    have he : (5 * 0.0126 / sourceP N) *
        (8864 + 6 * nu (sourceP N) ^ 2 *
          ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ))) =
        0.063 * (8864 / sourceP N + 6 *
          (nu (sourceP N) ^ 2 * ((sourceP N) ^ (1 / 6 : ℝ) -
            (10 : ℝ) ^ (5 / 3 : ℝ)) / sourceP N)) := by ring
    rw [he]
    linarith
  calc
    _ ≤ linearPrefactor * (0.0194 * 3.2868 + 0.063 * (8864 / 10000000000 + 6 / 5280000)) :=
      mul_le_mul_of_nonneg_left hinner (by unfold linearPrefactor; positivity)
    _ ≤ 1.7376 * (0.0194 * 3.2868 + 0.063 * (8864 / 10000000000 + 6 / 5280000)) :=
      mul_le_mul_of_nonneg_right linearPrefactor_le (by norm_num)
    _ ≤ _ := by norm_num

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
