import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.OrdinaryTransport

set_option autoImplicit false

noncomputable section

open Set
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem ordinary_delta_log {y : ℝ} (hy : 10000 ≤ y) :
    delta y * Real.log y = 2 / 3 := by
  have hL : 0 < Real.log y := lt_of_lt_of_le (by norm_num) (log_ge_nine hy)
  unfold delta
  field_simp

theorem ordinary_exp_eight_thirds : Real.exp (8 / 3) ≤ 15 := by
  have he1 : Real.exp 1 ≤ 11 / 4 :=
    le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he1 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he3 : Real.exp (8 / 3) ^ 3 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  by_contra h
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15) (le_of_lt (lt_of_not_ge h)) 3
  rw [he3] at hh
  norm_num at hh
  linarith

theorem ordinary_moving_power {y α : ℝ} (hy : 10000 ≤ y) :
    y ^ (4 * (1 - (α - delta y))) =
      y ^ (4 * (1 - α)) * Real.exp (8 / 3) := by
  have hd := ordinary_delta_log hy
  have hy0 : 0 < y := by linarith
  rw [Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hy0, ← Real.exp_add]
  congr 1
  nlinarith

theorem ordinary_mean_budget {y α : ℝ} (hy : 10000 ≤ y) :
    (1861 * y ^ (4 * (1 - (α - delta y))) *
      Real.log y ^ (6 * (α - delta y) - 1)) / (2 * Real.pi * delta y) ≤
        7000 * y ^ (4 * (1 - α)) * Real.log y ^ (6 * α - 6 * delta y) := by
  have hL := log_ge_nine hy
  have hL0 : 0 < Real.log y := by linarith
  have hd := (delta_bounds hy).1
  have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hden : 0 < 2 * Real.pi * delta y := by positivity
  have he := ordinary_exp_eight_thirds
  have hcoef : 1861 * Real.exp (8 / 3) * 3 / (4 * Real.pi) ≤ (7000 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
    nlinarith
  have hpow : Real.log y ^ (6 * (α - delta y) - 1) * Real.log y =
      Real.log y ^ (6 * α - 6 * delta y) := by
    calc
      _ = Real.log y ^ (6 * (α - delta y) - 1) * Real.log y ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = Real.log y ^ ((6 * (α - delta y) - 1) + 1) := (Real.rpow_add hL0 _ _).symm
      _ = _ := by congr 1; ring
  have hnorm :
      (1861 * y ^ (4 * (1 - (α - delta y))) *
        Real.log y ^ (6 * (α - delta y) - 1)) / (2 * Real.pi * delta y) =
      (1861 * Real.exp (8 / 3) * 3 / (4 * Real.pi)) *
        y ^ (4 * (1 - α)) * Real.log y ^ (6 * α - 6 * delta y) := by
    rw [ordinary_moving_power hy, ← hpow]
    apply (div_eq_iff hden.ne').mpr
    unfold delta
    field_simp
    ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg hL0.le _)

theorem ordinary_mean_source_budget {y α : ℝ} (hy : 10000 ≤ y) :
    (1861 * y ^ (4 * (1 - (α - delta y))) *
      Real.log y ^ (6 * (α - delta y) - 1)) / (2 * Real.pi * delta y) ≤
        7000 * y ^ (4 * (1 - α)) * Real.log y ^ (6 * α) := by
  have hL := log_ge_nine hy
  have hd := (delta_bounds hy).1
  apply (ordinary_mean_budget hy).trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Real.log y) (by linarith))
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
