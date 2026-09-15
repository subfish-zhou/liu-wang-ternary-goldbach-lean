import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.OrdinaryJensen

set_option autoImplicit false

noncomputable section

open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem ordinary_argument_budget {y α : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y) /
      (2 * Real.pi * delta y) ≤ (405 / 8) * Real.log y ^ 3 + (27 / 8) * Real.log y := by
  have hd := (delta_bounds hy).1
  have hL := log_ge_nine hy
  have hr : 0 ≤ 2 - α + delta y := by linarith
  have hrmax : 2 - α + delta y ≤ 3 / 2 := by linarith
  let J := Real.log (2 * (1 + windowMajorant y (α - 3 * delta y / 2)) /
    (2 - 8 / (y - 1) ^ 2)) /
      Real.log ((2 - α + 3 * delta y / 2) / (2 - α + delta y))
  have hJ : J ≤ (45 / 2) * Real.log y ^ 2 := ordinary_jensen_budget hy hα hα1
  have he :
      argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y) /
        (2 * Real.pi * delta y) =
      ((2 - α + delta y) * (2 * J + 3)) / (2 * delta y) := by
    unfold argumentMajorant
    rw [show 2 - (2 - α + 3 * delta y / 2) = α - 3 * delta y / 2 by ring,
      show 2 - (α - delta y) = 2 - α + delta y by ring]
    change ((2 - α + delta y) * Real.pi * (2 * J + 3)) /
      (2 * Real.pi * delta y) = _
    field_simp
  rw [he]
  calc
    _ ≤ ((3 / 2) * (45 * Real.log y ^ 2 + 3)) / (2 * delta y) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (mul_le_mul_of_nonneg_left (show 2 * J + 3 ≤ 45 * Real.log y ^ 2 + 3 by linarith) hr).trans
      exact mul_le_mul_of_nonneg_right hrmax (by positivity)
    _ = _ := by
      unfold delta
      field_simp
      ring

theorem ordinary_pole_budget {y α : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) :
    (4 * Real.pi * (1 - (α - delta y))) / (2 * Real.pi * delta y) ≤
      (3 / 2) * Real.log y := by
  have hd := (delta_bounds hy).1
  have hL := log_ge_nine hy
  have he : (4 * Real.pi * (1 - (α - delta y))) / (2 * Real.pi * delta y) =
      3 * (1 - (α - delta y)) * Real.log y := by
    unfold delta
    field_simp
    ring
  rw [he]
  have hσ : 1 / 2 ≤ α - delta y := by linarith
  nlinarith

theorem ordinary_right_log_budget {y : ℝ} (hy : 10000 ≤ y) :
    (16 * y / (y - 1) ^ 2) / (2 * Real.pi * delta y) ≤ 4 * Real.log y := by
  have hd := (delta_bounds hy).1
  have hL := log_ge_nine hy
  have hp := Real.pi_gt_three.le
  have hfrac : 16 * y / (y - 1) ^ 2 ≤ 16 :=
    (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < y - 1))).mpr (by nlinarith)
  have he : (16 : ℝ) / (2 * Real.pi * delta y) = 12 * Real.log y / Real.pi := by
    unfold delta
    field_simp
    ring
  calc
    _ ≤ 16 / (2 * Real.pi * delta y) := div_le_div_of_nonneg_right hfrac (by positivity)
    _ = _ := he
    _ ≤ _ := (div_le_iff₀ Real.pi_pos).mpr (by nlinarith)

theorem ordinary_lower_order_budget {y α : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    (16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - delta y)) +
      argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y)) /
      (2 * Real.pi * delta y) ≤ 51 * Real.log y ^ 3 := by
  have hL := log_ge_nine hy
  have ha := ordinary_argument_budget hy hα hα1
  have hp := ordinary_pole_budget hy hα
  have hr := ordinary_right_log_budget hy
  rw [add_div, add_div]
  have hcube : 71 * Real.log y ≤ 3 * Real.log y ^ 3 := by
    have hs : 71 ≤ 3 * Real.log y ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ Real.log y by linarith)
    nlinarith
  linarith

theorem ordinary_principal_budget_sharp (q : ℕ) [NeZero q]
    {y α : ℝ} (hy : 10000 ≤ y) (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    (count (1 : Character q) α y : ℝ) ≤
      7000 * y ^ (4 * (1 - α)) * Real.log y ^ (6 * α - 6 * delta y) +
        51 * Real.log y ^ 3 := by
  have hmain := ordinary_mean_budget (α := α) hy
  have hsmall := ordinary_lower_order_budget hy hα hα1
  have hcount := ordinary_principal_high_alpha_density q hy hα hα1
  rw [show
    1861 * y ^ (4 * (1 - (α - delta y))) * Real.log y ^ (6 * (α - delta y) - 1) +
      16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - delta y)) +
      argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y) =
    1861 * y ^ (4 * (1 - (α - delta y))) * Real.log y ^ (6 * (α - delta y) - 1) +
      (16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - delta y)) +
        argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y)) by ring,
    add_div] at hcount
  exact hcount.trans (add_le_add hmain hsmall)

theorem ordinary_principal_budget (q : ℕ) [NeZero q]
    {y α : ℝ} (hy : 10000 ≤ y) (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    (count (1 : Character q) α y : ℝ) ≤
      7000 * y ^ (4 * (1 - α)) * Real.log y ^ (6 * α) + 51 * Real.log y ^ 3 := by
  have hd := (delta_bounds hy).1
  have hL := log_ge_nine hy
  apply (ordinary_principal_budget_sharp q hy hα hα1).trans
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Real.log y) (by linarith))
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))

theorem ordinary_complete_principal_budget (q : ℕ) [NeZero q]
    {y α : ℝ} (hy : 10000 ≤ y) (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    (∑ s ∈ (CompleteExpansion.zeroValues (1 : Character q) y).filter
      (fun s => α ≤ s.re), (analyticOrderNatAt (1 : Character q).LFunction s : ℝ)) ≤
      7000 * y ^ (4 * (1 - α)) * Real.log y ^ (6 * α) + 51 * Real.log y ^ 3 := by
  have hd := (delta_bounds hy).1
  simpa only [count, Applications.values_eq_complete_filter _
    (show 1 / 2 ≤ α by linarith), Nat.cast_sum] using
    ordinary_principal_budget q hy hα hα1

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
