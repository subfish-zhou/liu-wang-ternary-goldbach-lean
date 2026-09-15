import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer.Window
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.ThreeLines

set_option autoImplicit false
noncomputable section

open Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets

theorem original_interpolation_scalar {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) :
    (254.13 * y ^ 2 * Real.log y) ^ ((1 + sourceDelta y - sigma) / (1 / 2 + sourceDelta y)) *
      (90.5727 * Real.log y ^ 5) ^ ((sigma - 1 / 2) / (1 / 2 + sourceDelta y)) ≤
      90.5727 * Real.exp (4 / 1.5) * y ^ (4 * (1 - sigma)) *
        Real.log y ^ (8 * sigma - 3) := by
  obtain ⟨hy', hL⟩ := source_height_log_bounds hy
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < Real.log y := by linarith
  have hll : 0 ≤ Real.log (Real.log y) := Real.log_nonneg (by linarith)
  rw [sourceDelta_eq_strip_delta] at hs ⊢
  have hw := Strip.weight_bounds (by linarith) hs
  have hd := Strip.delta_bounds (show 10000 ≤ y by linarith)
  have hr : (1 / 2 + Strip.delta y) * Strip.rightWeight y sigma = sigma - 1 / 2 := by
    unfold Strip.rightWeight
    exact mul_div_cancel₀ _ (by linarith : 1 / 2 + Strip.delta y ≠ 0)
  have hdl : Strip.delta y * Real.log y = 2 / 3 := by
    unfold Strip.delta; field_simp
  have he : (1 + Strip.delta y - sigma) / (1 / 2 + Strip.delta y) =
      1 - Strip.rightWeight y sigma := by
    unfold Strip.rightWeight
    apply (div_eq_iff (by linarith : 1 / 2 + Strip.delta y ≠ 0)).mpr
    rw [sub_mul, div_mul_cancel₀ _ (by linarith : 1 / 2 + Strip.delta y ≠ 0)]
    ring
  rw [he]
  change (254.13 * y ^ 2 * Real.log y) ^ (1 - Strip.rightWeight y sigma) *
    (90.5727 * Real.log y ^ 5) ^ Strip.rightWeight y sigma ≤ _
  have hc : Real.log 254.13 ≤ Real.log 90.5727 + 4 / 1.5 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 254.13)).mpr
    rw [Real.exp_add, Real.exp_log (by norm_num)]
    nlinarith [Real.add_one_le_exp (4 / 1.5)]
  rw [Real.rpow_def_of_pos (by positivity : 0 < 254.13 * y ^ 2 * Real.log y),
    Real.rpow_def_of_pos (by positivity : 0 < 90.5727 * Real.log y ^ 5),
    Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hL0,
    Real.log_mul (by positivity) hL0.ne', Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow, ← Real.exp_add]
  conv_rhs => rw [show (90.5727 : ℝ) = Real.exp (Real.log 90.5727) from
    (Real.exp_log (by norm_num)).symm]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc' := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ 1 - Strip.rightWeight y sigma)
  have hrL := congrArg (fun x : ℝ => x * Real.log y) hr
  have hrl := congrArg (fun x : ℝ => x * Real.log (Real.log y)) hr
  have hdlw := congrArg (fun x : ℝ => x * Strip.rightWeight y sigma) hdl
  have hp := mul_nonneg (mul_nonneg hd.1.le hw.1) hll
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

theorem actual_mean_interpolation {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) :
    weightedMean y sigma ≤
      weightedMean y (1 / 2) ^ ((1 + sourceDelta y - sigma) / (1 / 2 + sourceDelta y)) *
        weightedMean y (1 + sourceDelta y) ^ ((sigma - 1 / 2) / (1 / 2 + sourceDelta y)) := by
  have hy' : 10000 ≤ y := by linarith [(source_height_log_bounds hy).1]
  rw [sourceDelta_eq_strip_delta] at hs ⊢
  have hd := Strip.delta_bounds hy'
  have he : (1 + Strip.delta y - sigma) / (1 / 2 + Strip.delta y) =
      1 - Strip.rightWeight y sigma := by
    unfold Strip.rightWeight
    apply (div_eq_iff (by linarith : 1 / 2 + Strip.delta y ≠ 0)).mpr
    rw [sub_mul, div_mul_cancel₀ _ (by linarith : 1 / 2 + Strip.delta y ≠ 0)]
    ring
  rw [he]
  exact MeanInterpolation.weightedMean_interpolation hy' hs

theorem source_exp_constant : Real.exp (4 / 1.5) ≤ 14.392 := by
  have he : Real.exp 1 ≤ 2.718282 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have hc : Real.exp (4 / 1.5) ^ 3 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  by_contra h
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 14.392)
    (le_of_lt (lt_of_not_ge h)) 3
  rw [hc] at hpow
  norm_num at hpow
  linarith

theorem original_small_window_scalar {y sigma : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (hs : sigma ∈ Icc (1 / 2) 1) :
    2 * 4.255 * y ^ (2 * (1 - sigma)) * Real.log y ^ (4 * sigma) ≤
      y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 1) := by
  obtain ⟨hy', hL⟩ := source_height_log_bounds hy
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < Real.log y := by linarith
  have hpow : y ^ (2 * (1 - sigma)) * Real.log y ^ (4 * sigma) ≤
      y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 2) := by
    rw [Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hL0,
      Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hL0, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_nonneg (sub_nonneg.mpr hs.2)
      (sub_nonneg.mpr ((Real.log_le_sub_one_of_pos hL0).trans (by linarith)))
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2 * 4.255)
  have hb := mul_le_mul_of_nonneg_right (show 2 * 4.255 ≤ Real.log y by linarith)
    (show 0 ≤ y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 2) by positivity)
  have he : Real.log y * (y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 2)) =
      y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 1) := by
    rw [show 6 * sigma - 1 = (6 * sigma - 2) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    ring
  rw [he] at hb
  nlinarith

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets
