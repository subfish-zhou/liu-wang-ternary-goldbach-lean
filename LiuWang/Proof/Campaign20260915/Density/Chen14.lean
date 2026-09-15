import LiuWang.Proof.Campaign20260915.Density.RightMeanLimit
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.CriticalMean
import LiuWang.Proof.DirichletZeroCount.Applications.LowAlpha

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem right_error_polynomial {L : ℝ} (hL : 8 ≤ L) :
    4 * (3 * (1 + (3 / 4) * L) ^ 4 + (3 * L) * (1 + L) ^ 4) +
      4 * (1 + (3 / 2) * L) ^ 5 ≤ 66 * L ^ 5 := by
  have h1 := pow_le_pow_left₀ (show 0 ≤ 1 + (3 / 4) * L by linarith)
    (show 1 + (3 / 4) * L ≤ (7 / 8) * L by linarith) 4
  have h2 := pow_le_pow_left₀ (show 0 ≤ 1 + L by linarith)
    (show 1 + L ≤ (9 / 8) * L by linarith) 4
  have h3 := pow_le_pow_left₀ (show 0 ≤ 1 + (3 / 2) * L by linarith)
    (show 1 + (3 / 2) * L ≤ (13 / 8) * L by linarith) 5
  have h4 : 8 * L ^ 4 ≤ L ^ 5 := by
    nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ L by linarith) 4)
      (show 0 ≤ L - 8 by linarith)]
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ L by linarith)
  norm_num [mul_pow] at h1 h3 h2'
  nlinarith only [h1, h2', h3, h4]

theorem source_shift_decay {y : ℝ} (hy : 1 < y) :
    y ^ (-2 * sourceDelta y) ≤ 1 / 2 := by
  have hL : 0 < Real.log y := Real.log_pos hy
  rw [Real.rpow_def_of_pos (by linarith : 0 < y)]
  have he : Real.log y * (-2 * sourceDelta y) = -(4 / 3 : ℝ) := by
    unfold sourceDelta
    field_simp
    ring
  rw [he, Real.exp_neg]
  have hh : (2 : ℝ) ≤ Real.exp (4 / 3) := by
    linarith [Real.add_one_le_exp (4 / 3 : ℝ)]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hh

theorem chen14_right_mean {y u : ℝ} (hy : 10000 * Real.log 6 ≤ y) (hu : 0 ≤ u) :
    M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5 := by
  obtain ⟨hy', hL⟩ := source_height_log_bounds hy
  have hy1 : 1 < y := by linarith
  have hd : 0 < sourceDelta y := by unfold sourceDelta; positivity
  have hm := actual_right_mean hy1 hd (show 0 ≤ y * u by positivity)
  have hi : 1 / sourceDelta y = (3 / 2) * Real.log y := by
    unfold sourceDelta
    field_simp
    norm_num
  have hi2 : 1 / (2 * sourceDelta y) = (3 / 4) * Real.log y := by
    rw [show 1 / (2 * sourceDelta y) = (1 / 2) * (1 / sourceDelta y) by ring, hi]
    ring
  have hi3 : 1 / ((3 / 2) * sourceDelta y) = Real.log y := by
    rw [show 1 / ((3 / 2) * sourceDelta y) = (2 / 3) * (1 / sourceDelta y) by ring, hi]
    ring
  have hi4 : 2 / sourceDelta y = 3 * Real.log y := by
    rw [show 2 / sourceDelta y = 2 * (1 / sourceDelta y) by ring, hi]
    ring
  rw [hi2, hi3, hi4, hi] at hm
  have herr := right_error_polynomial (show 8 ≤ Real.log y by linarith)
  have hdiag : 2 * (y * u) * ((24 / y) * y ^ (-2 * sourceDelta y)) ≤ 24 * u := by
    have he : 2 * (y * u) * ((24 / y) * y ^ (-2 * sourceDelta y)) =
        48 * u * y ^ (-2 * sourceDelta y) := by field_simp; ring
    rw [he]
    have h := mul_le_mul_of_nonneg_left (source_shift_decay hy1)
      (show 0 ≤ 48 * u by positivity)
    nlinarith only [h]
  have hslope : 24 ≤ 0.0003 * Real.log y ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9.75) hL 5
    norm_num at hp
    linarith
  have hsl := mul_le_mul_of_nonneg_right hslope hu
  have hp : 0 ≤ Real.log y ^ 5 := by positivity
  nlinarith only [hm, herr, hdiag, hsl, hp]

#print axioms chen14_right_mean

end LiuWang.Proof.Campaign20260915.Density
