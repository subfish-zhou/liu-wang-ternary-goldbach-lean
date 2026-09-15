import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.Endpoints
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.Interpolation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets

theorem equation_3_46 {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y))
    (hzmax : ∀ u : ℝ, 0 ≤ u → ∀ t ∈ Icc (-(y * u)) (y * u),
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ 12.5 * (2 + y * u))
    (hzmean : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        8 * (2 + y * u) ^ 2)
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    weightedMean y sigma ≤
      (254.13 * y ^ 2 * Real.log y) ^ ((1 + sourceDelta y - sigma) / (1 / 2 + sourceDelta y)) *
        (90.5727 * Real.log y ^ 5) ^ ((sigma - 1 / 2) / (1 / 2 + sourceDelta y)) := by
  have hd : 0 < sourceDelta y := by
    rw [sourceDelta_eq_strip_delta]
    exact (Strip.delta_bounds (by linarith [(source_height_log_bounds hy).1])).1
  apply (actual_mean_interpolation hy hs).trans
  exact mul_le_mul
    (Real.rpow_le_rpow (MeanInterpolation.weightedMean_nonneg _ _)
      (equation_3_44 hy hzmax hzmean hchen24) (div_nonneg (by linarith [hs.2]) (by linarith)))
    (Real.rpow_le_rpow (MeanInterpolation.weightedMean_nonneg _ _)
      (equation_3_45 hy hchen14) (div_nonneg (by linarith [hs.1]) (by linarith)))
    (Real.rpow_nonneg (MeanInterpolation.weightedMean_nonneg _ _) _)
    (Real.rpow_nonneg (by have := (source_height_log_bounds hy).2; positivity) _)

theorem equation_3_46_source_shape {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y))
    (hzmax : ∀ u : ℝ, 0 ≤ u → ∀ t ∈ Icc (-(y * u)) (y * u),
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ 12.5 * (2 + y * u))
    (hzmean : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        8 * (2 + y * u) ^ 2)
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    weightedMean y sigma ≤ 90.5727 * Real.exp (4 / 1.5) *
      y ^ (4 * (1 - sigma)) * Real.log y ^ (8 * sigma - 3) :=
  (equation_3_46 hy hs hzmax hzmean hchen24 hchen14).trans (original_interpolation_scalar hy hs)

theorem lemma_3_5_from_original_inputs {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y))
    (hzmax : ∀ u : ℝ, 0 ≤ u → ∀ t ∈ Icc (-(y * u)) (y * u),
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ 12.5 * (2 + y * u))
    (hzmean : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        8 * (2 + y * u) ^ 2)
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    M y sigma y ≤ 3318.39 * y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 1) := by
  obtain ⟨hy', hL⟩ := source_height_log_bounds hy
  have hd : 0 < sourceDelta y := by
    rw [sourceDelta_eq_strip_delta]; exact (Strip.delta_bounds (by linarith)).1
  have hstrip : sigma ∈ Icc (1 / 2) (1 + sourceDelta y) := ⟨hs.1, by linarith [hs.2]⟩
  have hsmall := original_small_window_scalar hy ⟨hs.1, by linarith [hs.2]⟩
  have hmean := equation_3_46_source_shape hy hstrip hzmax hzmean hchen24 hchen14
  have hlogpow : Real.log y ^ (8 * sigma - 3) ≤ Real.log y ^ (6 * sigma - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hs.2])
  have hmean' : weightedMean y sigma ≤
      (90.5727 * 14.392) * (y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 1)) := by
    have he := mul_le_mul_of_nonneg_left source_exp_constant (by norm_num : (0 : ℝ) ≤ 90.5727)
    have hp := mul_le_mul he hlogpow
      (by positivity : 0 ≤ Real.log y ^ (8 * sigma - 3)) (by norm_num)
    have hp' := mul_le_mul_of_nonneg_right hp (show 0 ≤ y ^ (4 * (1 - sigma)) by positivity)
    nlinarith
  have htransfer := MeanTransfer.equation_3_47_with_small_window_paid hy hs
  have hpay := mul_le_mul_of_nonneg_left hmean' (by norm_num : (0 : ℝ) ≤ 1.272 * 2)
  have hn : 0 ≤ y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 1) := by positivity
  nlinarith

theorem lemma_3_5_from_3_36_and_chen {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y))
    (h336 : ∀ t : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      Real.sqrt 2 * (2 + (1 / 2 + |t|)⁻¹) * Real.sqrt (1 / 2 + |t|))
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    M y sigma y ≤ 3318.39 * y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 1) := by
  have hy0 : 0 ≤ y := by linarith [(source_height_log_bounds hy).1]
  exact lemma_3_5_from_original_inputs hy hs
    (fun u hu => (zeta_inputs_of_3_36 (mul_nonneg hy0 hu) h336).1)
    (fun u hu => (zeta_inputs_of_3_36 (mul_nonneg hy0 hu) h336).2) hchen24 hchen14

theorem lemma_3_5_at_source_shift (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1)
    (h336 : ∀ t : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      Real.sqrt 2 * (2 + (1 / 2 + |t|)⁻¹) * Real.sqrt (1 / 2 + |t|))
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    M y (alpha - sourceDelta y) y ≤
      3318.39 * y ^ (4 * (1 - (alpha - sourceDelta y))) *
        Real.log y ^ (6 * (alpha - sourceDelta y) - 1) := by
  have hs := source_shift_in_lemma_3_5_domain ha ha1 (source_height_ge_log_six hy)
  rw [← sourceDelta_eq_strip_delta] at hs
  exact lemma_3_5_from_3_36_and_chen (source_height_ge_log_six hy) hs h336 hchen24 hchen14

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets
