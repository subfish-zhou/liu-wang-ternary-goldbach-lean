import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.WeightedRight

/-! Symbolic source-shaped L2 budgets retaining the full moving-strip width. -/

set_option autoImplicit false

noncomputable section

open Set
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem weightedMean_explicit {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    weightedMean y σ ≤
      (230 * y ^ 2 * Real.log y) ^ (1 - rightWeight y σ) *
        (280 * Real.log y ^ 4) ^ rightWeight y σ := by
  have hw := weight_bounds hy hσ
  apply (weightedMean_interpolation hy hσ).trans
  exact mul_le_mul
    (Real.rpow_le_rpow (weightedMean_nonneg _ _) (weightedMean_critical_sharp hy) (by linarith))
    (Real.rpow_le_rpow (weightedMean_nonneg _ _) (weightedMean_moving_sharp hy) hw.1)
    (Real.rpow_nonneg (weightedMean_nonneg _ _) _)
    (Real.rpow_nonneg (by have := log_ge_nine hy; positivity) _)

theorem mean_log_budget {y : ℝ} (hy : 10000 ≤ y) :
    Real.log 280 + 8 / 3 ≤ Real.log 600 + Real.log (Real.log y) := by
  have hL := log_ge_nine hy
  have hl0 : 0 < Real.log y := by linarith
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 280 * 33)
    (show (280 : ℝ) * 33 ≤ 600 * Real.log y * (7 / 4) by nlinarith)
  rw [Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by positivity) (by norm_num),
    Real.log_mul (by norm_num) hl0.ne'] at h
  linarith [log_boundary_budget]

theorem mean_interpolation_budget {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    (230 * y ^ 2 * Real.log y) ^ (1 - rightWeight y σ) *
        (280 * Real.log y ^ 4) ^ rightWeight y σ ≤
      600 * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) := by
  have hL := log_ge_nine hy
  have hy0 : 0 < y := by linarith
  have hl0 : 0 < Real.log y := by linarith
  have hll : 0 ≤ Real.log (Real.log y) := Real.log_nonneg (by linarith)
  have hw := weight_bounds hy hσ
  have hd := delta_bounds hy
  have hrel : (1 / 2 + delta y) * rightWeight y σ = σ - 1 / 2 := by
    unfold rightWeight
    exact mul_div_cancel₀ _ (ne_of_gt (by linarith : 0 < 1 / 2 + delta y))
  have hdl : delta y * Real.log y = 2 / 3 := by unfold delta; field_simp
  have hconst : Real.log 230 ≤ Real.log 280 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hbudget := mean_log_budget hy
  rw [Real.rpow_def_of_pos (by positivity : 0 < 230 * y ^ 2 * Real.log y),
    Real.rpow_def_of_pos (by positivity : 0 < 280 * Real.log y ^ 4),
    Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hl0,
    Real.log_mul (by positivity) hl0.ne',
    Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow, ← Real.exp_add]
  have h600 : (600 : ℝ) = Real.exp (Real.log 600) := (Real.exp_log (by norm_num)).symm
  conv_rhs => rw [h600]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc := mul_le_mul_of_nonneg_right hconst (show 0 ≤ 1 - rightWeight y σ by linarith)
  have hrelL := congrArg (fun x : ℝ => x * Real.log y) hrel
  have hrell := congrArg (fun x : ℝ => x * Real.log (Real.log y)) hrel
  have hdlw := congrArg (fun x : ℝ => x * rightWeight y σ) hdl
  have hpos := mul_nonneg (mul_nonneg hd.1.le hw.1) hll
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

theorem weightedMean_source_shape {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    weightedMean y σ ≤ 600 * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) :=
  (weightedMean_explicit hy hσ).trans (mean_interpolation_budget hy hσ)

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
