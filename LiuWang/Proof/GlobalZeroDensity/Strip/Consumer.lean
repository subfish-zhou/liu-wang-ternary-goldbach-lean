import LiuWang.Proof.GlobalZeroDensity.Strip.Window
import LiuWang.Proof.GlobalZeroDensity.Strip.FullAxis

set_option autoImplicit false

namespace LiuWang.Proof.GlobalZeroDensity.Strip

theorem actual_moving_boundary {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : s.re = 1 + delta y) :
    ‖regularG y s‖ ^ 2 ≤ (7 / 4) * Real.log y ^ 4 ∧
      F y s ≤ (169 / 100) * Real.log y ^ 4 :=
  ⟨regularG_moving_sq hy hs, F_right_half hy hs.ge⟩

theorem actual_strip_and_window {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Set.Icc (1 / 2) (1 + delta y)) (t : ℝ) :
    ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (33 * y ^ 2) ^ (1 - rightWeight y σ) *
        ((7 / 4) * Real.log y ^ 4) ^ rightWeight y σ ∧
      K y σ ≤ 42 * y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4) := by
  constructor
  · simpa using regularG_interpolation hy (s := (σ : ℂ) + t * Complex.I)
      (by simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hσ)
  · exact K_left hy hσ

theorem actual_lemma_3_3 {y σ : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    (1 / 2 ≤ σ ∧ σ ≤ 1 + delta y →
      K y σ ≤ (42021 / 1000) * y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4)) ∧
    (1 + delta y ≤ σ ∧ σ ≤ 4 → K y σ ≤ (174 / 100) * Real.log y ^ 4) :=
  lemma_3_3 hy

theorem actual_critical_weighted_mean {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    MeasureTheory.Integrable
      (fun t : ℝ => ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ∧
      weightedMean y (1 / 2) ≤ 230 * y ^ 2 * Real.log y ∧
      weightedMean y (1 / 2) ≤ (25413 / 100) * y ^ 2 * Real.log y := by
  have hy' : 10000 ≤ y := by linarith [Sharp.log_six_ge_one]
  exact ⟨integrable_regularG_critical_sq (by linarith), weightedMean_critical_sharp hy',
    critical_254_13 hy⟩

theorem actual_full_axis_inputs {y : ℝ} (hy : 10000 ≤ y) :
    (∀ σ ∈ Set.Icc (1 / 2) (1 + delta y),
      MeasureTheory.Integrable (fun t : ℝ => ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2)) ∧
    MeasureTheory.Integrable
      (fun t : ℝ => ‖regularG y (((1 + delta y : ℝ) : ℂ) + t * Complex.I)‖ ^ 2) ∧
    weightedMean y (1 / 2) ≤ 230 * y ^ 2 * Real.log y ∧
    weightedMean y (1 + delta y) ≤ (1183 / 125) * y * Real.log y ^ 4 := by
  have hd := delta_bounds hy
  exact ⟨fun _ hσ => regularG_strip_integrable hy hσ,
    regularG_right_integrable hy le_rfl (by linarith),
    weightedMean_critical_sharp hy, weightedMean_right_bound hy le_rfl (by linarith)⟩

theorem actual_removable_point {y : ℝ} (hy : 10000 ≤ y) :
    regularG y 1 = Q y 1 / Complex.cos (1 / (2 * (y : ℂ))) ∧
    ‖Q y 1 / Complex.cos (1 / (2 * (y : ℂ)))‖ ^ 2 ≤ 33 * Real.log y ^ 4 ∧
    MeasureTheory.Integrable
      (fun t : ℝ => ‖regularG y ((1 : ℂ) + t * Complex.I)‖ ^ 2) := by
  have hd := delta_bounds hy
  have hσ : (1 : ℝ) ∈ Set.Icc (1 / 2) (1 + delta y) := by
    constructor <;> linarith
  have hb := regularG_strip_source hy (s := 1)
    (by simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hσ)
  rw [regularG_one] at hb
  norm_num at hb
  exact ⟨regularG_one y, by norm_num; exact hb, regularG_strip_integrable hy hσ⟩

end LiuWang.Proof.GlobalZeroDensity.Strip
