import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.OriginalCutoff
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.Consumer

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336

theorem zeta_inputs {v : ℝ} (hv : 0 ≤ v) :
    (∀ t ∈ Icc (-v) v,
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ 12.5 * (2 + v)) ∧
    (∫ t in -v..v, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤ 8 * (2 + v) ^ 2 :=
  zeta_inputs_of_3_36 hv equation_3_36

theorem lemma_3_4_with_zeta_paid {y u : ℝ} (hy : 10000 * Real.log 6 ≤ y) (hu : 0 ≤ u)
    (hchen24 : (∫ t in -(y * u)..y * u,
      ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤ y * (2.19021 * u + 2.906) * Real.log y) :
    M y (1 / 2) (y * u) ≤
      12.508 * y * (2 + y * u) * (2.19021 * u + 2.906) * Real.log y := by
  have hv : 0 ≤ y * u := mul_nonneg (by linarith [(source_height_log_bounds hy).1]) hu
  exact lemma_3_4_from_original_inputs hy hu (zeta_inputs hv).1 (zeta_inputs hv).2 hchen24

theorem equation_3_46_with_zeta_paid {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y))
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    weightedMean y sigma ≤ 90.5727 * Real.exp (4 / 1.5) *
      y ^ (4 * (1 - sigma)) * Real.log y ^ (8 * sigma - 3) := by
  have hy0 : 0 ≤ y := by linarith [(source_height_log_bounds hy).1]
  exact MeanBudgets.equation_3_46_source_shape hy hs
    (fun u hu => (zeta_inputs (mul_nonneg hy0 hu)).1)
    (fun u hu => (zeta_inputs (mul_nonneg hy0 hu)).2) hchen24 hchen14

theorem lemma_3_5_with_zeta_paid {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y))
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    M y sigma y ≤ 3318.39 * y ^ (4 * (1 - sigma)) * Real.log y ^ (6 * sigma - 1) :=
  MeanBudgets.lemma_3_5_from_3_36_and_chen hy hs equation_3_36 hchen24 hchen14

theorem lemma_3_5_at_source_shift_with_zeta_paid (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1)
    (hchen24 : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -(y * u)..y * u, ‖Q y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        y * (2.19021 * u + 2.906) * Real.log y)
    (hchen14 : ∀ u : ℝ, 0 ≤ u →
      M y (1 + sourceDelta y) (y * u) ≤ (67.929 + 0.0003 * u) * Real.log y ^ 5) :
    M y (alpha - sourceDelta y) y ≤
      3318.39 * y ^ (4 * (1 - (alpha - sourceDelta y))) *
        Real.log y ^ (6 * (alpha - sourceDelta y) - 1) :=
  MeanBudgets.lemma_3_5_at_source_shift q hy ha ha1 equation_3_36 hchen24 hchen14

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336
