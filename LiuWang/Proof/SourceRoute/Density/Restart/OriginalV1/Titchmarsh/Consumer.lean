import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh.SmallMean

set_option autoImplicit false
noncomputable section

open Complex Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh

theorem equation_3_39_literal_domain {y sigma t : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (hs : 1 / 2 ≤ sigma)
    (hs' : sigma ≤ 1 - 1 / (1.5 * Real.log y)) (ht : |t| ≤ 1) :
    ‖riemannZeta ((sigma : ℂ) + t * I)‖ ≤
        (1 / 2) * Real.sqrt (((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2)) +
          Real.sqrt (sigma ^ 2 + t ^ 2) / (2 * sigma) ∧
      (1 / 2) * Real.sqrt (((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2)) +
          Real.sqrt (sigma ^ 2 + t ^ 2) / (2 * sigma) ≤ 1.5 * Real.log y :=
  equation_3_39 hy ⟨hs, hs'⟩ ht

theorem equation_3_41_at_source_shift (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1)
    (hchen11 : ∀ u : ℝ, ‖Q y ((1 / 2 : ℂ) + u * I)‖ ≤ 1.3071 * Real.sqrt y)
    (hchen12 : ∀ u : ℝ, ‖Q y ((1 : ℂ) + u * I)‖ ≤ 1.19 * Real.log y) :
    M y (alpha - sourceDelta y) 1 ≤
      2 * 4.255 * y ^ (2 * (1 - (alpha - sourceDelta y))) *
        (Real.log y) ^ (4 * (alpha - sourceDelta y)) := by
  have hy' := source_height_ge_log_six hy
  have hs := source_shift_in_lemma_3_5_domain ha ha1 hy'
  rw [← sourceDelta_eq_strip_delta] at hs
  exact equation_3_41 hy' hs hchen11 hchen12

theorem closed_height_endpoints {y sigma : ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) :
    ‖riemannZeta ((sigma : ℂ) + I)‖ ≤ 1.5 * Real.log y ∧
      ‖riemannZeta ((sigma : ℂ) - I)‖ ≤ 1.5 * Real.log y := by
  constructor
  · simpa using zeta_small_height hy hs (t := 1) (by norm_num)
  · simpa [sub_eq_add_neg] using zeta_small_height hy hs (t := -1) (by norm_num)

theorem closed_sigma_endpoint {y t : ℝ}
    (hy : 10000 * Real.log 6 ≤ y) (ht : |t| ≤ 1) :
    ‖riemannZeta (((1 - sourceDelta y : ℝ) : ℂ) + t * I)‖ ≤
      1.5 * Real.log y := by
  have hy' := (source_height_log_bounds hy).1
  have hd := sourceDelta_le_twelfth (show 10000 ≤ y by linarith)
  exact zeta_small_height hy ⟨by linarith, le_rfl⟩ ht

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh
