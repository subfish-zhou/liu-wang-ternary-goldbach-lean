import LiuWang.Proof.Campaign20260915.Density.FamilyChen14
import LiuWang.Proof.SourceRoute.Density.Restart.ProductVertical

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_familyMean_right_paid (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    SourceRoute.Density.Restart.familyMean q ((q : ℝ) * y)
      (1 + sourceDelta ((q : ℝ) * y)) (y * u) ≤
      (67.929 + 0.0003 * u) * Real.log ((q : ℝ) * y) ^ 5 := by
  rw [SourceRoute.Density.Restart.familyMean]
  unfold SourceRoute.Density.Restart.familySquare
  rw [intervalIntegral.integral_finsetSum]
  · exact source_full_nonprincipal_chen14 q hy hu
  · intro chi hc
    exact NonprincipalDensityMeans.f_vertical_integrable
      ((mem_nonprincipalCharacters chi).mp hc) _ _ _

theorem source_Fmean_right_paid (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    NonprincipalDensityMeans.Fmean q ((q : ℝ) * y)
      (1 + sourceDelta ((q : ℝ) * y)) (y * u) ≤
      ((67.929 + 0.0003 * u) * Real.log ((q : ℝ) * y) ^ 5) / q.totient :=
  div_le_div_of_nonneg_right (source_full_nonprincipal_chen14 q hy hu) (Nat.cast_nonneg _)

#print axioms source_familyMean_right_paid
#print axioms source_Fmean_right_paid

end LiuWang.Proof.Campaign20260915.Density
