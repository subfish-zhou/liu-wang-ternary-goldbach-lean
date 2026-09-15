import LiuWang.Proof.Campaign20260915.Density.Equation30
import LiuWang.Proof.Campaign20260915.Density.SharpRecovery

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Set
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis (cosineDetector)
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

def chenEndpointBudget (q : ℕ) (y sigma : ℝ) : ℝ :=
  let theta := (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))
  (235.69 * ((q : ℝ) * y) ^ (3 / 2 : ℝ) * y ^ (1 / 2 : ℝ) *
    Real.log ((q : ℝ) * y) ^ 2) ^ (1 - theta) *
  (90.5727 * Real.log ((q : ℝ) * y) ^ 5) ^ theta

theorem source_family_chen_endpoints (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2) ≤
      chenEndpointBudget q y sigma := by
  have hd := source_product_shift_bounds q hy
  have hy0 : 0 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have ht0 : 0 ≤ (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y)) :=
    div_nonneg (sub_nonneg.mpr hs.1) (by linarith)
  have ht1 : (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y)) ≤ 1 := by
    apply (div_le_one (by linarith)).mpr
    linarith [hs.2]
  have hL := Real.rpow_le_rpow
    (sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
    (source_family_equation_30 q hy) (show 0 ≤ 1 - (sigma - 1 / 2) /
      (1 / 2 + sourceDelta ((q : ℝ) * y)) by linarith)
  have hR := Real.rpow_le_rpow
    (sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
    (source_family_equation_31 q hy) ht0
  exact (source_family_interpolation q hy hs).trans
    (mul_le_mul hL hR (Real.rpow_nonneg
      (sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))) _)
      (Real.rpow_nonneg (by positivity) _))

theorem source_familyMean_chen_endpoints (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    SourceRoute.Density.Restart.familyMean q ((q : ℝ) * y) sigma y ≤
      1.272 * chenEndpointBudget q y sigma := by
  have hy' : 2 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hd := source_product_shift_bounds q hy
  have h := (family_window_le_cosine_sharp q ((q : ℝ) * y) hy'
    ⟨hs.1, by linarith [hs.2]⟩).trans
    (mul_le_mul_of_nonneg_left (source_family_chen_endpoints q hy hs) (by norm_num))
  rw [SourceRoute.Density.Restart.familyMean]
  unfold SourceRoute.Density.Restart.familySquare
  rw [intervalIntegral.integral_finsetSum]
  · exact h
  · intro chi hc
    exact f_vertical_integrable
      ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc) _ _ _

#print axioms source_family_chen_endpoints
#print axioms source_familyMean_chen_endpoints

end LiuWang.Proof.Campaign20260915.Density
