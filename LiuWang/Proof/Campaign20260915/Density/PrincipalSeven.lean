import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.OrdinaryBudget
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.AuxiliaryDomain
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.FamilyAssembly

/-! Pay the original principal-character input from the existing stronger bound.
The family statements still require Chen's full nonprincipal estimate. -/

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem ordinary_budget_le_principalSevenBound {alpha y : ℝ} (hy : 10000 ≤ y) :
    7000 * y ^ (4 * (1 - alpha)) * Real.log y ^ (6 * alpha) +
      51 * Real.log y ^ (3 : ℕ) ≤ principalSevenBound alpha y := by
  have hy0 : 0 ≤ y := by linarith
  have hL : 1 ≤ Real.log y := by
    linarith [log_height_ge_eight hy]
  have hlog : Real.log y ^ (3 : ℕ) ≤ Real.log y ^ (6 : ℕ) :=
    pow_le_pow_right₀ hL (by norm_num)
  have hmain : 0 ≤ y ^ (4 * (1 - alpha)) * Real.log y ^ (6 * alpha) := by
    positivity
  have hextra : 0 ≤ 3872 * y ^ (4 * (1 - alpha)) *
      Real.log y ^ (8 * alpha - 3) := by positivity
  unfold principalSevenBound
  nlinarith only [hlog, hmain, hextra, pow_nonneg (by linarith : 0 ≤ Real.log y) 6]

theorem principal_count_le_principalSevenBound (q : ℕ) [NeZero q]
    {alpha y : ℝ} (hy : 10000 ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1) :
    (count (1 : Character q) alpha y : ℝ) ≤ principalSevenBound alpha y := by
  rw [sourceDelta_eq_strip_delta] at ha
  exact (ordinary_principal_budget q hy ha ha1).trans
    (ordinary_budget_le_principalSevenBound hy)

theorem principal_source_input (q : ℕ) [NeZero q] {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha1 : alpha < 1) :
    1 / 2 + 2 * sourceDelta y ≤ alpha →
      (count (1 : Character 1) alpha y : ℝ) ≤ principalSevenBound alpha y := by
  intro ha
  exact principal_count_le_principalSevenBound 1
    (source_height_ge_ten_thousand hy) ha ha1

theorem family_sourceSeven_with_principal_paid (q : ℕ) [NeZero q]
    {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1)
    (hchen : 3 ≤ q → ∀ beta ∈ Ico (1 / 2) 1,
      (strictNonprincipalCount q beta y : ℝ) ≤ chenBound q beta y) :
    (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y :=
  family_sourceSeven_from_original_inputs q hy ha ha1
    (principal_source_input q hy ha1) hchen

theorem complete_family_sourceSeven_with_principal_paid (q : ℕ) [NeZero q]
    {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1)
    (hchen : 3 ≤ q → ∀ beta ∈ Ico (1 / 2) 1,
      (strictNonprincipalCount q beta y : ℝ) ≤ chenBound q beta y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      16541 * (Real.log y) ^ (6 : ℕ) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
          (Real.log ((q : ℝ) * y)) ^ (6 * alpha) :=
  complete_family_sourceSeven_from_original_inputs q hy ha ha1
    (principal_source_input q hy ha1) hchen

#print axioms principal_count_le_principalSevenBound
#print axioms principal_source_input
#print axioms family_sourceSeven_with_principal_paid
#print axioms complete_family_sourceSeven_with_principal_paid

end LiuWang.Proof.Campaign20260915.Density
