import LiuWang.Proof.SourceRoute.ThirdArc.LowWeight
import LiuWang.Proof.SourceRoute.ThirdArc.ErrorBudget

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc

theorem real_zero_in_low_band {N q : ℕ} [NeZero q] {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (sourceT N)) (hg : rho.im = 0) :
    rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
      (fun rho => 0 ≤ |rho.im| ∧ |rho.im| ≤ lowHeight) := by
  apply Finset.mem_filter.mpr
  refine ⟨hr, ?_⟩
  simpa only [hg, abs_zero] using And.intro (le_refl (0 : ℝ)) lowHeight_pos.le

theorem real_zero_not_middle_band {N q : ℕ} [NeZero q]
    (chi : Character q) {rho : ℂ} (hg : rho.im = 0) :
    rho ∉ (CompleteExpansion.zeroValues chi (sourceT N)).filter
      (fun rho => lowHeight ≤ |rho.im| ∧ |rho.im| ≤ middleHeight N q) := by
  intro hr
  have h := (Finset.mem_filter.mp hr).2.1
  rw [hg, abs_zero] at h
  exact (not_le.mpr lowHeight_pos) h

theorem collapsed_height_interval (q : ℕ) [NeZero q] (alpha : ℝ)
    {u : ℝ} (hu : 0 < u) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u u,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) ≤
      (1 / u) * familyCount q alpha u := by
  simpa only [intervalIntegral.integral_same, add_zero] using equation_5_39 q alpha hu le_rfl

theorem beta_lower_endpoint {X : ℝ} (hX : 0 < X) :
    (∫ alpha in (1 / 2 : ℝ)..1,
      (Set.Iic (1 / 2 : ℝ)).indicator (betaKernel X) alpha) = 0 := by
  have h : (∫ alpha in (1 / 2 : ℝ)..1,
      (Set.Iic (1 / 2 : ℝ)).indicator (betaKernel X) alpha) =
      ∫ alpha in (1 / 2 : ℝ)..(1 / 2 : ℝ), betaKernel X alpha :=
    intervalIntegral.integral_indicator ⟨le_rfl, by norm_num⟩
  rw [h, integral_betaKernel hX]
  ring

end LiuWang.Proof.SourceRoute.ThirdArc
