import LiuWang.Proof.DirichletZeroCount.Applications.ClosedHeight
import LiuWang.Proof.DirichletZeroCount.Applications.DensityWeights

/-! # Right limits of actual counts and the complete-S zero-value sum -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.DirichletZeroCount.Applications

theorem continuousWithinAt_of_right_plateau {β : Type*} [PseudoMetricSpace β]
    {f : ℝ → β} {y H : ℝ} (hyH : y < H)
    (hf : ∀ t : ℝ, y ≤ t → t ≤ H → f t = f y) :
    ContinuousWithinAt f (Set.Ici y) y := by
  apply Metric.continuousWithinAt_iff.mpr
  intro e he
  refine ⟨H - y, sub_pos.mpr hyH, ?_⟩
  intro t ht hdist
  have hyt : y ≤ t := ht
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyt)] at hdist
  rw [hf t hyt (by linarith), dist_self]
  exact he

theorem count_continuousWithinAt_right {q : ℕ} [NeZero q] (chi : Character q)
    (alpha y : ℝ) :
    ContinuousWithinAt (fun t : ℝ => (count chi alpha t : ℝ)) (Set.Ici y) y := by
  obtain ⟨H, hyH, _, hc, _, _⟩ :=
    exists_common_count_plateau q (y := y) (r := 1) (by norm_num)
  exact continuousWithinAt_of_right_plateau hyH
    (fun t ht htH => congrArg (fun n : ℕ => (n : ℝ)) (hc chi alpha t ht htH))

theorem familyCount_continuousWithinAt_right (q : ℕ) [NeZero q] (alpha y : ℝ) :
    ContinuousWithinAt (fun t : ℝ => (familyCount q alpha t : ℝ)) (Set.Ici y) y := by
  obtain ⟨H, hyH, _, _, hc, _⟩ :=
    exists_common_count_plateau q (y := y) (r := 1) (by norm_num)
  exact continuousWithinAt_of_right_plateau hyH
    (fun t ht htH => congrArg (fun n : ℕ => (n : ℝ)) (hc alpha t ht htH))

theorem zeroValueSum_continuousWithinAt_right {q : ℕ} [NeZero q] (chi : Character q)
    (N : ℕ) (eta y : ℝ) :
    ContinuousWithinAt (fun t : ℝ => CompleteExpansion.zeroValueSum chi N t eta)
      (Set.Ici y) y := by
  obtain ⟨H, hyH, _, hv, _⟩ :=
    exists_complete_common_regular_height q (y := y) (r := 1) (by norm_num)
  apply continuousWithinAt_of_right_plateau hyH
  intro t ht htH
  simp only [CompleteExpansion.zeroValueSum, hv chi t ht htH]

theorem complete_band_weighted_continuousWithinAt_right {q : ℕ} [NeZero q]
    (chi : Character q) (alpha u y : ℝ) (w : ℂ → ℝ) :
    ContinuousWithinAt
      (fun t : ℝ => ∑ rho ∈ (CompleteExpansion.zeroValues chi t).filter
        (fun rho => alpha ≤ rho.re ∧ u ≤ |rho.im|),
          (analyticOrderNatAt chi.LFunction rho : ℝ) * w rho) (Set.Ici y) y := by
  obtain ⟨H, hyH, _, hv, _⟩ :=
    exists_complete_common_regular_height q (y := y) (r := 1) (by norm_num)
  apply continuousWithinAt_of_right_plateau hyH
  intro t ht htH
  simp only [hv chi t ht htH]

end LiuWang.Proof.DirichletZeroCount.Applications
