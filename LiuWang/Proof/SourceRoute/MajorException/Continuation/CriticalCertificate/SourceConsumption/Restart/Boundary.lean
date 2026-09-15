import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.Consumer

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

theorem mixed_budget_total :
    mixedBudget .oneEach + mixedBudget .oneExceptionalTwoRegular +
      mixedBudget .twoExceptionalOneRegular = (0.00008457:ℝ) := by
  norm_num [mixedBudget]

theorem original_mixed_budget_saving :
    originalMixedBudget .oneEach + originalMixedBudget .oneExceptionalTwoRegular +
      originalMixedBudget .twoExceptionalOneRegular -
      (mixedBudget .oneEach + mixedBudget .oneExceptionalTwoRegular +
        mixedBudget .twoExceptionalOneRegular) = (0.00319547:ℝ) := by
  norm_num [mixedBudget, originalMixedBudget]

theorem retained_pure_and_mixed_budget :
    (0.00002099:ℝ)+0.0010299+0.093965+
      (mixedBudget .oneEach+mixedBudget .oneExceptionalTwoRegular+
        mixedBudget .twoExceptionalOneRegular) = 0.09510046 := by
  norm_num [mixedBudget]

theorem finite_moment_empty (s : ℝ) : totientMoment 0 s = 0 := by
  simp [totientMoment]

theorem low_endpoint_not_strict_high {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hq : 0 < q) {rho : ℂ}
    (hr : |rho.im| = omegaCutoff N q) :
    regularWeight N q rho = lowWeight N rho ∧ rho.im ≠ 0 := by
  constructor
  · simp only [regularWeight, if_pos hr.le]
  · have hp := omegaCutoff_pos hN hq
    exact abs_pos.mp (by linarith)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
