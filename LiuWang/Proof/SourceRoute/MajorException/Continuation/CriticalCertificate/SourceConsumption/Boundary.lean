import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Consumer

set_option autoImplicit false
noncomputable section
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

theorem height_boundary_is_low {N q : ℕ} [NeZero q]
    {chi : Character q} {rho : ℂ} (hr : rho ∈ regularValues N chi)
    (he : |rho.im| = omegaCutoff N q) :
    rho ∈ regularLowValues N chi ∧ rho ∉ regularHighValues N chi := by
  simp [regularLowValues, regularHighValues, hr, he]

theorem high_weight_never_divides_by_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ regularHighValues N chi) : rho.im ≠ 0 :=
  abs_pos.mp ((omegaCutoff_pos hN (NeZero.pos q)).trans (Finset.mem_filter.mp hr).2)

theorem actual_order_kept {q : ℕ} [NeZero q] (chi : Character q) (rho : ℂ)
    {m : ℕ} (hm : analyticOrderNatAt chi.LFunction rho = m) :
    ‖regularAmplitude chi rho‖ = ‖gaussScale chi‖*(m : ℝ) := by
  rw [norm_regularAmplitude, hm]

theorem frozen_pure_amounts_retained :
    pureCostBudget .linear = 0.00002099 ∧ pureCostBudget .quadratic = 0.0010299 ∧
      pureCostBudget .cubic = 0.093965 := by
  norm_num [pureCostBudget]

theorem no_exception_cost_zero {q : ℕ} [NeZero q] (N : ℕ)
    (hn : ∀ chi : Character q, LiuWang.Proof.MajorZeroInteraction.exceptionalValues N chi = ∅)
    (j : MixedKind) : selectedMixedCost N q j = 0 := by
  simp [selectedMixedCost, NeZero.ne q, hn]

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
