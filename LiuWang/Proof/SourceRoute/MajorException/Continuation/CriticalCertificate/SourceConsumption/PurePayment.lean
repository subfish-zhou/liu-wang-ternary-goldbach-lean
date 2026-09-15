import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.ActualGap

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

theorem actual_pure_totals {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor) :
    ∀ j : PureKind,
      (∑ s ∈ denominators (sourceP N), ‖selectedPureArc N s j‖) ≤
        pureCostBudget j*(N : ℝ)^2 :=
  actual_pure_totals_numeric hN hq hr (source_conductor_domain hN hq chi h987) hphi
    (actual_exceptional_gap (exp_2000_le_of_exp_3100_le hN) hq hr h987)

theorem actual_pure_integrals {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor) :
    ‖selectedPureIntegral N .linear‖ ≤ 0.00002099*(N : ℝ)^2 ∧
      ‖selectedPureIntegral N .quadratic‖ ≤ 0.0010299*(N : ℝ)^2 ∧
      ‖selectedPureIntegral N .cubic‖ ≤ 0.093965*(N : ℝ)^2 :=
  actual_pure_integrals_from_source hN hq hr h987 hphi
    (actual_exceptional_gap (exp_2000_le_of_exp_3100_le hN) hq hr h987)

theorem actual_pure_original_budgets {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor) :
    ∀ j : PureKind, ‖selectedPureIntegral N j‖ ≤ originalPureCostBudget j*(N : ℝ)^2 :=
  actual_pure_integrals_original hN hq hr h987 hphi
    (actual_exceptional_gap (exp_2000_le_of_exp_3100_le hN) hq hr h987)

theorem actual_pure_aggregate {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor) :
    ‖exceptionalIntegral N‖ ≤ 0.09501589*(N : ℝ)^2 :=
  actual_exceptionalIntegral_pure_bound hN hq hr h987 hphi
    (actual_exceptional_gap (exp_2000_le_of_exp_3100_le hN) hq hr h987)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
