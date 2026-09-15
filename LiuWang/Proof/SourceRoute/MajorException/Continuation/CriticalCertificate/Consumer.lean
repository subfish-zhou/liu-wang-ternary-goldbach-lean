import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.PureCost

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

theorem source_conductor_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (chi : Character q) (hr : 987 ≤ (chi.conductor : ℝ)) :
    paperDomain chi.conductor (sourceL N) := by
  refine ⟨hr, sourceL_ge_3100 hN, ?_⟩
  exact (Nat.cast_le.mpr (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)).trans hq

theorem actual_pure_integrals_from_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor)
    (hgap : Real.pi/(0.4923*Real.sqrt chi.conductor*(Real.log chi.conductor)^2) ≤ 1-rho.re) :
    ‖selectedPureIntegral N .linear‖ ≤ 0.00002099*(N : ℝ)^2 ∧
      ‖selectedPureIntegral N .quadratic‖ ≤ 0.0010299*(N : ℝ)^2 ∧
      ‖selectedPureIntegral N .cubic‖ ≤ 0.093965*(N : ℝ)^2 := by
  have h := actual_pure_integrals_numeric hN hq hr
    (source_conductor_domain hN hq chi h987) hphi hgap
  exact ⟨h .linear, h .quadratic, h .cubic⟩

theorem actual_pure_integrals_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor)
    (hgap : Real.pi/(0.4923*Real.sqrt chi.conductor*(Real.log chi.conductor)^2) ≤ 1-rho.re) :
    ∀ j : PureKind, ‖selectedPureIntegral N j‖ ≤ originalPureCostBudget j*(N : ℝ)^2 := by
  have h := actual_pure_integrals_numeric hN hq hr
    (source_conductor_domain hN hq chi h987) hphi hgap
  exact fun j => (h j).trans (mul_le_mul_of_nonneg_right
    (pure_decimal_payment j).2 (sq_nonneg _))

theorem actual_exceptionalIntegral_pure_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor)
    (hgap : Real.pi/(0.4923*Real.sqrt chi.conductor*(Real.log chi.conductor)^2) ≤ 1-rho.re) :
    ‖exceptionalIntegral N‖ ≤ 0.09501589*(N : ℝ)^2 := by
  have h := actual_pure_integrals_from_source hN hq hr h987 hphi hgap
  rw [exceptionalIntegral_eq_selected (exp_2000_le_of_exp_3100_le hN)]
  have ht := (norm_add_le (selectedPureIntegral N .linear+selectedPureIntegral N .quadratic)
    (selectedPureIntegral N .cubic)).trans
    (add_le_add_left (norm_add_le (selectedPureIntegral N .linear)
      (selectedPureIntegral N .quadratic)) _)
  nlinarith [h.1, h.2.1, h.2.2]

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
