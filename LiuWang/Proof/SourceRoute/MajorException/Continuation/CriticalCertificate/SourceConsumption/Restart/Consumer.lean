import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.DecimalPayment

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

theorem actual_mixed_totals_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor:ℝ))
    (hphi : (chi.conductor:ℝ)/(chi.conductor.totient:ℝ) ≤ nu chi.conductor) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      WeightedLowZeros.Continuation.PaperSource N d rho ∧
      ((∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedLowZeros.retainedSum N s (omegaCutoff N s) d rho ≤ 8.2e-10/sourceL N) →
      (∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedHighZeros.highSum N s ≤ 0.0126*s/sourceL N^4) →
      ∀ j : MixedKind, totalMixedCost N j ≤ mixedBudget j*(N:ℝ)^2) := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  obtain ⟨d, hdc, hs, h⟩ := common_source_normalization hN hq hr
  refine ⟨d, hdc, hs, ?_⟩
  intro hlow hhigh j
  have hd : paperDomain d.modulus (sourceL N) := by
    rw [hdc]
    exact source_conductor_domain hN hq chi h987
  have hp : (d.modulus:ℝ)/(d.modulus.totient:ℝ) ≤ nu d.modulus := by
    simpa only [hdc] using hphi
  have hg : Real.pi/(0.4923*Real.sqrt d.modulus*(Real.log d.modulus)^2) ≤ 1-rho.re := by
    simpa only [hdc] using actual_exceptional_gap hN' hq hr h987
  exact ((h hlow hhigh j).trans
    (normalizedTotal_le_analytic hN' d.modulus_pos rho.re j)).trans
    (analyticCost_numeric hN hd hp hg (exceptional_beta_source_range hN' hr).2 j)

theorem actual_mixed_integrals_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor:ℝ))
    (hphi : (chi.conductor:ℝ)/(chi.conductor.totient:ℝ) ≤ nu chi.conductor) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      WeightedLowZeros.Continuation.PaperSource N d rho ∧
      ((∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedLowZeros.retainedSum N s (omegaCutoff N s) d rho ≤ 8.2e-10/sourceL N) →
      (∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedHighZeros.highSum N s ≤ 0.0126*s/sourceL N^4) →
      ∀ j : MixedKind, ‖mixedIntegral N j‖ ≤ mixedBudget j*(N:ℝ)^2) := by
  obtain ⟨d, hdc, hs, h⟩ := actual_mixed_totals_paid hN hq hr h987 hphi
  exact ⟨d, hdc, hs, fun hl hh j =>
    (actual_mixed_integrals (exp_2000_le_of_exp_3100_le hN) j).trans (h hl hh j)⟩

theorem major_lower_without_mixed_mothers {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hodd : Odd N) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor:ℝ))
    (hphi : (chi.conductor:ℝ)/(chi.conductor.totient:ℝ) ≤ nu chi.conductor) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      WeightedLowZeros.Continuation.PaperSource N d rho ∧
      ((∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedLowZeros.retainedSum N s (omegaCutoff N s) d rho ≤ 8.2e-10/sourceL N) →
      (∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedHighZeros.highSum N s ≤ 0.0126*s/sourceL N^4) →
      0.56106954*(N:ℝ)^2+(ordinaryIntegral N).re-
        6760*(N:ℝ)^2/sourceL N^4 ≤ (majorIntegral N).re) := by
  obtain ⟨d, hdc, hs, h⟩ := actual_mixed_totals_paid hN hq hr h987 hphi
  refine ⟨d, hdc, hs, ?_⟩
  intro hl hh
  have h1 := h hl hh .oneEach
  have h2 := h hl hh .oneExceptionalTwoRegular
  have h3 := h hl hh .twoExceptionalOneRegular
  simp only [mixedBudget] at h1 h2 h3
  have hm := major_lower_with_actual_remaining_masses hN hodd hq hr h987 hphi
  linarith

theorem source_expansion_error_payment {N : ℕ} (hN : Real.exp 3100 ≤ (N:ℝ)) :
    6760*(N:ℝ)^2/sourceL N^4 ≤ 0.000000000074*(N:ℝ)^2 := by
  have hL := sourceL_ge_3100 hN
  have h0 : 0 < sourceL N := by linarith
  have h4 : (3100:ℝ)^4 ≤ sourceL N^4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hcoef : 6760/sourceL N^4 ≤ (0.000000000074:ℝ) := by
    apply (div_le_iff₀ (pow_pos h0 4)).mpr
    nlinarith
  calc
    _ = (6760/sourceL N^4)*(N:ℝ)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (N:ℝ))

theorem caseII_of_original_low_high_and_ordinary {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hodd : Odd N) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor:ℝ))
    (hphi : (chi.conductor:ℝ)/(chi.conductor.totient:ℝ) ≤ nu chi.conductor)
    (hordinary : -(0.00000009*(N:ℝ)^2) ≤ (ordinaryIntegral N).re) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      WeightedLowZeros.Continuation.PaperSource N d rho ∧
      ((∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedLowZeros.retainedSum N s (omegaCutoff N s) d rho ≤ 8.2e-10/sourceL N) →
      (∀ (s : ℕ) [NeZero s], (s:ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedHighZeros.highSum N s ≤ 0.0126*s/sourceL N^4) →
      0.5577*(N:ℝ)^2 ≤ (majorIntegral N).re) := by
  obtain ⟨d, hdc, hs, h⟩ := major_lower_without_mixed_mothers hN hodd hq hr h987 hphi
  refine ⟨d, hdc, hs, ?_⟩
  intro hl hh
  have hm := h hl hh
  have he := source_expansion_error_payment hN
  nlinarith [sq_nonneg (N:ℝ)]

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
