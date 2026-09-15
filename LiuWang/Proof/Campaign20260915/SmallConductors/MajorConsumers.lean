import LiuWang.Proof.Campaign20260915.SmallConductors.Through986
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.Consumer

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.SourceRoute.MajorException
open LiuWang.Proof.SourceRoute.MajorException.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem actual_exceptional_conductor_ge_987_real {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    987 ≤ (chi.conductor : ℝ) := by
  exact_mod_cast actual_exceptional_conductor_ge_987 hN hq hr

theorem actual_exceptional_gap_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    Real.pi / (0.4923 * Real.sqrt chi.conductor * (Real.log chi.conductor) ^ 2) ≤
      1 - rho.re :=
  SourceConsumption.actual_exceptional_gap (exp_2000_le_of_exp_3100_le hN) hq hr
    (actual_exceptional_conductor_ge_987_real hN hq hr)

theorem actual_pure_integrals_conductor_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hphi : (chi.conductor : ℝ) / (chi.conductor.totient : ℝ) ≤ nu chi.conductor) :
    ‖selectedPureIntegral N .linear‖ ≤ 0.00002099 * (N : ℝ) ^ 2 ∧
      ‖selectedPureIntegral N .quadratic‖ ≤ 0.0010299 * (N : ℝ) ^ 2 ∧
      ‖selectedPureIntegral N .cubic‖ ≤ 0.093965 * (N : ℝ) ^ 2 :=
  SourceConsumption.actual_pure_integrals hN hq hr
    (actual_exceptional_conductor_ge_987_real hN hq hr) hphi

theorem actual_mixed_totals_conductor_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hphi : (chi.conductor : ℝ) / (chi.conductor.totient : ℝ) ≤ nu chi.conductor) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      WeightedLowZeros.Continuation.PaperSource N d rho ∧
      ((∀ (s : ℕ) [NeZero s], (s : ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedLowZeros.retainedSum N s (omegaCutoff N s) d rho ≤ 8.2e-10 / sourceL N) →
      (∀ (s : ℕ) [NeZero s], (s : ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedHighZeros.highSum N s ≤ 0.0126 * s / sourceL N ^ 4) →
      ∀ j : MixedKind, totalMixedCost N j ≤ mixedBudget j * (N : ℝ) ^ 2) :=
  SourceConsumption.Restart.actual_mixed_totals_paid hN hq hr
    (actual_exceptional_conductor_ge_987_real hN hq hr) hphi

theorem caseII_conductor_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hphi : (chi.conductor : ℝ) / (chi.conductor.totient : ℝ) ≤ nu chi.conductor)
    (hordinary : -(0.00000009 * (N : ℝ) ^ 2) ≤ (ordinaryIntegral N).re) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      WeightedLowZeros.Continuation.PaperSource N d rho ∧
      ((∀ (s : ℕ) [NeZero s], (s : ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedLowZeros.retainedSum N s (omegaCutoff N s) d rho ≤ 8.2e-10 / sourceL N) →
      (∀ (s : ℕ) [NeZero s], (s : ℝ) ≤ sourceP N → d.modulus ∣ s →
        WeightedHighZeros.highSum N s ≤ 0.0126 * s / sourceL N ^ 4) →
      0.5577 * (N : ℝ) ^ 2 ≤ (majorIntegral N).re) :=
  SourceConsumption.Restart.caseII_of_original_low_high_and_ordinary hN hodd hq hr
    (actual_exceptional_conductor_ge_987_real hN hq hr) hphi hordinary

#print axioms actual_exceptional_conductor_ge_987_real
#print axioms actual_exceptional_gap_paid
#print axioms actual_pure_integrals_conductor_paid
#print axioms actual_mixed_totals_conductor_paid
#print axioms caseII_conductor_paid

end LiuWang.Proof.Campaign20260915.SmallConductors
