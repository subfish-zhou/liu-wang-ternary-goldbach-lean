import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.CharacterMass
import LiuWang.Proof.WeightedLowZeros.Consumer
import LiuWang.Proof.WeightedHighZeros.Consumer

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

theorem lowValues_at_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (d : PrimitiveQuadraticDatum) (hd : inducedAt d q = chi) (psi : Character q) :
    regularLowValues N psi =
      WeightedLowZeros.retainedValues psi (omegaCutoff N q) d rho := by
  rw [regularLowValues, actual_regular_deletion (exp_2000_le_of_exp_3100_le hN) hq hr]
  rw [WeightedLowZeros.retainedValues,
    WeightedLowZeros.values_low_eq_filter psi (WeightedLowZeros.omegaCutoff_le_sourceT hN), hd]
  split_ifs with hc <;> ext tau <;> simp only [Finset.mem_filter, Finset.mem_erase]
  · simp only [hc, ne_eq, not_true_eq_false, false_or]
    tauto
  · simp only [hc, ne_eq, not_false_eq_true, true_or, and_true]

theorem lowMother_at_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (d : PrimitiveQuadraticDatum) (hd : inducedAt d q = chi) :
    lowMother N q = WeightedLowZeros.retainedSum N q (omegaCutoff N q) d rho := by
  simp only [lowMother, regularLowMass, lowValues_at_source hN hq hr d hd,
    WeightedLowZeros.retainedSum, zeroMultiplicity, lowWeight, WeightedLowZeros.weight,
    baseWeight]

theorem highMother_le_closed_high (N q : ℕ) [NeZero q] :
    highMother N q ≤ WeightedHighZeros.highSum N q := by
  change (∑ psi : Character q, regularHighMass N psi) ≤
    ∑ psi : Character q, ∑ rho ∈ WeightedHighZeros.highValues N psi,
      (analyticOrderNatAt psi.LFunction rho : ℝ) * ((N:ℝ)^(rho.re-1)/|rho.im|)
  apply Finset.sum_le_sum
  intro psi _
  simp only [regularHighMass, highWeight, baseWeight]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hr, hh⟩ := Finset.mem_filter.mp hr
    rw [WeightedHighZeros.highValues_eq_complete]
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, hh.le⟩
  · intro rho _ _
    positivity

theorem original_mother_from_retained {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (d : PrimitiveQuadraticDatum) (hd : inducedAt d q = chi)
    (hlow : WeightedLowZeros.retainedSum N q (omegaCutoff N q) d rho ≤
      8.2e-10/sourceL N)
    (hhigh : WeightedHighZeros.highSum N q ≤ 0.0126*q/sourceL N^4) :
    regularMother N q ≤ 8.2e-10/sourceL N + 0.063*q/sourceL N^4 :=
  regularMother_original ((lowMother_at_source hN hq hr d hd).trans_le hlow)
    ((highMother_le_closed_high N q).trans hhigh)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
