import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.MixedCancellation

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget

def rangePayment (N r : ℕ) (beta : ℝ) : ℝ :=
  if ¬ Nat.Coprime N r ∧ 10000 ≤ r then -0.15*(N : ℝ)^2
  else if 1600000000 ≤ r then -0.25*(N : ℝ)^2
  else -sourceCost N r beta

def automaticPayment (N r : ℕ) (beta : ℝ) : ℝ :=
  max (max (totalAllModuliExceptionalPayment N) (-sourceCost N r beta))
    (rangePayment N r beta)

theorem automaticPayment_preserves (N r : ℕ) (beta : ℝ) :
    max (totalAllModuliExceptionalPayment N) (-sharpConductorCost N r beta) ≤
      automaticPayment N r beta := by
  exact (max_le_max le_rfl (neg_le_neg (sourceCost_le_sharp N r beta))).trans (le_max_left _ _)

theorem automaticPayment_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi) :
    automaticPayment N chi.conductor rho.re ≤ (exceptionalIntegral N).re := by
  apply max_le (exceptionalIntegral_paid_source hN hq hrho)
  unfold rangePayment
  split_ifs with hc hr
  · exact (le_max_right _ _).trans
      (exceptional_non_coprime_large_paid hN hq hrho hc.2 hc.1)
  · exact (le_max_right _ _).trans (exceptional_large_paid hN hq hrho hr)
  · exact (le_max_right _ _).trans (exceptionalIntegral_paid_source hN hq hrho)

theorem automaticPayment_large {N r : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (hr : 1600000000 ≤ r) :
    -0.25*(N : ℝ)^2 ≤ automaticPayment N r beta := by
  have h := sourceCost_large hN hb hr
  exact (by linarith : -0.25*(N : ℝ)^2 ≤ -sourceCost N r beta).trans
    ((le_max_right _ _).trans (le_max_left _ _))

theorem automaticPayment_non_coprime {N r : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (hr : 10000 ≤ r) (hnc : ¬ Nat.Coprime N r) :
    -0.15*(N : ℝ)^2 ≤ automaticPayment N r beta := by
  have h := sourceCost_non_coprime_large hN hb hr hnc
  exact (by linarith : -0.15*(N : ℝ)^2 ≤ -sourceCost N r beta).trans
    ((le_max_right _ _).trans (le_max_left _ _))

theorem lambdaTripleCount_automatic {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi) :
    0.48166084*(N : ℝ)^2 + automaticPayment N chi.conductor rho.re +
      totalEnhancedRegularPayment N + (prunedHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split hN', Complex.add_re, regularHigherIntegral_pruned hN'] at h
  linarith [enhancedPayment_integral hN', automaticPayment_paid hN' hq hrho]

theorem lambdaTripleCount_non_coprime_pruned {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi)
    (hr : 10000 ≤ chi.conductor) (hnc : ¬ Nat.Coprime N chi.conductor) :
    0.33166084*(N : ℝ)^2 + totalEnhancedRegularPayment N + (prunedHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  simpa only [regularHigherIntegral_pruned (exp_2000_le_of_exp_3100_le hN)] using
    lambdaTripleCount_non_coprime_conductor hN hodd hq hrho hr hnc

theorem lambdaTripleCount_no_exception_pruned {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    0.48166084*(N : ℝ)^2 +
      totalEnhancedRegularPayment N + (prunedHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  simpa only [regularHigherIntegral_pruned (exp_2000_le_of_exp_3100_le hN)] using
    lambdaTripleCount_no_exception_direct hN hodd hnone

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget
