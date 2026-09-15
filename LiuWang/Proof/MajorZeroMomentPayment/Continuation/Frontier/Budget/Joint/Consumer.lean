import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint.MixedPayment

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.SingularIntegral LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint

def nonlinearKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩;
    let M := principalCoefficient q*J N eta
    let E := characterEvaluation (exceptionalCoefficient (q := q) N eta) a
    let R := characterEvaluation (regularCoefficient (q := q) N eta) a
    3*(M-E)*R^2 - R^3

theorem regularHigherKernel_split (N a q : ℕ) (eta : ℝ) :
    regularHigherKernel N a q eta =
      mixedLinearKernel N a q eta + nonlinearKernel N a q eta := by
  by_cases hq : q = 0
  · simp [regularHigherKernel, mixedLinearKernel, nonlinearKernel, hq]
  · simp only [regularHigherKernel, mixedLinearKernel, nonlinearKernel, dif_neg hq]
    ring

theorem continuous_nonlinear {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (nonlinearKernel N a q) := by
  by_cases hq : q = 0
  · subst q; exact continuous_const
  let : NeZero q := ⟨hq⟩
  have he : Continuous (fun eta =>
      characterEvaluation (exceptionalCoefficient (q := q) N eta) a) :=
    continuous_finsetSum _ fun chi _ => continuous_const.mul (continuous_exceptionalCoefficient hN chi)
  have hr : Continuous (fun eta =>
      characterEvaluation (regularCoefficient (q := q) N eta) a) :=
    continuous_finsetSum _ fun chi _ => continuous_const.mul (continuous_regularCoefficient hN chi)
  have hm : Continuous (fun eta => principalCoefficient q*J N eta) :=
    continuous_const.mul (continuous_J hN)
  unfold nonlinearKernel
  simp only [dif_neg hq]
  exact ((continuous_const.mul (hm.sub he)).mul (hr.pow 2)).sub (hr.pow 3)

def nonlinearIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    nonlinearKernel N i.2 i.1 eta*arcPhase N i.2 i.1 eta

theorem higherIntegral_mixed_nonlinear {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    prunedHigherIntegral N = mixedLinearIntegral N + nonlinearIntegral N := by
  rw [← regularHigherIntegral_pruned hN]
  have he : mixedLinearIntegral N =
      ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
        mixedLinearKernel N i.2 i.1 eta*arcPhase N i.2 i.1 eta := by
    rw [coreIndices, Finset.sum_sigma]
    rfl
  rw [he, nonlinearIntegral, regularHigherIntegral, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hm := ((continuous_mixedLinear (nat_pos_of_exp_le hN) i.2 i.1).mul
    (continuous_arcPhase N i.2 i.1)).intervalIntegrable
      (μ := volume) (-deltaRadius N i.1) (deltaRadius N i.1)
  have hn := ((continuous_nonlinear (nat_pos_of_exp_le hN) i.2 i.1).mul
    (continuous_arcPhase N i.2 i.1)).intervalIntegrable
      (μ := volume) (-deltaRadius N i.1) (deltaRadius N i.1)
  have hadd := intervalIntegral.integral_add hm hn
  simp only [Pi.mul_apply] at hadd
  rw [← hadd]
  congr 1
  ext eta
  simp only [regularHigherKernel_split, add_mul]

theorem mixed_none_global {N : ℕ}
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    mixedLinearIntegral N = 0 ∧ totalMixedLinearCost N = 0 := by
  constructor
  · apply Finset.sum_eq_zero
    intro q hq
    let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
    exact (mixedLinear_none (hnone q hq)).1
  · apply Finset.sum_eq_zero
    intro q hq
    let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
    exact (mixedLinear_none (hnone q hq)).2

theorem lambdaTripleCount_mixed_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi) :
    0.48166084*(N : ℝ)^2 + automaticPayment N chi.conductor rho.re +
      totalEnhancedRegularPayment N - totalMixedLinearCost N + (nonlinearIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have h := lambdaTripleCount_automatic hN hodd hq hrho
  rw [higherIntegral_mixed_nonlinear hN', Complex.add_re] at h
  linarith [mixedLinearIntegral_paid hN']

theorem lambdaTripleCount_large_mixed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi)
    (hr : 1600000000 ≤ chi.conductor) :
    0.23166084*(N : ℝ)^2 + totalEnhancedRegularPayment N -
      totalMixedLinearCost N + (nonlinearIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have h := lambdaTripleCount_large_pruned hN hodd hq hrho hr
  rw [higherIntegral_mixed_nonlinear hN', Complex.add_re] at h
  linarith [mixedLinearIntegral_paid hN']

theorem lambdaTripleCount_non_coprime_mixed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi)
    (hr : 10000 ≤ chi.conductor) (hnc : ¬ Nat.Coprime N chi.conductor) :
    0.33166084*(N : ℝ)^2 + totalEnhancedRegularPayment N -
      totalMixedLinearCost N + (nonlinearIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have h := lambdaTripleCount_non_coprime_pruned hN hodd hq hrho hr hnc
  rw [higherIntegral_mixed_nonlinear hN', Complex.add_re] at h
  linarith [mixedLinearIntegral_paid hN']

theorem lambdaTripleCount_no_exception_nonlinear {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    0.48166084*(N : ℝ)^2 + totalEnhancedRegularPayment N + (nonlinearIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have h := lambdaTripleCount_no_exception_pruned hN hodd hnone
  rwa [higherIntegral_mixed_nonlinear (exp_2000_le_of_exp_3100_le hN),
    (mixed_none_global hnone).1, zero_add] at h

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint
