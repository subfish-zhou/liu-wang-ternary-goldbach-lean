import LiuWang.Proof.SourceRoute.MajorException.ScalarBudget
import LiuWang.Proof.PrimePowerRemoval.Main

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorZeroInteraction LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException

example (N : ℕ) (r s t : ℂ) : finiteMoment N 0 r s t = 0 := by
  simp [finiteMoment]

example (N : ℕ) (beta : ℝ) :
    (∫ eta in -(0 : ℝ)..0, ‖Jrho N (beta : ℂ) eta‖^3) = 0 := by simp

example {N : ℕ} (hN : 0 < N) {delta : ℝ} (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, ‖Jrho N ((0.9957 : ℝ) : ℂ) eta‖^3) ≤
      (3*1.0302*1.0033^2/Real.pi)*(N : ℝ)^(3*(0.9957 : ℝ)-1) :=
  Jrho_cubic_source hN le_rfl (by norm_num) hd

example {N : ℕ} (hN : 0 < N) {delta : ℝ} (hd : 0 ≤ delta) :
    ‖finiteMoment N delta 1 1 1‖ ≤ 0.9653*(N : ℝ)^2 := by
  simpa [baseWeight] using finite_linear_source hN (beta := 1) (by norm_num) le_rfl hd

theorem regression_moebius_four : moebiusWeight 4 = 0 := by
  rw [moebiusWeight_eq, if_neg (by decide : ¬Squarefree (4 : ℕ))]

example (X : ℕ) :
    (∑ q ∈ Finset.Icc 1 X, if 4 ∣ q then moebiusWeight q/(q.totient : ℝ)^2 else 0) = 0 := by
  apply le_antisymm
  · have h := squarefree_totient_multiples X (d := 4) (by norm_num)
    rw [regression_moebius_four, zero_div, zero_mul] at h
    exact h
  · apply Finset.sum_nonneg
    intro q _
    split_ifs
    · exact div_nonneg (moebiusWeight_nonneg q) (sq_nonneg _)
    · rfl

example {q : ℕ} [NeZero q] (N : ℕ)
    (hn : ∀ chi : Character q, exceptionalValues N chi = ∅) (j : MixedKind) :
    mixedArc N q j = 0 := by
  have hz (a : ℕ) (eta : ℝ) : mixedKernel N a q eta j = 0 := by
    cases j <;> simp [mixedKernel, characterEvaluation,
      (no_exceptional_coefficient hn eta _).1]
  simp only [mixedArc, hz, zero_mul, intervalIntegral.integral_zero, Finset.sum_const_zero]

example (N a : ℕ) (eta : ℝ) (j : MixedKind) : mixedKernel N a 0 eta j = 0 := by
  simp [mixedKernel]

example (N : ℕ) (j : PureKind) : selectedPureArc N 0 j = 0 := by
  simp [selectedPureArc]

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lambdaTripleCount N - I N < (3/1000 : ℝ)*(N : ℝ)^2 :=
  PrimePowerRemoval.lambdaTripleCount_sub_I_lt_budget hN

example (N : ℕ) (alpha : ℝ) :
    S N alpha = ∑ n ∈ windowFinset N,
      (ArithmeticFunction.vonMangoldt n : ℂ)*charReal ((n : ℝ)*alpha) :=
  CompleteExpansion.S_eq_closed_sum N alpha

end LiuWang.Proof.SourceRoute.MajorException
