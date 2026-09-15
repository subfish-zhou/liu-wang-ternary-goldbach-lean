import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint.QuadraticSign

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

theorem mixedEnvelope_le_separate {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (U V : ℂ) :
    mixedEnvelope N beta U V ≤
      ‖U‖*realEndpoint N beta + ‖V‖*(realEndpoint N beta)^2 := by
  have hv : 0 ≤ baseWeight N beta := by unfold baseWeight; positivity
  have hw := endpointGap_nonneg hN hb
  have h0 := norm_add_le (U*(baseWeight N beta : ℂ)) (V*(baseWeight N beta : ℂ)^2)
  have h1 := norm_add_le U (2*V*(baseWeight N beta : ℂ))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv,
    Complex.norm_ofNat] at h0 h1
  have hm := mul_le_mul_of_nonneg_right h1 hw
  unfold mixedEnvelope
  unfold endpointGap at *
  nlinarith

theorem mixedCoefficient_weights {q : ℕ} [NeZero q] (N : ℕ) (chi psi : Character q) :
    ‖crossCoefficient N chi psi‖ ≤
      6*‖principalCoefficient q‖*‖gaussScale chi‖*‖gaussScale psi‖*arithmeticWeight N (chi*psi) ∧
    ‖squareCoefficient N chi psi‖ ≤
      3*‖gaussScale chi‖^2*‖gaussScale psi‖*arithmeticWeight N psi := by
  constructor
  · simp only [crossCoefficient, norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (norm_phaseCoefficient_le_weight N (chi*psi)) (by positivity)
  · simp only [squareCoefficient, norm_mul, norm_pow, norm_neg, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (norm_phaseCoefficient_le_weight N psi) (by positivity)

def quadraticBonus (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : Character q, ∑ rho ∈ exceptionalValues N chi,
      if (q : ℝ) ≤ sourceP N/32 ∧ Nat.Coprime N q ∧ chi (-1) = 1 then
        max 0 (evenQuadraticPayment N chi rho.re - allModuliExceptionalPayment N q) else 0

theorem quadraticBonus_nonneg (N q : ℕ) : 0 ≤ quadraticBonus N q := by
  unfold quadraticBonus
  split_ifs
  · rfl
  · apply Finset.sum_nonneg
    intro chi _
    apply Finset.sum_nonneg
    intro rho _
    split_ifs
    · exact le_max_left _ _
    · rfl

theorem quadraticBonus_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    quadraticBonus N q =
      if (q : ℝ) ≤ sourceP N/32 ∧ Nat.Coprime N q ∧ chi (-1) = 1 then
        max 0 (evenQuadraticPayment N chi rho.re - allModuliExceptionalPayment N q) else 0 := by
  simp only [quadraticBonus, dif_neg (NeZero.ne q)]
  rw [Fintype.sum_eq_single chi]
  · rw [exceptionalValues_at_witness hN hq hr, Finset.sum_singleton]
  · intro psi hp
    rw [exceptionalValues_other_character hN hq hr hp, Finset.sum_empty]

theorem quadraticBonus_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    allModuliExceptionalPayment N q + quadraticBonus N q ≤ (exceptionalArc N q).re := by
  have ho := allModuliExceptionalPayment_lower hN hq
  by_cases hex : ∃ (chi : Character q) (rho : ℂ), rho ∈ exceptionalValues N chi
  · obtain ⟨chi, rho, hr⟩ := hex
    rw [quadraticBonus_at_witness hN hq hr]
    split_ifs with hc
    · have hp := evenQuadraticPayment_lower hN hc.1 hc.2.1 hr hc.2.2
      rw [add_max, add_zero]
      exact max_le ho (by linarith)
    · simpa only [add_zero] using ho
  · have hn : ∀ chi : Character q, exceptionalValues N chi = ∅ :=
      fun chi => Finset.eq_empty_iff_forall_notMem.mpr (fun rho hr => hex ⟨chi, rho, hr⟩)
    simpa only [quadraticBonus, dif_neg (NeZero.ne q), hn, Finset.sum_empty,
      Finset.sum_const_zero, add_zero] using ho

def creditedExceptionalPayment (N : ℕ) : ℝ :=
  totalAllModuliExceptionalPayment N + ∑ q ∈ denominators (sourceP N), quadraticBonus N q

theorem creditedExceptionalPayment_preserves (N : ℕ) :
    totalAllModuliExceptionalPayment N ≤ creditedExceptionalPayment N :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun q _ => quadraticBonus_nonneg N q))

theorem creditedExceptionalPayment_paid {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    creditedExceptionalPayment N ≤ (exceptionalIntegral N).re := by
  have he : (exceptionalIntegral N).re =
      ∑ q ∈ denominators (sourceP N), (exceptionalArc N q).re := by
    rw [exceptionalIntegral, coreIndices, Finset.sum_sigma, Complex.re_sum]
    rfl
  rw [he, creditedExceptionalPayment, totalAllModuliExceptionalPayment, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  have hq' := (mem_denominators (sourceP_pos hN).le q).mp hq
  let : NeZero q := ⟨by omega⟩
  exact quadraticBonus_paid hN hq'.2

theorem creditedExceptionalPayment_none {N : ℕ}
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    creditedExceptionalPayment N = 0 := by
  rw [creditedExceptionalPayment, allModuli_payment_no_exception hnone, zero_add]
  apply Finset.sum_eq_zero
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  simp only [quadraticBonus, dif_neg (NeZero.ne q), hnone q hq, Finset.sum_empty, Finset.sum_const_zero]

theorem lambdaTripleCount_signed_mixed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi) :
    0.48166084*(N : ℝ)^2 +
      max (automaticPayment N chi.conductor rho.re) (creditedExceptionalPayment N) +
      totalEnhancedRegularPayment N - totalMixedLinearCost N + (nonlinearIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hp := max_le (automaticPayment_paid hN' hq hrho) (creditedExceptionalPayment_paid hN')
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split hN', Complex.add_re, regularHigherIntegral_pruned hN',
    higherIntegral_mixed_nonlinear hN', Complex.add_re] at h
  linarith [enhancedPayment_integral hN', mixedLinearIntegral_paid hN']

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint
