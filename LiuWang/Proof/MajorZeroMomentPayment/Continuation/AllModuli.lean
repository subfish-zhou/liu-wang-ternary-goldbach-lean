import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Shifted
import LiuWang.Proof.MajorZeroMomentPayment.Continuation.RegularLinear

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation

def shiftedExceptionalPayment (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : Character q, ∑ rho ∈ exceptionalValues N chi,
      -0.955 * (N : ℝ)^2 *
        shiftedEnvelope (baseWeight N rho.re) (endpointGap N rho.re) 0
          (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi)

theorem shiftedExceptionalPayment_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    shiftedExceptionalPayment N q =
      -0.955 * (N : ℝ)^2 *
        shiftedEnvelope (baseWeight N rho.re) (endpointGap N rho.re) 0
          (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi) := by
  simp only [shiftedExceptionalPayment, dif_neg (NeZero.ne q)]
  rw [Fintype.sum_eq_single chi]
  · rw [exceptionalValues_at_witness hN hq hr, Finset.sum_singleton]
  · intro psi hpsi
    rw [exceptionalValues_other_character hN hq hr hpsi, Finset.sum_empty]

theorem shiftedExceptionalPayment_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    shiftedExceptionalPayment N q ≤ (exceptionalArc N q).re := by
  by_cases hex : ∃ (chi : Character q) (rho : ℂ), rho ∈ exceptionalValues N chi
  · obtain ⟨chi, rho, hr⟩ := hex
    rw [shiftedExceptionalPayment_at_witness hN hq hr, exceptionalArc_eq_joint hN hq hr]
    exact jointFinite_shift_lower_decimal (nat_pos_of_exp_le hN)
      (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
      (deltaRadius_pos hN (NeZero.pos q)).le _ _ _ _
  · have hn : ∀ chi : Character q, exceptionalValues N chi = ∅ := by
      intro chi
      exact Finset.eq_empty_iff_forall_notMem.mpr (fun rho hr => hex ⟨chi, rho, hr⟩)
    rw [(exceptionalArc_no_exception N hn).1]
    simp [shiftedExceptionalPayment, NeZero.ne q, hn]

def allModuliExceptionalPayment (N q : ℕ) : ℝ :=
  max (localExceptionalPayment N q) (shiftedExceptionalPayment N q)

theorem allModuliExceptionalPayment_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    allModuliExceptionalPayment N q ≤ (exceptionalArc N q).re :=
  max_le (exceptionalArc_re_lower hN hq) (shiftedExceptionalPayment_lower hN hq)

def totalAllModuliExceptionalPayment (N : ℕ) : ℝ :=
  ∑ q ∈ denominators (sourceP N), allModuliExceptionalPayment N q

theorem allModuli_payment_preserves_signed (N : ℕ) :
    totalExceptionalPayment N ≤ totalAllModuliExceptionalPayment N := by
  exact Finset.sum_le_sum (fun q _ => le_max_left (localExceptionalPayment N q)
    (shiftedExceptionalPayment N q))

theorem exceptionalIntegral_allModuli_payment {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    totalAllModuliExceptionalPayment N ≤ (exceptionalIntegral N).re := by
  rw [exceptionalIntegral, coreIndices, Finset.sum_sigma]
  change totalAllModuliExceptionalPayment N ≤ (∑ q ∈ denominators (sourceP N), exceptionalArc N q).re
  rw [totalAllModuliExceptionalPayment, Complex.re_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hp := (mem_denominators (sourceP_pos hN).le q).mp hq
  let : NeZero q := ⟨by omega⟩
  exact allModuliExceptionalPayment_lower hN hp.2

theorem allModuli_payment_no_exception {N : ℕ}
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    totalAllModuliExceptionalPayment N = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  have hn := hnone q hq
  have hp := (exceptionalArc_no_exception N hn).2
  simp [allModuliExceptionalPayment, hp, shiftedExceptionalPayment, NeZero.ne q, hn]

theorem actual_finite_linear_high {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : 0 < q) {rho : ℂ} (hr : 1/2 ≤ rho.re) (hr' : rho.re < 1)
    (hg : 0 < |rho.im|) :
    ‖finiteMoment N (deltaRadius N q) 1 1 rho‖ ≤
      (N : ℝ)^2 * baseWeight N rho.re * (1 / |rho.im|^2 + 0.033 / |rho.im|) +
        100 / 3.36^2 * ((q : ℝ) / sourceP N)^2 * (N : ℝ)^2 *
          explicitVariation N rho := by
  have h := norm_add_le
    (finiteMoment N (deltaRadius N q) 1 1 rho - linearValue N rho) (linearValue N rho)
  rw [sub_add_cancel] at h
  linarith [actual_linear_tail hN hq (by linarith : 0 < rho.re) hr',
    full_linear_high (nat_pos_of_exp_le hN) hr hg]

theorem lambdaTripleCount_allModuli_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.48166084 * (N : ℝ)^2 + totalAllModuliExceptionalPayment N +
      totalRegularLinearPayment N + (regularHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ lambdaTripleCount N := by
  have h := lambdaTripleCount_ge_exceptional_regular hN hodd
  rw [regularIntegral_split (exp_2000_le_of_exp_3100_le hN), Complex.add_re] at h
  linarith [exceptionalIntegral_allModuli_payment (exp_2000_le_of_exp_3100_le hN),
    regularLinearIntegral_payment (exp_2000_le_of_exp_3100_le hN)]

theorem lambdaTripleCount_allModuli_paid_decimal {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.481660839 * (N : ℝ)^2 + totalAllModuliExceptionalPayment N +
      totalRegularLinearPayment N + (regularHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re ≤ lambdaTripleCount N := by
  linarith [lambdaTripleCount_allModuli_paid hN hodd,
    log_power_le_decimal (exp_2000_le_of_exp_3100_le hN)]

end LiuWang.Proof.MajorZeroMomentPayment.Continuation
