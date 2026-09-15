import LiuWang.Proof.MajorZeroMomentPayment.Joint

/-! The actual simple R24 exceptional packet is paid by explicit endpoint
weights and signed Gauss coefficients. No per-modulus selector is introduced. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularIntegral LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment

def gaussScale {q : ℕ} [NeZero q] (chi : Character q) : ℂ :=
  (q.totient : ℂ)⁻¹ * gaussSum chi⁻¹ ZMod.stdAddChar

def linearCoefficient {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℂ :=
  -3 * principalCoefficient q^2 * gaussScale chi * phaseCoefficient N chi

def quadraticCoefficient {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℂ :=
  3 * principalCoefficient q * gaussScale chi^2 * ramanujan N q

def cubicCoefficient {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℂ :=
  -gaussScale chi^3 * phaseCoefficient N chi

def pureCoefficient (N q : ℕ) : ℂ :=
  principalCoefficient q^3 * ramanujan N q

def exceptionalArc (N q : ℕ) : ℂ :=
  ∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
    exceptionalKernel N a q eta * arcPhase N a q eta

def pureArc (N q : ℕ) : ℂ :=
  ∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
    (principalCoefficient q * J N eta)^3 * arcPhase N a q eta

theorem exceptional_coefficient_real_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (eta : ℝ) :
    exceptionalCoefficient N eta chi = gaussScale chi * Jrho N rho.re eta := by
  have hi := (exceptionalValues_quadratic_simple hN hq hr).2.2.1
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  rw [exceptionalCoefficient_at_witness hN hq hr, he]
  rfl

theorem exceptionalArc_eq_joint {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    exceptionalArc N q =
      jointFinite N (deltaRadius N q) rho.re 0
        (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi) := by
  rw [exceptionalArc, exceptional_arc_contraction hN hq hr,
    jointFinite_eq_integral (nat_pos_of_exp_le hN)]
  congr 1
  ext eta
  rw [exceptional_coefficient_real_zero hN hq hr]
  simp only [tripleKernel, Jrho_one_eq_J, linearCoefficient, quadraticCoefficient,
    cubicCoefficient]
  ring

theorem pureArc_eq_moment (N q : ℕ) :
    pureArc N q = pureCoefficient N q * finiteMoment N (deltaRadius N q) 1 1 1 := by
  unfold pureArc
  simp only [pure_kernel_eq, intervalIntegral.integral_const_mul]
  rw [← Finset.sum_mul]
  have he :
      (∑ a ∈ numerators q,
        (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)^3 *
          charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) = pureCoefficient N q := by
    rw [pureCoefficient, principalCoefficient_cube, ramanujan, Finset.mul_sum]
    rfl
  rw [he]
  congr 1
  unfold finiteMoment
  congr 1
  ext eta
  simp only [tripleKernel, Jrho_one_eq_J]
  ring

theorem pure_add_exceptional_eq_joint {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    pureArc N q + exceptionalArc N q =
      jointFinite N (deltaRadius N q) rho.re (pureCoefficient N q)
        (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi) := by
  rw [pureArc_eq_moment, exceptionalArc_eq_joint hN hq hr]
  unfold jointFinite
  ring

theorem pure_add_exceptional_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    paidLower N (deltaRadius N q) rho.re (pureCoefficient N q)
      (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi) ≤
        (pureArc N q + exceptionalArc N q).re := by
  rw [pure_add_exceptional_eq_joint hN hq hr]
  exact jointFinite_re_lower (nat_pos_of_exp_le hN)
    ((mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le)
    (deltaRadius_pos hN (NeZero.pos q)) _ _ _ _

def localExceptionalPayment (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : Character q, ∑ rho ∈ exceptionalValues N chi,
      paidLower N (deltaRadius N q) rho.re 0
        (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi)

theorem localExceptionalPayment_eq {q : ℕ} [NeZero q] (N : ℕ) :
    localExceptionalPayment N q =
      ∑ chi : Character q, ∑ rho ∈ exceptionalValues N chi,
        paidLower N (deltaRadius N q) rho.re 0
          (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi) := by
  simp only [localExceptionalPayment, dif_neg (NeZero.ne q)]

theorem localExceptionalPayment_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    localExceptionalPayment N q =
      paidLower N (deltaRadius N q) rho.re 0
        (linearCoefficient N chi) (quadraticCoefficient N chi) (cubicCoefficient N chi) := by
  rw [localExceptionalPayment_eq, Fintype.sum_eq_single chi]
  · rw [exceptionalValues_at_witness hN hq hr, Finset.sum_singleton]
  · intro psi hpsi
    rw [exceptionalValues_other_character hN hq hr hpsi, Finset.sum_empty]

theorem exceptionalArc_no_exception {q : ℕ} [NeZero q] (N : ℕ)
    (hnone : ∀ chi : Character q, exceptionalValues N chi = ∅) :
    exceptionalArc N q = 0 ∧ localExceptionalPayment N q = 0 := by
  constructor
  · unfold exceptionalArc
    apply Finset.sum_eq_zero
    intro a ha
    have he (eta : ℝ) := (interaction_no_exceptional N a eta
      (mem_numerators.mp ha).2.2 hnone).1
    simp only [he, zero_mul, intervalIntegral.integral_zero]
  · simp only [localExceptionalPayment_eq, hnone, Finset.sum_empty, Finset.sum_const_zero]

theorem exceptionalArc_re_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    localExceptionalPayment N q ≤ (exceptionalArc N q).re := by
  by_cases hex : ∃ (chi : Character q) (rho : ℂ), rho ∈ exceptionalValues N chi
  · obtain ⟨chi, rho, hr⟩ := hex
    rw [localExceptionalPayment_at_witness hN hq hr, exceptionalArc_eq_joint hN hq hr]
    exact jointFinite_re_lower (nat_pos_of_exp_le hN)
      ((mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le)
      (deltaRadius_pos hN (NeZero.pos q)) _ _ _ _
  · have hn : ∀ chi : Character q, exceptionalValues N chi = ∅ := by
      intro chi
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro rho hr
      exact hex ⟨chi, rho, hr⟩
    rw [(exceptionalArc_no_exception N hn).1, (exceptionalArc_no_exception N hn).2]
    rfl

def totalExceptionalPayment (N : ℕ) : ℝ :=
  ∑ q ∈ denominators (sourceP N), localExceptionalPayment N q

theorem exceptionalIntegral_payment {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    totalExceptionalPayment N ≤ (exceptionalIntegral N).re := by
  rw [exceptionalIntegral, coreIndices, Finset.sum_sigma]
  change totalExceptionalPayment N ≤ (∑ q ∈ denominators (sourceP N), exceptionalArc N q).re
  rw [totalExceptionalPayment, Complex.re_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hparts := (mem_denominators (sourceP_pos hN).le q).mp hq
  let : NeZero q := ⟨by omega⟩
  exact exceptionalArc_re_lower hN hparts.2

theorem lambdaTripleCount_ge_paid_exceptional {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.48166084 * (N : ℝ)^2 + totalExceptionalPayment N +
      (regularInteractionIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ lambdaTripleCount N := by
  linarith [lambdaTripleCount_ge_exceptional_regular hN hodd,
    exceptionalIntegral_payment (exp_2000_le_of_exp_3100_le hN)]

end LiuWang.Proof.MajorZeroMomentPayment
