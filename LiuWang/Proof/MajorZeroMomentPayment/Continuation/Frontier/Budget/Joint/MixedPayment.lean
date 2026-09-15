import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint.MixedMoment

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

def mixedArithmeticSum {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) (beta : ℝ) : ℝ :=
  ∑ psi : Character q,
    mixedEnvelope N beta (crossCoefficient N chi psi) (squareCoefficient N chi psi) *
      regularRhoWeight N psi

theorem mixedArithmeticSum_nonneg {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) {beta : ℝ} (hb : beta ≤ 1) :
    0 ≤ mixedArithmeticSum N chi beta :=
  Finset.sum_nonneg (fun psi _ => mul_nonneg (mixedEnvelope_nonneg hN hb _ _)
    (regularRhoWeight_nonneg N psi))

theorem mixedLinearArc_norm_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ‖mixedLinearArc N q‖ ≤
      (16/Real.pi)*(N : ℝ)^2*radiusLog N q*mixedArithmeticSum N chi rho.re := by
  rw [mixedLinearArc_moments hN hq hr, mixedArithmeticSum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro psi _
  rw [regularRhoWeight, Finset.mul_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro tau ht
  have hz := mem_zeroValues.mp (Finset.mem_filter.mp ht).1
  have ht0 : tau ≠ 0 := by intro he; simp [he] at hz
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  rw [norm_mul, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left
    (mixedMoment_actual hN (NeZero.pos q) hb hz.2.1.le ht0 _ _) (by positivity)).trans_eq
  ring

def mixedLinearCost (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (16/Real.pi)*(N : ℝ)^2*radiusLog N q*
      ∑ chi : Character q, ∑ rho ∈ exceptionalValues N chi, mixedArithmeticSum N chi rho.re

theorem mixedLinearCost_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    mixedLinearCost N q =
      (16/Real.pi)*(N : ℝ)^2*radiusLog N q*mixedArithmeticSum N chi rho.re := by
  simp only [mixedLinearCost, dif_neg (NeZero.ne q)]
  rw [Fintype.sum_eq_single chi]
  · rw [exceptionalValues_at_witness hN hq hr, Finset.sum_singleton]
  · intro psi hp
    rw [exceptionalValues_other_character hN hq hr hp, Finset.sum_empty]

theorem mixedLinear_none {N q : ℕ} [NeZero q]
    (hnone : ∀ chi : Character q, exceptionalValues N chi = ∅) :
    mixedLinearArc N q = 0 ∧ mixedLinearCost N q = 0 := by
  constructor
  · have he (a : ℕ) (eta : ℝ) : mixedLinearKernel N a q eta = 0 := by
      simp only [mixedLinearKernel, dif_neg (NeZero.ne q), characterEvaluation,
        (no_exceptional_coefficient hnone eta _).1, mul_zero, Finset.sum_const_zero,
        zero_pow (by norm_num : 2 ≠ 0), zero_mul, sub_zero]
    simp only [mixedLinearArc, he, zero_mul, intervalIntegral.integral_zero, Finset.sum_const_zero]
  · simp only [mixedLinearCost, dif_neg (NeZero.ne q), hnone, Finset.sum_empty,
      Finset.sum_const_zero, mul_zero]

theorem mixedLinearArc_norm {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    ‖mixedLinearArc N q‖ ≤ mixedLinearCost N q := by
  by_cases hex : ∃ (chi : Character q) (rho : ℂ), rho ∈ exceptionalValues N chi
  · obtain ⟨chi, rho, hr⟩ := hex
    rw [mixedLinearCost_at_witness hN hq hr]
    exact mixedLinearArc_norm_at_witness hN hq hr
  · have hn : ∀ chi : Character q, exceptionalValues N chi = ∅ :=
      fun chi => Finset.eq_empty_iff_forall_notMem.mpr (fun rho hr => hex ⟨chi, rho, hr⟩)
    rw [(mixedLinear_none hn).1, (mixedLinear_none hn).2, norm_zero]

theorem mixedLinearArc_weighted_budget {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    {b : ℝ} (hb : mixedArithmeticSum N chi rho.re ≤ b) :
    ‖mixedLinearArc N q‖ ≤ 5.1*(N : ℝ)^2*radiusLog N q*b := by
  have hnon := mixedArithmeticSum_nonneg (nat_pos_of_exp_le hN) chi
    (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  have hc : (16 : ℝ)/Real.pi ≤ 5.1 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_d4]
  apply (mixedLinearArc_norm_at_witness hN hq hr).trans
  apply mul_le_mul _ hb hnon (by have := radiusLog_nonneg (q := q) hN; positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ))) (radiusLog_nonneg hN)

def mixedLinearIntegral (N : ℕ) : ℂ :=
  ∑ q ∈ denominators (sourceP N), mixedLinearArc N q

def totalMixedLinearCost (N : ℕ) : ℝ :=
  ∑ q ∈ denominators (sourceP N), mixedLinearCost N q

theorem mixedLinearIntegral_paid {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    -totalMixedLinearCost N ≤ (mixedLinearIntegral N).re := by
  have hn : ‖mixedLinearIntegral N‖ ≤ totalMixedLinearCost N := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q hq
    have hq' := (mem_denominators (sourceP_pos hN).le q).mp hq
    let : NeZero q := ⟨by omega⟩
    exact mixedLinearArc_norm hN hq'.2
  have h := Complex.re_le_norm (-mixedLinearIntegral N)
  rw [Complex.neg_re, norm_neg] at h
  linarith

theorem cross_off_diagonal_divisor_zero {N q : ℕ} [NeZero q] (hd : q ∣ N)
    (chi : Character q) (beta : ℝ) :
    (∑ psi : Character q, if psi = chi⁻¹ then 0 else
      ∑ tau ∈ regularValues N psi, (analyticOrderNatAt psi.LFunction tau : ℂ) *
        crossCoefficient N chi psi*finiteMoment N (deltaRadius N q) 1 beta tau) = 0 := by
  apply Finset.sum_eq_zero
  intro psi _
  split_ifs with hp
  · rfl
  · simp only [crossCoefficient_divisor_zero hd chi psi hp, mul_zero, zero_mul, Finset.sum_const_zero]

theorem mixedLinearArc_divisor {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (hd : q ∣ N) :
    mixedLinearArc N q =
      crossCoefficient N chi chi⁻¹ *
        (∑ tau ∈ regularValues N chi⁻¹, (analyticOrderNatAt chi⁻¹.LFunction tau : ℂ) *
          finiteMoment N (deltaRadius N q) 1 rho.re tau) +
      squareCoefficient N chi 1 *
        (∑ tau ∈ regularValues N (1 : Character q),
          (analyticOrderNatAt (1 : Character q).LFunction tau : ℂ) *
            finiteMoment N (deltaRadius N q) rho.re rho.re tau) := by
  rw [mixedLinearArc_moments hN hq hr]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_eq_single chi⁻¹, Finset.mul_sum]
    · apply Finset.sum_congr rfl
      intro tau _
      ring
    · intro psi hp
      simp only [crossCoefficient_divisor_zero hd chi psi hp, zero_mul, mul_zero, Finset.sum_const_zero]
  · rw [Fintype.sum_eq_single (1 : Character q), Finset.mul_sum]
    · apply Finset.sum_congr rfl
      intro tau _
      ring
    · intro psi hp
      simp only [squareCoefficient, phaseCoefficient_vanishes hd hp,
        mul_zero, zero_mul, Finset.sum_const_zero]

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint
