import LiuWang.Proof.SourceRoute.MajorException.MixedPhases

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException

def regularAmplitude {q : ℕ} [NeZero q] (psi : Character q) (rho : ℂ) : ℂ :=
  gaussScale psi * (analyticOrderNatAt psi.LFunction rho : ℂ)

theorem regularCoefficient_eq_amplitudes {q : ℕ} [NeZero q]
    (N : ℕ) (psi : Character q) (eta : ℝ) :
    regularCoefficient N eta psi =
      ∑ rho ∈ regularValues N psi, regularAmplitude psi rho * Jrho N rho eta := by
  simp only [regularCoefficient, regularAmplitude, regularValues, gaussScale, Finset.mul_sum,
    mul_assoc]

theorem single_regular_moment {N q : ℕ} [NeZero q] (hN : 0 < N)
    (psi : Character q) (r s C : ℂ) (delta : ℝ) :
    (∫ eta in -delta..delta,
      C*Jrho N r eta*Jrho N s eta*regularCoefficient N eta psi*
        charReal (-(N : ℝ)*eta)) =
      ∑ rho ∈ regularValues N psi,
        (C*regularAmplitude psi rho)*finiteMoment N delta r s rho := by
  have hp (eta : ℝ) :
      C*Jrho N r eta*Jrho N s eta*regularCoefficient N eta psi*
        charReal (-(N : ℝ)*eta) =
      ∑ rho ∈ regularValues N psi,
        (C*regularAmplitude psi rho)*tripleKernel N r s rho eta := by
    rw [regularCoefficient_eq_amplitudes]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro rho _
    unfold tripleKernel
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum
    (f := fun rho eta => (C*regularAmplitude psi rho)*tripleKernel N r s rho eta)
    (fun rho _ => (continuous_const.mul (continuous_tripleKernel hN r s rho)).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, finiteMoment]

theorem double_regular_moment {N q : ℕ} [NeZero q] (hN : 0 < N)
    (psi tau : Character q) (r C : ℂ) (delta : ℝ) :
    (∫ eta in -delta..delta,
      C*Jrho N r eta*regularCoefficient N eta psi*regularCoefficient N eta tau*
        charReal (-(N : ℝ)*eta)) =
      ∑ rho ∈ regularValues N psi, ∑ sigma ∈ regularValues N tau,
        (C*regularAmplitude psi rho*regularAmplitude tau sigma)*
          finiteMoment N delta r rho sigma := by
  have hp (eta : ℝ) :
      C*Jrho N r eta*regularCoefficient N eta psi*regularCoefficient N eta tau*
        charReal (-(N : ℝ)*eta) =
      ∑ rho ∈ regularValues N psi, ∑ sigma ∈ regularValues N tau,
        (C*regularAmplitude psi rho*regularAmplitude tau sigma)*
          tripleKernel N r rho sigma eta := by
    simp only [regularCoefficient_eq_amplitudes, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro rho _
    apply Finset.sum_congr rfl
    intro sigma _
    unfold tripleKernel
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum
    (f := fun rho eta => ∑ sigma ∈ regularValues N tau,
      (C*regularAmplitude psi rho*regularAmplitude tau sigma)*tripleKernel N r rho sigma eta)
    (fun rho _ => (continuous_finsetSum _ (fun sigma _ =>
      continuous_const.mul (continuous_tripleKernel hN r rho sigma))).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro rho _
  rw [intervalIntegral.integral_finsetSum
    (f := fun sigma eta =>
      (C*regularAmplitude psi rho*regularAmplitude tau sigma)*tripleKernel N r rho sigma eta)
    (fun sigma _ =>
      (continuous_const.mul (continuous_tripleKernel hN r rho sigma)).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, finiteMoment]

theorem mixed_one_each_moments {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    mixedArc N q .oneEach =
      ∑ psi : Character q, ∑ tau ∈ regularValues N psi,
        (6*principalCoefficient q*gaussScale chi*phaseCoefficient N (chi*psi)*
          regularAmplitude psi tau)*finiteMoment N (deltaRadius N q) 1 rho.re tau := by
  have hn := nat_pos_of_exp_le hN
  rw [mixedArc_contract hn]
  simp_rw [mixed_one_each_contraction hN hq hr, Finset.sum_mul,
    exceptional_coefficient_real_zero hN hq hr]
  rw [intervalIntegral.integral_finsetSum
    (f := fun psi eta => (6*(principalCoefficient q*J N eta)*
      (gaussScale chi*Jrho N rho.re eta)*regularCoefficient N eta psi*
        phaseCoefficient N (chi*psi))*charReal (-(N : ℝ)*eta))
    (fun psi _ => by
      apply Continuous.intervalIntegrable
      have hj := continuous_J hn
      have he := Jrho_continuous hn (rho.re : ℂ)
      have hp := continuous_regularCoefficient hn psi
      have hc : Continuous (fun eta : ℝ => charReal (-(N : ℝ)*eta)) :=
        charReal_continuous.comp (continuous_const.mul continuous_id)
      fun_prop)]
  apply Finset.sum_congr rfl
  intro psi _
  rw [← single_regular_moment hn psi 1 rho.re
    (6*principalCoefficient q*gaussScale chi*phaseCoefficient N (chi*psi))]
  congr 1
  ext eta
  rw [Jrho_one_eq_J]
  ring

theorem mixed_two_exceptional_moments {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    mixedArc N q .twoExceptionalOneRegular =
      ∑ psi : Character q, ∑ tau ∈ regularValues N psi,
        (-3*gaussScale chi^2*phaseCoefficient N psi*regularAmplitude psi tau)*
          finiteMoment N (deltaRadius N q) rho.re rho.re tau := by
  have hn := nat_pos_of_exp_le hN
  rw [mixedArc_contract hn]
  simp_rw [mixed_two_exceptional_contraction hN hq hr, Finset.sum_mul,
    exceptional_coefficient_real_zero hN hq hr]
  rw [intervalIntegral.integral_finsetSum
    (f := fun psi eta => (-3*(gaussScale chi*Jrho N rho.re eta)^2*
      regularCoefficient N eta psi*phaseCoefficient N psi)*charReal (-(N : ℝ)*eta))
    (fun psi _ => by
      apply Continuous.intervalIntegrable
      have he := Jrho_continuous hn (rho.re : ℂ)
      have hp := continuous_regularCoefficient hn psi
      have hc : Continuous (fun eta : ℝ => charReal (-(N : ℝ)*eta)) :=
        charReal_continuous.comp (continuous_const.mul continuous_id)
      fun_prop)]
  apply Finset.sum_congr rfl
  intro psi _
  rw [← single_regular_moment hn psi rho.re rho.re
    (-3*gaussScale chi^2*phaseCoefficient N psi)]
  congr 1
  ext eta
  ring

theorem mixed_one_exceptional_moments {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    mixedArc N q .oneExceptionalTwoRegular =
      ∑ psi : Character q, ∑ tau : Character q,
        ∑ sigma ∈ regularValues N psi, ∑ omega ∈ regularValues N tau,
          (-3*gaussScale chi*phaseCoefficient N (chi*psi*tau)*
            regularAmplitude psi sigma*regularAmplitude tau omega)*
              finiteMoment N (deltaRadius N q) rho.re sigma omega := by
  have hn := nat_pos_of_exp_le hN
  have hc : Continuous (fun eta : ℝ => charReal (-(N : ℝ)*eta)) :=
    charReal_continuous.comp (continuous_const.mul continuous_id)
  have he := Jrho_continuous hn (rho.re : ℂ)
  have hf (psi tau : Character q) : Continuous (fun eta =>
      (-3*(gaussScale chi*Jrho N rho.re eta)*regularCoefficient N eta psi*
        regularCoefficient N eta tau*phaseCoefficient N (chi*psi*tau))*
          charReal (-(N : ℝ)*eta)) := by
    have hp := continuous_regularCoefficient hn psi
    have ht := continuous_regularCoefficient hn tau
    fun_prop
  rw [mixedArc_contract hn]
  simp_rw [mixed_one_exceptional_contraction hN hq hr, Finset.sum_mul,
    exceptional_coefficient_real_zero hN hq hr]
  rw [intervalIntegral.integral_finsetSum
    (f := fun psi eta => ∑ tau : Character q,
      (-3*(gaussScale chi*Jrho N rho.re eta)*regularCoefficient N eta psi*
        regularCoefficient N eta tau*phaseCoefficient N (chi*psi*tau))*
          charReal (-(N : ℝ)*eta))
    (fun psi _ => (continuous_finsetSum _ (fun tau _ => hf psi tau)).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro psi _
  rw [intervalIntegral.integral_finsetSum (fun tau _ => (hf psi tau).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro tau _
  rw [← double_regular_moment hn psi tau rho.re
    (-3*gaussScale chi*phaseCoefficient N (chi*psi*tau))]
  congr 1
  ext eta
  ring

theorem mixed_one_exceptional_divisor {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (hd : q ∣ N) :
    mixedArc N q .oneExceptionalTwoRegular =
      ∑ psi : Character q,
        ∑ sigma ∈ regularValues N psi, ∑ omega ∈ regularValues N ((chi*psi)⁻¹),
          (-3*gaussScale chi*SingularSeries.ramanujan N q*
            regularAmplitude psi sigma*regularAmplitude ((chi*psi)⁻¹) omega)*
              finiteMoment N (deltaRadius N q) rho.re sigma omega := by
  rw [mixed_one_exceptional_moments hN hq hr]
  apply Finset.sum_congr rfl
  intro psi _
  rw [Fintype.sum_eq_single ((chi*psi)⁻¹)]
  · rw [mul_inv_cancel, phaseCoefficient_principal]
  · intro tau hne
    have hc : chi*psi*tau ≠ 1 := by
      intro he
      have ht := congrArg (fun z : Character q => (chi*psi)⁻¹*z) he
      simp only [inv_mul_cancel_left, mul_one] at ht
      exact hne ht
    simp only [phaseCoefficient_vanishes hd hc, mul_zero, zero_mul, Finset.sum_const_zero]

end LiuWang.Proof.SourceRoute.MajorException
