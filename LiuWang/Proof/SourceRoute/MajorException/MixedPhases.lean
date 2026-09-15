import LiuWang.Proof.SourceRoute.MajorException.PureTerms
import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.MixedCancellation

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException

theorem phase_evaluation {q : ℕ} [NeZero q] (N : ℕ)
    (f : Character q → ℂ) :
    (∑ a ∈ numerators q, characterEvaluation f a *
      charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      ∑ chi : Character q, f chi * phaseCoefficient N chi := by
  simp only [characterEvaluation, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro chi _
  rw [phaseCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem phase_twisted_evaluation {q : ℕ} [NeZero q] (N : ℕ)
    (chi : Character q) (f : Character q → ℂ) :
    (∑ a ∈ numerators q, chi (a : ZMod q) * characterEvaluation f a *
      charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      ∑ psi : Character q, f psi * phaseCoefficient N (chi*psi) := by
  simp only [characterEvaluation, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  rw [phaseCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [MulChar.mul_apply]
  ring

theorem phase_twisted_product {q : ℕ} [NeZero q] (N : ℕ)
    (chi : Character q) (f g : Character q → ℂ) :
    (∑ a ∈ numerators q,
      chi (a : ZMod q) * characterEvaluation f a * characterEvaluation g a *
        charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      ∑ psi : Character q, ∑ tau : Character q,
        f psi * g tau * phaseCoefficient N (chi*psi*tau) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [characterEvaluation, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tau _
  rw [phaseCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [MulChar.mul_apply]
  ring

theorem phase_twisted_product_divisor {N q : ℕ} [NeZero q] (hd : q ∣ N)
    (chi : Character q) (f g : Character q → ℂ) :
    (∑ a ∈ numerators q,
      chi (a : ZMod q) * characterEvaluation f a * characterEvaluation g a *
        charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      (∑ psi : Character q, f psi * g ((chi*psi)⁻¹)) * ramanujan N q := by
  rw [phase_twisted_product, Finset.sum_mul]
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
    rw [phaseCoefficient_vanishes hd hc, mul_zero]

inductive MixedKind
  | oneEach
  | oneExceptionalTwoRegular
  | twoExceptionalOneRegular
  deriving DecidableEq

def mixedKernel (N a q : ℕ) (eta : ℝ) (j : MixedKind) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let M := principalCoefficient q * J N eta
    let E := characterEvaluation (exceptionalCoefficient (q := q) N eta) a
    let R := characterEvaluation (regularCoefficient (q := q) N eta) a
    match j with
    | .oneEach => 6*M*E*R
    | .oneExceptionalTwoRegular => -3*E*R^2
    | .twoExceptionalOneRegular => -3*E^2*R

theorem mixed_one_each_contraction {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (eta : ℝ) :
    (∑ a ∈ numerators q, mixedKernel N a q eta .oneEach *
      charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      ∑ psi : Character q, 6*(principalCoefficient q*J N eta)*
        exceptionalCoefficient N eta chi * regularCoefficient N eta psi *
          phaseCoefficient N (chi*psi) := by
  have h := congrArg
    (fun z : ℂ => (6*(principalCoefficient q*J N eta)*exceptionalCoefficient N eta chi)*z)
    (phase_twisted_evaluation N chi (regularCoefficient N eta))
  simp only [Finset.mul_sum] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro a _
    simp only [mixedKernel, dif_neg (NeZero.ne q),
      exceptional_evaluation_at_witness hN hq hr]
    ring
  · apply Finset.sum_congr rfl
    intro psi _
    ring

theorem mixed_one_exceptional_contraction {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (eta : ℝ) :
    (∑ a ∈ numerators q, mixedKernel N a q eta .oneExceptionalTwoRegular *
      charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      ∑ psi : Character q, ∑ tau : Character q,
        -3*exceptionalCoefficient N eta chi * regularCoefficient N eta psi *
          regularCoefficient N eta tau * phaseCoefficient N (chi*psi*tau) := by
  have h := congrArg (fun z : ℂ => (-3*exceptionalCoefficient N eta chi)*z)
    (phase_twisted_product N chi (regularCoefficient N eta) (regularCoefficient N eta))
  simp only [Finset.mul_sum] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro a _
    simp only [mixedKernel, dif_neg (NeZero.ne q),
      exceptional_evaluation_at_witness hN hq hr]
    ring
  · apply Finset.sum_congr rfl
    intro psi _
    apply Finset.sum_congr rfl
    intro tau _
    ring

theorem mixed_two_exceptional_contraction {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (eta : ℝ) :
    (∑ a ∈ numerators q, mixedKernel N a q eta .twoExceptionalOneRegular *
      charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      ∑ psi : Character q, -3*exceptionalCoefficient N eta chi^2 *
        regularCoefficient N eta psi * phaseCoefficient N psi := by
  have hc := (exceptionalValues_quadratic_simple hN hq hr).2.1
  have h := congrArg (fun z : ℂ => (-3*exceptionalCoefficient N eta chi^2)*z)
    (phase_twisted_evaluation N (chi^2) (regularCoefficient N eta))
  simp only [hc, one_mul, Finset.mul_sum] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro a ha
    have hu := (ZMod.isUnit_iff_coprime a q).mpr (mem_numerators.mp ha).2.2
    have hs : chi (a : ZMod q)^2 = 1 := by
      have hx := congrArg (fun psi : Character q => psi (a : ZMod q)) hc
      simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using hx
    simp only [mixedKernel, dif_neg (NeZero.ne q),
      exceptional_evaluation_at_witness hN hq hr, mul_pow, hs,
      MulChar.one_apply hu, one_mul]
    ring
  · apply Finset.sum_congr rfl
    intro psi _
    ring

theorem continuous_mixedKernel {N : ℕ} (hN : 0 < N) (a q : ℕ) (j : MixedKind) :
    Continuous (fun eta => mixedKernel N a q eta j) := by
  by_cases hq : q = 0
  · subst q
    exact continuous_const
  let : NeZero q := ⟨hq⟩
  have he : Continuous (fun eta =>
      characterEvaluation (exceptionalCoefficient (q := q) N eta) a) :=
    continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_exceptionalCoefficient hN chi))
  have hr : Continuous (fun eta =>
      characterEvaluation (regularCoefficient (q := q) N eta) a) :=
    continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_regularCoefficient hN chi))
  have hm : Continuous (fun eta => principalCoefficient q*J N eta) :=
    continuous_const.mul (continuous_J hN)
  cases j <;> simp only [mixedKernel, dif_neg hq] <;> fun_prop

def mixedArc (N q : ℕ) (j : MixedKind) : ℂ :=
  ∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
    mixedKernel N a q eta j * arcPhase N a q eta

theorem mixedArc_contract {N : ℕ} (hN : 0 < N) (q : ℕ) (j : MixedKind) :
    mixedArc N q j =
      ∫ eta in -deltaRadius N q..deltaRadius N q,
        (∑ a ∈ numerators q, mixedKernel N a q eta j *
          charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) * charReal (-(N : ℝ)*eta) := by
  rw [mixedArc, ← intervalIntegral.integral_finsetSum
    (f := fun a eta => mixedKernel N a q eta j * arcPhase N a q eta)
    (fun a _ => ((continuous_mixedKernel hN a q j).mul
      (continuous_arcPhase N a q)).intervalIntegrable _ _)]
  congr 1
  ext eta
  simp only [arcPhase_split, ← mul_assoc, ← Finset.sum_mul]

end LiuWang.Proof.SourceRoute.MajorException
