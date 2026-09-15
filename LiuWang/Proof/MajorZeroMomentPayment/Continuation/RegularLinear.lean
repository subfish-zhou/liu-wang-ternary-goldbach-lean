import LiuWang.Proof.MajorZeroMomentPayment.Continuation.LinearTail

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

def regularValues {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : Finset ℂ :=
  (zeroValues chi (sourceT N)).filter
    (fun rho => ¬ ZeroRegionFamily.RealClosure.region (sourceP N) q rho)

def regularLinearKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩;
    -3 * (principalCoefficient q * J N eta)^2 *
      characterEvaluation (regularCoefficient (q := q) N eta) a

def regularHigherKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let M := principalCoefficient q * J N eta
    let E := characterEvaluation (exceptionalCoefficient (q := q) N eta) a
    let R := characterEvaluation (regularCoefficient (q := q) N eta) a
    6 * M * E * R - 3 * E^2 * R + 3 * (M - E) * R^2 - R^3

theorem regularKernel_split (N a q : ℕ) (eta : ℝ) :
    regularInteractionKernel N a q eta =
      regularLinearKernel N a q eta + regularHigherKernel N a q eta := by
  by_cases hq : q = 0
  · simp [regularInteractionKernel, regularLinearKernel, regularHigherKernel, hq]
  · simp only [regularInteractionKernel, regularLinearKernel, regularHigherKernel, dif_neg hq]
    ring

theorem continuous_regularCoefficient {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) : Continuous (fun eta => regularCoefficient N eta chi) := by
  unfold regularCoefficient
  exact continuous_const.mul (continuous_finsetSum _ fun rho _ =>
    continuous_const.mul (Jrho_continuous hN rho))

theorem continuous_regularLinearKernel {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (regularLinearKernel N a q) := by
  by_cases hq : q = 0
  · subst q
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    have hc : Continuous (fun eta =>
        characterEvaluation (regularCoefficient (q := q) N eta) a) :=
      continuous_finsetSum _ fun chi _ =>
        continuous_const.mul (continuous_regularCoefficient hN chi)
    unfold regularLinearKernel
    simp only [dif_neg hq]
    exact (continuous_const.mul ((continuous_const.mul (continuous_J hN)).pow 2)).mul hc

def regularLinearArc (N q : ℕ) : ℂ :=
  ∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
    regularLinearKernel N a q eta * arcPhase N a q eta

theorem regularLinearArc_eq_moments {N q : ℕ} [NeZero q] (hN : 0 < N) :
    regularLinearArc N q =
      ∑ chi : Character q, ∑ rho ∈ regularValues N chi,
        (linearCoefficient N chi * (analyticOrderNatAt chi.LFunction rho : ℂ)) *
          finiteMoment N (deltaRadius N q) 1 1 rho := by
  have hp (eta : ℝ) :
      (∑ a ∈ numerators q, regularLinearKernel N a q eta * arcPhase N a q eta) =
      ∑ chi : Character q, ∑ rho ∈ regularValues N chi,
        (linearCoefficient N chi * (analyticOrderNatAt chi.LFunction rho : ℂ)) *
          tripleKernel N 1 1 rho eta := by
    simp only [regularLinearKernel, dif_neg (NeZero.ne q), characterEvaluation,
      regularCoefficient, arcPhase_split, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro chi _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro rho _
    simp only [linearCoefficient, phaseCoefficient, Finset.mul_sum, Finset.sum_mul,
      gaussScale, tripleKernel, Jrho_one_eq_J]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [regularLinearArc, ← intervalIntegral.integral_finsetSum
    (f := fun a eta => regularLinearKernel N a q eta * arcPhase N a q eta) (fun a _ =>
    ((continuous_regularLinearKernel hN a q).mul
      (continuous_arcPhase N a q)).intervalIntegrable _ _)]
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum
    (f := fun chi eta => ∑ rho ∈ regularValues N chi,
      (linearCoefficient N chi * (analyticOrderNatAt chi.LFunction rho : ℂ)) *
        tripleKernel N 1 1 rho eta) (fun chi _ =>
    (continuous_finsetSum _ fun rho _ =>
      continuous_const.mul (continuous_tripleKernel hN 1 1 rho)).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro chi _
  rw [intervalIntegral.integral_finsetSum
    (f := fun rho eta =>
      (linearCoefficient N chi * (analyticOrderNatAt chi.LFunction rho : ℂ)) *
        tripleKernel N 1 1 rho eta) (fun rho _ =>
    (continuous_const.mul (continuous_tripleKernel hN 1 1 rho)).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, finiteMoment]

def localRegularLinearPayment (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : Character q, ∑ rho ∈ regularValues N chi,
      (((linearCoefficient N chi * (analyticOrderNatAt chi.LFunction rho : ℂ)) *
        linearValue N rho).re -
      ‖linearCoefficient N chi * (analyticOrderNatAt chi.LFunction rho : ℂ)‖ *
        linearTail N (deltaRadius N q) rho)

theorem regularLinearArc_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    localRegularLinearPayment N q ≤ (regularLinearArc N q).re := by
  rw [regularLinearArc_eq_moments (nat_pos_of_exp_le hN)]
  simp only [localRegularLinearPayment, dif_neg (NeZero.ne q), Complex.re_sum]
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum
  intro rho hr
  have hv := mem_zeroValues.mp (Finset.mem_filter.mp hr).1
  exact finite_linear_signed_lower (nat_pos_of_exp_le hN) hv.2.1 hv.2.2.1
    (deltaRadius_pos hN (NeZero.pos q)) _

theorem linearCoefficient_divisor_nonprincipal {N q : ℕ} [NeZero q]
    (hd : q ∣ N) {chi : Character q} (hc : chi ≠ 1) :
    linearCoefficient N chi = 0 := by
  rw [linearCoefficient, phaseCoefficient_vanishes hd hc, mul_zero]

theorem regularLinearPayment_divisor {N q : ℕ} [NeZero q] (hd : q ∣ N) :
    localRegularLinearPayment N q =
      ∑ rho ∈ regularValues N (1 : Character q),
        (((linearCoefficient N (1 : Character q) *
          (analyticOrderNatAt (1 : Character q).LFunction rho : ℂ)) * linearValue N rho).re -
        ‖linearCoefficient N (1 : Character q) *
          (analyticOrderNatAt (1 : Character q).LFunction rho : ℂ)‖ *
            linearTail N (deltaRadius N q) rho) := by
  simp only [localRegularLinearPayment, dif_neg (NeZero.ne q)]
  apply Fintype.sum_eq_single (1 : Character q)
  intro chi hc
  simp [linearCoefficient_divisor_nonprincipal hd hc]

def regularLinearIntegral (N : ℕ) : ℂ :=
  ∑ q ∈ denominators (sourceP N), regularLinearArc N q

def totalRegularLinearPayment (N : ℕ) : ℝ :=
  ∑ q ∈ denominators (sourceP N), localRegularLinearPayment N q

def regularHigherIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    regularHigherKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta

theorem regularIntegral_split {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    regularInteractionIntegral N = regularLinearIntegral N + regularHigherIntegral N := by
  have he : regularLinearIntegral N =
      ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
        regularLinearKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta := by
    rw [coreIndices, Finset.sum_sigma]
    rfl
  rw [he, regularInteractionIntegral, regularHigherIntegral, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have ha := ((mem_coreIndices hN i).mp hi).2.2.2
  let : NeZero i.1 :=
    ⟨(ArcGeometry.sourceIndex_den_pos ((mem_coreIndices hN i).mp hi).2).ne'⟩
  have hl : IntervalIntegrable (fun eta =>
      regularLinearKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta)
      volume (-deltaRadius N i.1) (deltaRadius N i.1) :=
    ((continuous_regularLinearKernel (nat_pos_of_exp_le hN) i.2 i.1).mul
      (continuous_arcPhase N i.2 i.1)).intervalIntegrable _ _
  have hr : IntervalIntegrable (fun eta =>
      regularInteractionKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta)
      volume (-deltaRadius N i.1) (deltaRadius N i.1) := by
    have he' : IntervalIntegrable (fun eta =>
        exceptionalKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta)
        volume (-deltaRadius N i.1) (deltaRadius N i.1) :=
      ((continuous_exceptionalKernel (nat_pos_of_exp_le hN) i.2 i.1).mul
        (continuous_arcPhase N i.2 i.1)).intervalIntegrable _ _
    convert (interaction_integrable (nat_pos_of_exp_le hN) i.2 i.1
      (-deltaRadius N i.1) (deltaRadius N i.1)).sub he' using 1
    ext eta
    rw [interaction_exceptional_add_regular N i.2 eta ha]
    ring
  have hh : IntervalIntegrable (fun eta =>
      regularHigherKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta)
      volume (-deltaRadius N i.1) (deltaRadius N i.1) := by
    convert hr.sub hl using 1
    ext eta
    rw [regularKernel_split]
    ring
  rw [← intervalIntegral.integral_add hl hh]
  congr 1
  ext eta
  rw [regularKernel_split, add_mul]

theorem regularLinearIntegral_payment {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    totalRegularLinearPayment N ≤ (regularLinearIntegral N).re := by
  rw [regularLinearIntegral, totalRegularLinearPayment, Complex.re_sum]
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact regularLinearArc_payment hN

theorem lambdaTripleCount_paid_regular_linear {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.48166084 * (N : ℝ)^2 + totalExceptionalPayment N + totalRegularLinearPayment N +
      (regularHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ lambdaTripleCount N := by
  have h := lambdaTripleCount_ge_paid_exceptional hN hodd
  rw [regularIntegral_split (exp_2000_le_of_exp_3100_le hN), Complex.add_re] at h
  linarith [regularLinearIntegral_payment (exp_2000_le_of_exp_3100_le hN)]

end LiuWang.Proof.MajorZeroMomentPayment.Continuation
