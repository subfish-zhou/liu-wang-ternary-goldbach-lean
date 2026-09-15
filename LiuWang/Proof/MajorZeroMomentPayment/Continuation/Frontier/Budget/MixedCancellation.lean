import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.LargeConductor

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget

def coprimeRegularCoefficient {q : ℕ} [NeZero q] (N : ℕ) (eta : ℝ)
    (chi : Character q) : ℂ :=
  if Nat.Coprime N chi.conductor then regularCoefficient N eta chi else 0

def nonCoprimeRegularCoefficient {q : ℕ} [NeZero q] (N : ℕ) (eta : ℝ)
    (chi : Character q) : ℂ :=
  if Nat.Coprime N chi.conductor then 0 else regularCoefficient N eta chi

theorem regularCoefficient_source_split {q : ℕ} [NeZero q]
    (N : ℕ) (eta : ℝ) (chi : Character q) :
    regularCoefficient N eta chi =
      coprimeRegularCoefficient N eta chi + nonCoprimeRegularCoefficient N eta chi := by
  unfold coprimeRegularCoefficient nonCoprimeRegularCoefficient
  split_ifs <;> simp

theorem nonCoprimeRegular_phase_zero {q : ℕ} [NeZero q]
    (N : ℕ) (eta : ℝ) (chi : Character q) :
    nonCoprimeRegularCoefficient N eta chi * phaseCoefficient N chi = 0 := by
  unfold nonCoprimeRegularCoefficient
  split_ifs with hc
  · simp
  · have hz := gaussScale_mul_phase_non_coprime chi hc
    change (gaussScale chi *
      ∑ rho ∈ regularValues N chi,
        (analyticOrderNatAt chi.LFunction rho : ℂ)*Jrho N rho eta) * phaseCoefficient N chi = 0
    rw [mul_right_comm, hz, zero_mul]

theorem nonCoprimeRegular_numerator_zero {q : ℕ} [NeZero q] (N : ℕ) (eta : ℝ) :
    (∑ a ∈ numerators q,
      characterEvaluation (nonCoprimeRegularCoefficient (q := q) N eta) a *
        charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) = 0 := by
  simp only [characterEvaluation, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro chi _
  have he : (∑ a ∈ numerators q,
      (chi (a : ZMod q)*nonCoprimeRegularCoefficient N eta chi) *
        charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      nonCoprimeRegularCoefficient N eta chi * phaseCoefficient N chi := by
    rw [phaseCoefficient, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he, nonCoprimeRegular_phase_zero]

def cancelledMixedKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩;
    -3*(characterEvaluation (exceptionalCoefficient (q := q) N eta) a)^2 *
      characterEvaluation (nonCoprimeRegularCoefficient (q := q) N eta) a

theorem cancelledMixed_numerator_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (eta : ℝ) :
    (∑ a ∈ numerators q, cancelledMixedKernel N a q eta *
      charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) = 0 := by
  by_cases hex : ∃ (chi : Character q) (rho : ℂ), rho ∈ exceptionalValues N chi
  · obtain ⟨chi, rho, hr⟩ := hex
    have hc := (exceptionalValues_quadratic_simple hN hq hr).2.1
    have he (a : ℕ) (ha : a ∈ numerators q) :
        cancelledMixedKernel N a q eta =
          -3*(exceptionalCoefficient N eta chi)^2 *
            characterEvaluation (nonCoprimeRegularCoefficient (q := q) N eta) a := by
      have hs : chi (a : ZMod q)^2 = 1 := by
        have h := congrArg (fun psi : Character q => psi (a : ZMod q)) hc
        have hu := (ZMod.isUnit_iff_coprime a q).mpr (mem_numerators.mp ha).2.2
        simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using h
      simp only [cancelledMixedKernel, dif_neg (NeZero.ne q),
        exceptional_evaluation_at_witness hN hq hr, mul_pow, hs, one_mul]
    calc
      _ = (-3*(exceptionalCoefficient N eta chi)^2) *
          ∑ a ∈ numerators q,
            characterEvaluation (nonCoprimeRegularCoefficient (q := q) N eta) a *
              charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [he a ha, mul_assoc]
      _ = 0 := by rw [nonCoprimeRegular_numerator_zero, mul_zero]
  · have hn : ∀ chi : Character q, exceptionalValues N chi = ∅ :=
      fun chi => Finset.eq_empty_iff_forall_notMem.mpr (fun rho hr => hex ⟨chi, rho, hr⟩)
    simp only [cancelledMixedKernel, dif_neg (NeZero.ne q), characterEvaluation,
      (no_exceptional_coefficient hn eta _).1, mul_zero, zero_mul, Finset.sum_const_zero,
      zero_pow (by norm_num : 2 ≠ 0)]

theorem continuous_cancelledMixed {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (cancelledMixedKernel N a q) := by
  by_cases hq : q = 0
  · subst q; exact continuous_const
  let : NeZero q := ⟨hq⟩
  have hc (chi : Character q) :
      Continuous (fun eta => nonCoprimeRegularCoefficient N eta chi) := by
    unfold nonCoprimeRegularCoefficient
    split_ifs
    · exact continuous_const
    · exact continuous_regularCoefficient hN chi
  have he : Continuous (fun eta =>
      characterEvaluation (exceptionalCoefficient (q := q) N eta) a) :=
    continuous_finsetSum Finset.univ (fun chi _ =>
      continuous_const.mul (continuous_exceptionalCoefficient hN chi))
  have hr : Continuous (fun eta =>
      characterEvaluation (nonCoprimeRegularCoefficient (q := q) N eta) a) :=
    continuous_finsetSum Finset.univ (fun chi _ => continuous_const.mul (hc chi))
  unfold cancelledMixedKernel
  simp only [dif_neg hq]
  exact (continuous_const.mul (he.pow 2)).mul hr

theorem cancelledMixed_arc_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
      cancelledMixedKernel N a q eta * arcPhase N a q eta) = 0 := by
  rw [← intervalIntegral.integral_finsetSum
    (f := fun a eta => cancelledMixedKernel N a q eta * arcPhase N a q eta) (fun a _ =>
    ((continuous_cancelledMixed (nat_pos_of_exp_le hN) a q).mul
      (continuous_arcPhase N a q)).intervalIntegrable _ _)]
  have he (eta : ℝ) :
      (∑ a ∈ numerators q, cancelledMixedKernel N a q eta * arcPhase N a q eta) = 0 := by
    simp only [arcPhase_split, ← mul_assoc, ← Finset.sum_mul,
      cancelledMixed_numerator_zero hN hq, zero_mul]
  simp only [he, intervalIntegral.integral_zero]

def prunedHigherKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  regularHigherKernel N a q eta - cancelledMixedKernel N a q eta

theorem prunedHigherKernel_explicit {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    prunedHigherKernel N a q eta =
      let M := principalCoefficient q*J N eta
      let E := characterEvaluation (exceptionalCoefficient (q := q) N eta) a
      let R := characterEvaluation (regularCoefficient (q := q) N eta) a
      let Rc := characterEvaluation (coprimeRegularCoefficient (q := q) N eta) a
      6*M*E*R - 3*E^2*Rc + 3*(M-E)*R^2 - R^3 := by
  have hs : characterEvaluation (regularCoefficient (q := q) N eta) a =
      characterEvaluation (coprimeRegularCoefficient (q := q) N eta) a +
        characterEvaluation (nonCoprimeRegularCoefficient (q := q) N eta) a := by
    simp only [characterEvaluation, regularCoefficient_source_split, mul_add, Finset.sum_add_distrib]
  unfold prunedHigherKernel regularHigherKernel cancelledMixedKernel
  simp only [dif_neg (NeZero.ne q)]
  rw [hs]
  ring

def prunedHigherIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    prunedHigherKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta

theorem regularHigherIntegral_pruned {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    regularHigherIntegral N = prunedHigherIntegral N := by
  have hz : (∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
      cancelledMixedKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta) = 0 := by
    rw [coreIndices, Finset.sum_sigma]
    apply Finset.sum_eq_zero
    intro q hq
    have hq' := (mem_denominators (sourceP_pos hN).le q).mp hq
    let : NeZero q := ⟨by omega⟩
    exact cancelledMixed_arc_zero hN hq'.2
  have he : prunedHigherIntegral N = regularHigherIntegral N -
      ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
        cancelledMixedKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta := by
    rw [prunedHigherIntegral, regularHigherIntegral, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hic := (mem_coreIndices hN i).mp hi
    let : NeZero i.1 := ⟨(ArcGeometry.sourceIndex_den_pos hic.2).ne'⟩
    have hr : IntervalIntegrable (fun eta =>
        regularHigherKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta)
        volume (-deltaRadius N i.1) (deltaRadius N i.1) := by
      have hp := interaction_integrable (nat_pos_of_exp_le hN) i.2 i.1
        (-deltaRadius N i.1) (deltaRadius N i.1)
      have he' := ((continuous_exceptionalKernel (nat_pos_of_exp_le hN) i.2 i.1).mul
        (continuous_arcPhase N i.2 i.1)).intervalIntegrable (μ := volume)
          (-deltaRadius N i.1) (deltaRadius N i.1)
      have hl := ((continuous_regularLinearKernel (nat_pos_of_exp_le hN) i.2 i.1).mul
        (continuous_arcPhase N i.2 i.1)).intervalIntegrable (μ := volume)
          (-deltaRadius N i.1) (deltaRadius N i.1)
      convert (hp.sub he').sub hl using 1
      ext eta
      rw [interaction_exceptional_add_regular N i.2 eta hic.2.2.2, regularKernel_split]
      simp only [Pi.mul_apply]
      ring
    have hc := ((continuous_cancelledMixed (nat_pos_of_exp_le hN) i.2 i.1).mul
      (continuous_arcPhase N i.2 i.1)).intervalIntegrable (μ := volume)
        (-deltaRadius N i.1) (deltaRadius N i.1)
    simp only [prunedHigherKernel, sub_mul]
    exact intervalIntegral.integral_sub hr hc
  rw [hz, sub_zero] at he
  exact he.symm

theorem directArithmeticSum_pruned {q : ℕ} [NeZero q] (N : ℕ) :
    directArithmeticSum N q =
      ∑ chi : Character q, if Nat.Coprime N chi.conductor then
        ‖linearCoefficient N chi‖*regularRhoWeight N chi else 0 := by
  simp only [directArithmeticSum, dif_neg (NeZero.ne q)]
  apply Finset.sum_congr rfl
  intro chi _
  split_ifs with hc
  · rfl
  · rw [(odd_coefficients_non_coprime chi hc).1, norm_zero, zero_mul]

theorem lambdaTripleCount_large_pruned {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ exceptionalValues N chi)
    (hr : 1600000000 ≤ chi.conductor) :
    0.23166084*(N : ℝ)^2 + totalEnhancedRegularPayment N + (prunedHigherIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re -
      6760*(N : ℝ)^2/sourceL N^4 ≤ lambdaTripleCount N := by
  simpa only [regularHigherIntegral_pruned (exp_2000_le_of_exp_3100_le hN)] using
    lambdaTripleCount_large_conductor hN hodd hq hrho hr

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget
