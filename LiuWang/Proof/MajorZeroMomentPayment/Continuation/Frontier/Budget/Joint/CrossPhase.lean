import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Consumer

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

theorem evaluation_phase {q : ℕ} [NeZero q] (N : ℕ) (f : Character q → ℂ) :
    (∑ a ∈ numerators q, characterEvaluation f a *
      charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      ∑ psi : Character q, f psi * phaseCoefficient N psi := by
  simp only [characterEvaluation, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  rw [phaseCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem twisted_evaluation_phase {q : ℕ} [NeZero q]
    (N : ℕ) (chi : Character q) (f : Character q → ℂ) :
    (∑ a ∈ numerators q, chi (a : ZMod q)*characterEvaluation f a *
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

theorem phase_principal_divisor {q : ℕ} [NeZero q] {N : ℕ} (hd : q ∣ N) :
    phaseCoefficient N (1 : Character q) = (q.totient : ℂ) := by
  rw [phaseCoefficient_principal, ramanujan]
  have he (a : ℕ) : charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ)) = 1 := by
    rw [← stdAddChar_negative_phase,
      (ZMod.natCast_eq_zero_iff N q).mpr hd, mul_zero, AddChar.map_zero_eq_one]
  simp only [he, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast reducedResidues_card q

theorem twisted_evaluation_divisor {q : ℕ} [NeZero q] {N : ℕ}
    (hd : q ∣ N) (chi : Character q) (f : Character q → ℂ) :
    (∑ psi : Character q, f psi * phaseCoefficient N (chi*psi)) =
      (q.totient : ℂ)*f chi⁻¹ := by
  rw [Fintype.sum_eq_single chi⁻¹]
  · rw [mul_inv_cancel, phase_principal_divisor hd, mul_comm]
  · intro psi hp
    have hc : chi*psi ≠ 1 := by
      intro he
      apply hp
      exact eq_inv_of_mul_eq_one_right he
    rw [phaseCoefficient_vanishes hd hc, mul_zero]

def crossCoefficient {q : ℕ} [NeZero q] (N : ℕ) (chi psi : Character q) : ℂ :=
  6*principalCoefficient q*gaussScale chi*gaussScale psi*phaseCoefficient N (chi*psi)

def squareCoefficient {q : ℕ} [NeZero q] (N : ℕ) (chi psi : Character q) : ℂ :=
  -3*gaussScale chi^2*gaussScale psi*phaseCoefficient N psi

theorem crossCoefficient_divisor_zero {N q : ℕ} [NeZero q]
    (hd : q ∣ N) (chi psi : Character q) (hp : psi ≠ chi⁻¹) :
    crossCoefficient N chi psi = 0 := by
  have hc : chi*psi ≠ 1 := fun h => hp (eq_inv_of_mul_eq_one_right h)
  rw [crossCoefficient, phaseCoefficient_vanishes hd hc, mul_zero]

theorem squareCoefficient_source_zero {N q : ℕ} [NeZero q]
    (chi psi : Character q) (hnc : ¬ Nat.Coprime N psi.conductor) :
    squareCoefficient N chi psi = 0 := by
  rw [squareCoefficient, mul_assoc, gaussScale_mul_phase_non_coprime psi hnc, mul_zero]

def mixedLinearKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩;
    let M := principalCoefficient q*J N eta
    let E := characterEvaluation (exceptionalCoefficient (q := q) N eta) a
    let R := characterEvaluation (regularCoefficient (q := q) N eta) a
    6*M*E*R - 3*E^2*R

theorem mixedLinear_contraction {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (eta : ℝ) :
    (∑ a ∈ numerators q, mixedLinearKernel N a q eta * arcPhase N a q eta) =
      ∑ psi : Character q, ∑ tau ∈ regularValues N psi,
        (analyticOrderNatAt psi.LFunction tau : ℂ) *
          (crossCoefficient N chi psi * tripleKernel N 1 rho.re tau eta +
            squareCoefficient N chi psi * tripleKernel N rho.re rho.re tau eta) := by
  have hs := (exceptionalValues_quadratic_simple hN hq hr).2.1
  have he (a : ℕ) (ha : a ∈ numerators q) :
      mixedLinearKernel N a q eta =
        (6*principalCoefficient q*J N eta*exceptionalCoefficient N eta chi) *
          (chi (a : ZMod q)*characterEvaluation (regularCoefficient (q := q) N eta) a) -
        (3*exceptionalCoefficient N eta chi^2) *
          characterEvaluation (regularCoefficient (q := q) N eta) a := by
    have hc : chi (a : ZMod q)^2 = 1 := by
      have h := congrArg (fun psi : Character q => psi (a : ZMod q)) hs
      have hu := (ZMod.isUnit_iff_coprime a q).mpr (mem_numerators.mp ha).2.2
      simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using h
    simp only [mixedLinearKernel, dif_neg (NeZero.ne q),
      exceptional_evaluation_at_witness hN hq hr, mul_pow, hc, one_mul]
    ring
  have hcontract :
      (∑ a ∈ numerators q, mixedLinearKernel N a q eta *
        charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) =
      (6*principalCoefficient q*J N eta*exceptionalCoefficient N eta chi) *
        ∑ psi : Character q, regularCoefficient N eta psi * phaseCoefficient N (chi*psi) -
      (3*exceptionalCoefficient N eta chi^2) *
        ∑ psi : Character q, regularCoefficient N eta psi * phaseCoefficient N psi := by
    calc
      _ = (6*principalCoefficient q*J N eta*exceptionalCoefficient N eta chi) *
          (∑ a ∈ numerators q, chi (a : ZMod q)*
            characterEvaluation (regularCoefficient (q := q) N eta) a *
              charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) -
        (3*exceptionalCoefficient N eta chi^2) *
          (∑ a ∈ numerators q, characterEvaluation (regularCoefficient (q := q) N eta) a *
            charReal (-(a : ℝ)*(N : ℝ)/(q : ℝ))) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        rw [he a ha]
        ring
      _ = _ := by rw [twisted_evaluation_phase, evaluation_phase]
  simp only [arcPhase_split, ← mul_assoc, ← Finset.sum_mul]
  rw [hcontract, exceptional_coefficient_real_zero hN hq hr]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro psi _
  simp only [regularCoefficient, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro tau _
  simp only [crossCoefficient, squareCoefficient, gaussScale, tripleKernel, Jrho_one_eq_J]
  ring

theorem continuous_mixedLinear {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (mixedLinearKernel N a q) := by
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
  unfold mixedLinearKernel
  simp only [dif_neg hq]
  exact (((continuous_const.mul hm).mul he).mul hr).sub
    ((continuous_const.mul (he.pow 2)).mul hr)

def mixedLinearArc (N q : ℕ) : ℂ :=
  ∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
    mixedLinearKernel N a q eta*arcPhase N a q eta

theorem mixedLinearArc_moments {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    mixedLinearArc N q =
      ∑ psi : Character q, ∑ tau ∈ regularValues N psi,
        (analyticOrderNatAt psi.LFunction tau : ℂ) *
          (crossCoefficient N chi psi * finiteMoment N (deltaRadius N q) 1 rho.re tau +
            squareCoefficient N chi psi * finiteMoment N (deltaRadius N q) rho.re rho.re tau) := by
  have hn := nat_pos_of_exp_le hN
  rw [mixedLinearArc, ← intervalIntegral.integral_finsetSum
    (f := fun a eta => mixedLinearKernel N a q eta*arcPhase N a q eta)
    (fun a _ => ((continuous_mixedLinear hn a q).mul (continuous_arcPhase N a q)).intervalIntegrable _ _)]
  simp_rw [mixedLinear_contraction hN hq hr]
  have hi (psi : Character q) (tau : ℂ) :
      Continuous (fun eta => (analyticOrderNatAt psi.LFunction tau : ℂ) *
        (crossCoefficient N chi psi * tripleKernel N 1 rho.re tau eta +
          squareCoefficient N chi psi * tripleKernel N rho.re rho.re tau eta)) :=
    continuous_const.mul ((continuous_const.mul (continuous_tripleKernel hn 1 rho.re tau)).add
      (continuous_const.mul (continuous_tripleKernel hn rho.re rho.re tau)))
  rw [intervalIntegral.integral_finsetSum (fun psi _ =>
    (continuous_finsetSum _ fun tau _ => hi psi tau).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro psi _
  rw [intervalIntegral.integral_finsetSum (fun tau _ => (hi psi tau).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro tau _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (((continuous_tripleKernel hn 1 rho.re tau).const_mul _).intervalIntegrable _ _)
    (((continuous_tripleKernel hn rho.re rho.re tau).const_mul _).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, finiteMoment]

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.Joint
