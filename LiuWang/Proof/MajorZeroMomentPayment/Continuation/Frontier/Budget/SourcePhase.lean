import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.FinalPayment
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget

theorem gaussScale_mul_phase_non_coprime {N q : ℕ} [NeZero q] (chi : Character q)
    (hN : ¬ Nat.Coprime N chi.conductor) :
    gaussScale chi * phaseCoefficient N chi = 0 := by
  obtain ⟨p, hp, hpN, hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp hN
  have hpq := hpc.trans chi.conductor_dvd_level
  by_cases he : phaseCoefficient N chi = 0
  · rw [he, mul_zero]
  have hfactor : chi.FactorsThrough (q/p) := by
    apply factorsThrough_of_gaussSum_ne_zero
      (ZMod.stdAddChar.mulShift (-(N : ZMod q))) (Nat.div_dvd_of_dvd hpq)
    · ext x
      have hzero : (N : ZMod q) * ((q/p : ℕ) : ZMod q) = 0 := by
        rw [← Nat.cast_mul]
        apply (ZMod.natCast_eq_zero_iff _ _).mpr
        obtain ⟨k, hk⟩ := hpN
        rw [hk]
        have hd := Nat.div_mul_cancel hpq
        exact ⟨k, by nlinarith only [hd]⟩
      simp only [AddChar.mulShift_apply, AddChar.one_apply]
      rw [neg_mul, ← mul_assoc, hzero, zero_mul, neg_zero, AddChar.map_zero_eq_one]
    · rwa [← phaseCoefficient_eq_gauss]
  have hcd := chi.conductor_dvd_of_mem_conductorSet hfactor
  have hpcq : p*chi.conductor ∣ q := by
    have h := Nat.mul_dvd_mul_left p hcd
    simpa only [Nat.mul_div_cancel' hpq] using h
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [gaussScale_redundant_prime hp hpc hpcq chi (dvd_refl _), zero_mul]

theorem odd_coefficients_non_coprime {N q : ℕ} [NeZero q] (chi : Character q)
    (hN : ¬ Nat.Coprime N chi.conductor) :
    linearCoefficient N chi = 0 ∧ cubicCoefficient N chi = 0 := by
  have h := gaussScale_mul_phase_non_coprime chi hN
  constructor
  · rw [linearCoefficient, mul_assoc, h, mul_zero]
  · calc
      cubicCoefficient N chi = -(gaussScale chi)^2 *
          (gaussScale chi * phaseCoefficient N chi) := by unfold cubicCoefficient; ring
      _ = 0 := by rw [h, mul_zero]

theorem exceptionalArc_non_coprime_eq {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hnc : ¬ Nat.Coprime N chi.conductor) :
    exceptionalArc N q = quadraticCoefficient N chi *
      finiteMoment N (deltaRadius N q) 1 rho.re rho.re := by
  rw [exceptionalArc_eq_joint hN hq hr, jointFinite]
  have h := odd_coefficients_non_coprime chi hnc
  rw [h.1, h.2]
  simp

theorem exceptionalArc_non_coprime_norm {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hnc : ¬ Nat.Coprime N chi.conductor) :
    ‖exceptionalArc N q‖ ≤ (9/Real.pi)*(N : ℝ)^2 *
      (chi.conductor : ℝ)*(realEndpoint N rho.re)^2/(q.totient : ℝ)^2 := by
  rw [exceptionalArc_non_coprime_eq hN hq hr hnc, norm_mul]
  have hb := (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le
  have hm := finite_real_triple_uniform (nat_pos_of_exp_le hN) le_rfl hb hb
    (deltaRadius_pos hN (NeZero.pos q)).le
  have he : realEndpoint N 1 = 1 := by simp [realEndpoint]
  simp only [he, one_mul, Complex.ofReal_one] at hm
  apply (mul_le_mul (coefficient_norms_conductor N chi).2.1 hm
    (norm_nonneg _) (by positivity)).trans_eq
  ring

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget
