import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.MixedTotal

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

theorem radiusRoot_cube_source {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q) :
    radiusRoot N q^3 = (3.36/(5*Real.pi))*sourceL N^3/(q : ℝ) := by
  have hn := natCast_pos_of_exp_le hN
  have hd := deltaRadius_pos hN hq
  rw [radiusRoot, cubeRoot_cube (by positivity)]
  unfold deltaRadius sourceP
  field_simp
  ring

theorem gaussScale_norm_totient {q : ℕ} [NeZero q] (chi : Character q) :
    ‖gaussScale chi‖ = (q.totient : ℝ)⁻¹*‖gaussSum chi⁻¹ ZMod.stdAddChar‖ := by
  simp only [gaussScale, norm_mul, norm_inv, Complex.norm_natCast]

theorem phaseMass_totient {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    phaseMass N chi = (q.totient : ℝ)⁻¹*
      ∑ psi : Character q, ‖phaseCoefficient N (chi*psi)‖*
        ‖gaussSum psi⁻¹ ZMod.stdAddChar‖*regularMass N psi := by
  simp only [phaseMass, gaussScale_norm_totient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro psi _
  ring

theorem pairPhaseMass_totient {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    pairPhaseMass N chi = (q.totient : ℝ)⁻¹^2*
      ∑ psi : Character q, ∑ tau : Character q, ‖phaseCoefficient N (chi*psi*tau)‖*
        ‖gaussSum psi⁻¹ ZMod.stdAddChar‖*‖gaussSum tau⁻¹ ZMod.stdAddChar‖*
          regularMass N psi*regularMass N tau := by
  simp only [pairPhaseMass, gaussScale_norm_totient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro psi _
  apply Finset.sum_congr rfl
  intro tau _
  ring

theorem principal_coefficient_moebius (q : ℕ) :
    ‖principalCoefficient q‖ = moebiusWeight q/(q.totient : ℝ) :=
  norm_principalCoefficient q

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
