import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Normalization
import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.DirectPayment

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def lowMother (N q : ℕ) [NeZero q] : ℝ :=
  ∑ psi : Character q, regularLowMass N psi

def highMother (N q : ℕ) [NeZero q] : ℝ :=
  ∑ psi : Character q, regularHighMass N psi

def regularMother (N q : ℕ) [NeZero q] : ℝ :=
  ∑ psi : Character q, regularMass N psi

theorem regularMother_split (N q : ℕ) [NeZero q] :
    regularMother N q = lowMother N q + 5 * highMother N q := by
  simp only [regularMother, regularMass_low_high, Finset.sum_add_distrib,
    lowMother, highMother, Finset.mul_sum]

theorem regularMother_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) : 0 ≤ regularMother N q :=
  Finset.sum_nonneg (fun psi _ => regularMass_nonneg hN psi)

theorem gaussScale_modulus {q : ℕ} [NeZero q] (psi : Character q) :
    ‖gaussScale psi‖ ≤ Real.sqrt q / q.totient := by
  apply (MajorZeroMomentPayment.Continuation.Frontier.gaussScale_norm_le psi).trans
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Nat.cast_le.mpr
      (BombieriVinogradov.DirichletCharacter.conductor_le_level psi⁻¹)))
    (inv_nonneg.mpr (Nat.cast_nonneg q.totient) : (0:ℝ) ≤ (q.totient:ℝ)⁻¹)

theorem phase_gauss_modulus {N q : ℕ} [NeZero q] (chi psi : Character q) :
    ‖phaseCoefficient N chi‖ * ‖gaussScale psi‖ ≤ Real.sqrt q := by
  have hp : (q.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  exact (mul_le_mul (norm_phaseCoefficient_le_totient N chi) (gaussScale_modulus psi)
    (norm_nonneg _) (Nat.cast_nonneg _)).trans_eq (by field_simp)

theorem phaseMass_le_mother {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) :
    phaseMass N chi ≤ Real.sqrt q * regularMother N q := by
  rw [phaseMass, regularMother, Finset.mul_sum]
  exact Finset.sum_le_sum (fun psi _ =>
    mul_le_mul_of_nonneg_right (phase_gauss_modulus (chi*psi) psi)
      (regularMass_nonneg hN psi))

theorem pairPhaseMass_le_mother {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) :
    pairPhaseMass N chi ≤ ((q : ℝ)/q.totient) * regularMother N q ^ 2 := by
  have he : Real.sqrt q * (Real.sqrt q / q.totient) = (q : ℝ)/q.totient := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ psi : Character q, ∑ tau : Character q,
        ((q : ℝ)/q.totient) * regularMass N psi * regularMass N tau := by
      apply Finset.sum_le_sum
      intro psi _
      apply Finset.sum_le_sum
      intro tau _
      apply mul_le_mul_of_nonneg_right _ (regularMass_nonneg hN tau)
      apply mul_le_mul_of_nonneg_right _ (regularMass_nonneg hN psi)
      exact (mul_le_mul (phase_gauss_modulus (chi*psi*tau) psi)
        (gaussScale_modulus tau) (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq he
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, regularMother]
      ring

theorem regularMother_original {N q : ℕ} [NeZero q]
    (hlow : lowMother N q ≤ 8.2e-10 / sourceL N)
    (hhigh : highMother N q ≤ 0.0126 * q / sourceL N ^ 4) :
    regularMother N q ≤ 8.2e-10 / sourceL N + 0.063 * q / sourceL N ^ 4 := by
  rw [regularMother_split]
  have h := add_le_add hlow (mul_le_mul_of_nonneg_left hhigh (by norm_num : (0:ℝ) ≤ 5))
  exact h.trans_eq (by ring)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
