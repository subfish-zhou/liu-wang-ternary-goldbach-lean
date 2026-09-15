import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.CharacterMass
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Consumer

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def originalMotherBudget (N q : ℕ) : ℝ :=
  8.2e-10 / sourceL N + 0.063 * q / sourceL N ^ 4

def normalizedCost (N q r : ℕ) (beta M : ℝ) : MixedKind → ℝ
  | .oneEach => 6 * moebiusWeight q * Real.sqrt r * Real.sqrt q / (q.totient:ℝ)^2 *
      (N:ℝ)^2 * principalRoot * exceptionalScale N beta * radiusRoot N q * M
  | .oneExceptionalTwoRegular => 3 * Real.sqrt r * q / (q.totient:ℝ)^2 *
      (N:ℝ)^2 * exceptionalScale N beta * (radiusRoot N q)^2 * M^2
  | .twoExceptionalOneRegular => 3 * r * Real.sqrt q / (q.totient:ℝ)^2 *
      (N:ℝ)^2 * (exceptionalScale N beta)^2 * radiusRoot N q * M

theorem normalizedCost_nonneg {N q r : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hq : 0 < q) (beta : ℝ) {M : ℝ}
    (hM : 0 ≤ M) (j : MixedKind) : 0 ≤ normalizedCost N q r beta M j := by
  obtain ⟨hp, he, hd⟩ := roots_pos hN hq
  have hb := baseWeight_pos (nat_pos_of_exp_le hN) beta
  have hm := moebiusWeight_nonneg q
  cases j <;> dsimp [normalizedCost, exceptionalScale] <;> positivity

theorem mixedCost_le_normalized {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N:ℝ)) (chi : Character q) (beta : ℝ)
    {M : ℝ} (hM : regularMother N q ≤ M) (j : MixedKind) :
    mixedCost N chi beta j ≤ normalizedCost N q chi.conductor beta M j := by
  have hM0 := (regularMother_nonneg hN).trans hM
  have hp : 0 < (q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  obtain ⟨hj, he, hd⟩ := roots_pos hN (NeZero.pos q)
  have hb := baseWeight_pos (nat_pos_of_exp_le hN) beta
  have he0 : 0 ≤ exceptionalScale N beta := by unfold exceptionalScale; positivity
  have hg : ‖gaussScale chi‖ ≤ Real.sqrt chi.conductor / q.totient := by
    have h := MajorZeroMomentPayment.Continuation.Frontier.gaussScale_norm_le chi
    simpa only [DirichletCharacter.conductor_inv, div_eq_mul_inv, mul_comm] using h
  have hs (psi : Character q) : phaseMass N psi ≤ Real.sqrt q * M :=
    (phaseMass_le_mother hN psi).trans
      (mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _))
  have ht : pairPhaseMass N chi ≤ ((q:ℝ)/q.totient) * M^2 :=
    (pairPhaseMass_le_mother hN chi).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (regularMother_nonneg hN) hM 2) (by positivity))
  have hphase (psi : Character q) : 0 ≤ phaseMass N psi :=
    Finset.sum_nonneg (fun tau _ =>
      mul_nonneg (by positivity) (regularMass_nonneg hN tau))
  have hpair : 0 ≤ pairPhaseMass N chi :=
    Finset.sum_nonneg (fun psi _ => Finset.sum_nonneg (fun tau _ =>
      mul_nonneg (mul_nonneg (by positivity) (regularMass_nonneg hN psi))
        (regularMass_nonneg hN tau)))
  cases j with
  | oneEach =>
    calc
      _ ≤ 6*‖principalCoefficient q‖*(Real.sqrt chi.conductor/q.totient)*(N:ℝ)^2*
          principalRoot*exceptionalScale N beta*radiusRoot N q*(Real.sqrt q*M) := by
        dsimp [mixedCost]
        gcongr
        exact hphase chi
        exact hs chi
      _ = _ := by rw [principal_coefficient_moebius]; dsimp [normalizedCost]; ring
  | oneExceptionalTwoRegular =>
    calc
      _ ≤ 3*(Real.sqrt chi.conductor/q.totient)*(N:ℝ)^2*
          exceptionalScale N beta*(radiusRoot N q)^2*(((q:ℝ)/q.totient)*M^2) := by
        dsimp [mixedCost]
        gcongr
      _ = _ := by dsimp [normalizedCost]; ring
  | twoExceptionalOneRegular =>
    calc
      _ ≤ 3*(Real.sqrt chi.conductor/q.totient)^2*(N:ℝ)^2*
          (exceptionalScale N beta)^2*radiusRoot N q*(Real.sqrt q*M) := by
        dsimp [mixedCost]
        gcongr
        exact hphase (1 : Character q)
        exact hs (1 : Character q)
      _ = _ := by
        dsimp [normalizedCost]
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        ring

theorem actual_arc_original_mothers {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hq : (q:ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hlow : lowMother N q ≤ 8.2e-10 / sourceL N)
    (hhigh : highMother N q ≤ 0.0126*q/sourceL N^4) (j : MixedKind) :
    ‖mixedArc N q j‖ ≤
      normalizedCost N q chi.conductor rho.re (originalMotherBudget N q) j :=
  (actual_mixed_arc_bound hN hq hr j).trans
    (mixedCost_le_normalized hN chi rho.re (regularMother_original hlow hhigh) j)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
