import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.RegularMass

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

def mixedCost {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) (beta : ℝ) : MixedKind → ℝ
  | .oneEach => 6*‖principalCoefficient q‖*‖gaussScale chi‖*(N : ℝ)^2*
      principalRoot*exceptionalScale N beta*radiusRoot N q*phaseMass N chi
  | .oneExceptionalTwoRegular => 3*‖gaussScale chi‖*(N : ℝ)^2*
      exceptionalScale N beta*(radiusRoot N q)^2*pairPhaseMass N chi
  | .twoExceptionalOneRegular => 3*‖gaussScale chi‖^2*(N : ℝ)^2*
      (exceptionalScale N beta)^2*radiusRoot N q*phaseMass N (1 : Character q)

theorem mixed_one_each_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ‖mixedArc N q .oneEach‖ ≤ mixedCost N chi rho.re .oneEach := by
  have hb := exceptional_beta_source_range hN hr
  rw [mixed_one_each_moments hN hq hr]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ psi : Character q, ∑ tau ∈ regularValues N psi,
        ‖6*principalCoefficient q*gaussScale chi*phaseCoefficient N (chi*psi)*
          regularAmplitude psi tau‖*
            ((N : ℝ)^2*principalRoot*exceptionalScale N rho.re*regularScale N q tau) := by
      apply Finset.sum_le_sum
      intro psi _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro tau ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (mixed_finite_one_each hN (NeZero.pos q) hb.1 hb.2 (regularValue_re_pos ht))
        (norm_nonneg _)
    _ = _ := by
      simp only [mixedCost, phaseMass, regularMass, Finset.mul_sum, norm_mul,
        norm_regularAmplitude, regularScale]
      norm_num only [Complex.norm_ofNat]
      apply Finset.sum_congr rfl
      intro psi _
      apply Finset.sum_congr rfl
      intro tau _
      ring

theorem mixed_two_exceptional_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ‖mixedArc N q .twoExceptionalOneRegular‖ ≤ mixedCost N chi rho.re .twoExceptionalOneRegular := by
  have hb := exceptional_beta_source_range hN hr
  rw [mixed_two_exceptional_moments hN hq hr]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ psi : Character q, ∑ tau ∈ regularValues N psi,
        ‖-3*gaussScale chi^2*phaseCoefficient N psi*regularAmplitude psi tau‖*
          ((N : ℝ)^2*(exceptionalScale N rho.re)^2*regularScale N q tau) := by
      apply Finset.sum_le_sum
      intro psi _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro tau ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (mixed_finite_two_exceptional hN (NeZero.pos q) hb.1 hb.2 (regularValue_re_pos ht))
        (norm_nonneg _)
    _ = _ := by
      simp only [mixedCost, phaseMass, one_mul, regularMass, Finset.mul_sum, norm_mul,
        norm_pow, norm_neg, norm_regularAmplitude, regularScale]
      norm_num only [Complex.norm_ofNat]
      apply Finset.sum_congr rfl
      intro psi _
      apply Finset.sum_congr rfl
      intro tau _
      ring

theorem mixed_one_exceptional_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ‖mixedArc N q .oneExceptionalTwoRegular‖ ≤ mixedCost N chi rho.re .oneExceptionalTwoRegular := by
  have hb := exceptional_beta_source_range hN hr
  rw [mixed_one_exceptional_moments hN hq hr]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ psi : Character q, ∑ tau : Character q,
        ∑ sigma ∈ regularValues N psi, ∑ omega ∈ regularValues N tau,
          ‖-3*gaussScale chi*phaseCoefficient N (chi*psi*tau)*
            regularAmplitude psi sigma*regularAmplitude tau omega‖*
              ((N : ℝ)^2*exceptionalScale N rho.re*regularScale N q sigma*regularScale N q omega) := by
      apply Finset.sum_le_sum
      intro psi _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro tau _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro sigma hs
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro omega ho
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (mixed_finite_one_exceptional hN (NeZero.pos q) hb.1 hb.2
          (regularValue_re_pos hs) (regularValue_re_pos ho)) (norm_nonneg _)
    _ = _ := by
      simp only [mixedCost, pairPhaseMass, regularMass, Finset.mul_sum,
        Finset.sum_mul, norm_mul, norm_neg, norm_regularAmplitude, regularScale]
      norm_num only [Complex.norm_ofNat]
      apply Finset.sum_congr rfl
      intro psi _
      apply Finset.sum_congr rfl
      intro tau _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro sigma _
      ring

theorem actual_mixed_arc_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (j : MixedKind) :
    ‖mixedArc N q j‖ ≤ mixedCost N chi rho.re j := by
  cases j
  · exact mixed_one_each_bound hN hq hr
  · exact mixed_one_exceptional_bound hN hq hr
  · exact mixed_two_exceptional_bound hN hq hr

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
