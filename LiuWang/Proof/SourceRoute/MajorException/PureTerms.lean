import LiuWang.Proof.SourceRoute.MajorException.MixedRealMoment
import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.ConductorSum

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation
open LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier

namespace LiuWang.Proof.SourceRoute.MajorException

def moebiusWeight (q : ℕ) : ℝ := |(ArithmeticFunction.moebius q : ℝ)|

theorem moebiusWeight_nonneg (q : ℕ) : 0 ≤ moebiusWeight q := abs_nonneg _

theorem source_coefficient_norms {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    ‖linearCoefficient N chi‖ ≤
        3*moebiusWeight q*Real.sqrt chi.conductor/(q.totient : ℝ)^2 ∧
      ‖quadraticCoefficient N chi‖ ≤
        3*moebiusWeight q*(chi.conductor : ℝ)/(q.totient : ℝ)^2 := by
  by_cases hm : ArithmeticFunction.moebius q = 0
  · simp [linearCoefficient, quadraticCoefficient, principalCoefficient, moebiusWeight, hm]
  · have habs : moebiusWeight q = 1 := by
      rcases ArithmeticFunction.moebius_eq_or q with h | h | h
      · exact (hm h).elim
      · norm_num [moebiusWeight, h]
      · norm_num [moebiusWeight, h]
    simpa only [habs, mul_one] using
      And.intro (coefficient_norms_conductor N chi).1 (coefficient_norms_conductor N chi).2.1

def linearTerm {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) (beta : ℝ) : ℂ :=
  linearCoefficient N chi * finiteMoment N (deltaRadius N q) 1 1 beta

def quadraticTerm {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) (beta : ℝ) : ℂ :=
  quadraticCoefficient N chi * finiteMoment N (deltaRadius N q) 1 beta beta

def cubicTerm {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) (beta : ℝ) : ℂ :=
  cubicCoefficient N chi * finiteMoment N (deltaRadius N q) beta beta beta

theorem linearTerm_source_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) :
    ‖linearTerm N chi beta‖ ≤ 2.8959*(N : ℝ)^2*baseWeight N beta *
      (moebiusWeight q*Real.sqrt chi.conductor/(q.totient : ℝ)^2) := by
  rw [linearTerm, norm_mul]
  have h := mul_le_mul (source_coefficient_norms N chi).1
    (finite_linear_source (nat_pos_of_exp_le hN) hb hb1
      (deltaRadius_pos hN (NeZero.pos q)).le) (norm_nonneg _)
    (by unfold moebiusWeight; positivity)
  exact h.trans_eq (by ring)

theorem quadraticTerm_source_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) :
    ‖quadraticTerm N chi beta‖ ≤
      (3*quadraticHolderConstant)*(N : ℝ)^2*baseWeight N beta^2 *
        (moebiusWeight q*(chi.conductor : ℝ)/(q.totient : ℝ)^2) := by
  rw [quadraticTerm, norm_mul]
  have h := mul_le_mul (source_coefficient_norms N chi).2
    (finite_quadratic_source (nat_pos_of_exp_le hN) hb hb1
      (deltaRadius_pos hN (NeZero.pos q)).le) (norm_nonneg _)
    (by unfold moebiusWeight; positivity)
  exact h.trans_eq (by ring)

theorem cubicTerm_source_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) :
    ‖cubicTerm N chi beta‖ ≤
      (3*1.0302*1.0033^2/Real.pi)*(N : ℝ)^2*baseWeight N beta^3 *
        ((chi.conductor : ℝ)*Real.sqrt chi.conductor/(q.totient : ℝ)^2) := by
  rw [cubicTerm, norm_mul]
  have h := mul_le_mul (coefficient_norms_conductor N chi).2.2
    (finite_cubic_source (nat_pos_of_exp_le hN) hb hb1
      (deltaRadius_pos hN (NeZero.pos q)).le) (norm_nonneg _) (by positivity)
  exact h.trans_eq (by ring)

theorem source_quadratic_summed_constant :
    (3*quadraticHolderConstant)*2.82682 ≤ 8.2914 := by
  convert source_quadratic_holder_constant using 1
  unfold quadraticHolderConstant
  ring

theorem source_cubic_summed_constant :
    (3*1.0302*1.0033^2/Real.pi)*(3.39102 : ℝ) ≤ 3.35804 := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_d6]

theorem exceptional_beta_source_range {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ exceptionalValues N chi) :
    0.9957 ≤ rho.re ∧ rho.re ≤ 1 := by
  have hreg := (Finset.mem_filter.mp hr).2
  have hz := mem_zeroValues.mp (Finset.mem_filter.mp hr).1
  have hlog := sourceP_log_ge_twenty hN
  have hdiv : 1/(24*Real.log (sourceP N)) ≤ (1/480 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 24*Real.log (sourceP N))).mpr
    linarith
  exact ⟨by linarith [hreg.1], hz.2.2.1.le⟩

theorem exceptionalArc_eq_source_terms {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    exceptionalArc N q =
      linearTerm N chi rho.re + quadraticTerm N chi rho.re + cubicTerm N chi rho.re := by
  rw [exceptionalArc_eq_joint hN hq hr]
  simp only [jointFinite, zero_mul, zero_add, linearTerm, quadraticTerm, cubicTerm]

theorem actual_pure_terms_source_bounds {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ exceptionalValues N chi) :
    ‖linearTerm N chi rho.re‖ ≤ 2.8959*(N : ℝ)^2*baseWeight N rho.re *
        (moebiusWeight q*Real.sqrt chi.conductor/(q.totient : ℝ)^2) ∧
      ‖quadraticTerm N chi rho.re‖ ≤
        (3*quadraticHolderConstant)*(N : ℝ)^2*baseWeight N rho.re^2 *
          (moebiusWeight q*(chi.conductor : ℝ)/(q.totient : ℝ)^2) ∧
      ‖cubicTerm N chi rho.re‖ ≤
        (3*1.0302*1.0033^2/Real.pi)*(N : ℝ)^2*baseWeight N rho.re^3 *
          ((chi.conductor : ℝ)*Real.sqrt chi.conductor/(q.totient : ℝ)^2) := by
  have hb := exceptional_beta_source_range hN hr
  exact ⟨linearTerm_source_bound hN chi hb.1 hb.2,
    quadraticTerm_source_bound hN chi hb.1 hb.2, cubicTerm_source_bound hN chi hb.1 hb.2⟩

end LiuWang.Proof.SourceRoute.MajorException
