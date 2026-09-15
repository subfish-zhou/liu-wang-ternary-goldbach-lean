import LiuWang.Proof.Campaign20260915.ZetaJnCentral.LocalHankelConsumer

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

example (sigma : ℝ) {eta : ℝ} (he : 0 < eta) :
    IntervalIntegrable (rsJnIntegrand sigma eta ⌊eta⌋₊ 1) volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ 1 y‖ ≤
      firstOrderJnConstant sigma / eta :=
  ⟨jn_local_integrable sigma he (Nat.zero_le_self_sub_floor he.le)
      (Nat.self_sub_floor_lt_one eta).le 0,
    jn_one_source_order sigma he (Nat.zero_le_self_sub_floor he.le)
      (Nat.self_sub_floor_lt_one eta).le⟩

example {eta : ℝ} (he : 0 < eta) :
    IntervalIntegrable (rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7) volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y‖ ≤
      localJnBudget (1 / 2) eta (21 / 40 * (rsSaddleScale * eta)) (eta / 2) 6 := by
  have hp := local_budget_parameters he
  exact jn_floor_local_budget (1 / 2) he hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 le_rfl 6

#print axioms jn_middle_pointwise
#print axioms jn_middle_half
#print axioms jn_middle_integrals
#print axioms positive_div_one_sub_exp_neg
#print axioms jn_zero
#print axioms gaussian_times_distance
#print axioms centralTaylorConstant_nonneg
#print axioms jn_central_pointwise
#print axioms jn_central_integral
#print axioms jn_measurable
#print axioms jn_central_integrable
#print axioms jn_local_integrable
#print axioms jn_local_split
#print axioms jn_local_budget
#print axioms jn_floor_local_budget
#print axioms local_budget_parameters
#print axioms saddle_exponent_norm
#print axioms firstOrderPolynomial_nonneg
#print axioms descent_exponent_norm
#print axioms descent_exponent_envelope
#print axioms firstOrder_remainder
#print axioms jn_one_pointwise
#print axioms power_gaussian_third
#print axioms firstOrderGaussianConstant_nonneg
#print axioms firstOrderPolynomial_gaussian
#print axioms gaussian_interval_le_full
#print axioms jn_one_source_order
#print axioms local_hankel_taylor_error
#print axioms local_hankel_one_error
#print axioms local_hankel_seven_error

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
