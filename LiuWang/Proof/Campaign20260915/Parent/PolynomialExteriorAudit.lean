import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorAudit

/-! Parent consumption of the actual polynomial exterior budget.
Integer eta is allowed for this exterior integral, not for the unmodified central contour.
The Jn integral and full zeta remainder remain unpaid.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Parent.PolynomialExteriorAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem actual_polynomial_exterior {eta : ℝ} (he : 10 ≤ eta) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ,
      ‖rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y‖) ≤
      1 / (10 * eta ^ 4) :=
  exterior_seven_large he (Nat.zero_le_self_sub_floor (by linarith))
    (Nat.self_sub_floor_lt_one eta).le

#print axioms actual_polynomial_exterior
end LiuWang.Proof.Campaign20260915.Parent.PolynomialExteriorAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_R0_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_R2_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_coefficient_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_coefficient_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_denominator_half
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_denominator_pos
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_div_pow_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_eta_original_height
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_exp_large
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_floor_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_floor_seven
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_gaussian_Ioi
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_gaussian_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_gaussian_bound_half
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_gaussian_complement
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_integrable_of_gaussian
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_integral_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_large_scalar
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_localHankel_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_localHankel_difference
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_localHankel_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_localHankel_seven
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_localHankel_seven_large
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_localPrefactor_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_mem_abs
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_norm_integral_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_one_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_one_large
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_one_le_seven_scalar
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_one_norm_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_polynomial_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_polynomial_general_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_polynomial_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_polynomial_measurable
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_polynomial_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_power_gaussian
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_seven_budget
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_seven_large
#print axioms LiuWang.Proof.Campaign20260915.ZetaMordell.exterior_seven_norm_budget
