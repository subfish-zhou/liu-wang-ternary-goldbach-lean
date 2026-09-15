import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorLocalHankel

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

#print axioms exterior_denominator_pos
#print axioms exterior_denominator_half
#print axioms exterior_gaussian_bound
#print axioms exterior_gaussian_bound_half
#print axioms exterior_polynomial_measurable
#print axioms exterior_polynomial_norm
#print axioms exterior_power_gaussian
#print axioms exterior_polynomial_bound
#print axioms exterior_gaussian_Ioi
#print axioms exterior_gaussian_complement
#print axioms exterior_mem_abs
#print axioms exterior_integrable_of_gaussian
#print axioms exterior_norm_integral_bound
#print axioms exterior_integral_bound
#print axioms exterior_polynomial_integrable
#print axioms exterior_polynomial_general_budget
#print axioms exterior_div_pow_norm
#print axioms exterior_coefficient_bound
#print axioms exterior_coefficient_sum
#print axioms exterior_one_norm_budget
#print axioms exterior_seven_norm_budget
#print axioms exterior_one_budget
#print axioms exterior_seven_budget
#print axioms exterior_exp_large
#print axioms exterior_large_scalar
#print axioms exterior_seven_large
#print axioms exterior_one_le_seven_scalar
#print axioms exterior_one_large
#print axioms exterior_eta_original_height
#print axioms exterior_floor_one
#print axioms exterior_floor_seven
#print axioms exterior_R0_height
#print axioms exterior_R2_height
#print axioms exterior_localPrefactor_norm
#print axioms exterior_localHankel_difference
#print axioms exterior_localHankel_budget
#print axioms exterior_localHankel_one
#print axioms exterior_localHankel_seven
#print axioms exterior_localHankel_seven_large

example :
    (∫ y : ℝ in (Ioc (-5 : ℝ) 5)ᶜ, ‖rsLocalPolynomialIntegrand (1 / 2) 10 10 7 y‖) ≤
      1 / 100000 := by
  have h := exterior_seven_large (eta := 10) (m := 10) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example (sigma : ℝ) (N : ℕ) :
    IntegrableOn (rsLocalPolynomialIntegrand sigma 1 1 N) (Ioc (-1 / 2) (1 / 2))ᶜ := by
  exact exterior_polynomial_integrable sigma (by norm_num) (by norm_num) (by norm_num) N

example {t : ℝ} (ht : 16 < t) :
    (∫ y : ℝ in (Ioc (-Real.sqrt (t / (2 * Real.pi)) / 2)
      (Real.sqrt (t / (2 * Real.pi)) / 2))ᶜ,
        ‖rsLocalPolynomialIntegrand (1 / 2) (Real.sqrt (t / (2 * Real.pi)))
          ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ 7 y‖) ≤
      120000 / Real.sqrt (t / (2 * Real.pi)) *
        Real.exp (-Real.pi * Real.sqrt (t / (2 * Real.pi)) ^ 2 / 8) :=
  exterior_floor_seven (exterior_eta_original_height ht)

end LiuWang.Proof.Campaign20260915.ZetaMordell
