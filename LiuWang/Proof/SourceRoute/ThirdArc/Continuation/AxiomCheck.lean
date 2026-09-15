import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.Principal
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.SourceWindows
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.HeightPayments

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

example (q : ℕ) [NeZero q] (y a b : ℝ) : countIntegral q 1 y a b = 0 := by
  simp [countIntegral, betaKernel]

example (q : ℕ) [NeZero q] (X y a : ℝ) : countIntegral q X y a a = 0 := by
  simp [countIntegral]

example (z d : ℝ) : threeRowPrice 1 z d = 0 := by
  simp [threeRowPrice]

#print axioms primeCorrection
#print axioms totientConstant
#print axioms one_le_primeCorrection
#print axioms large_prime_ratio
#print axioms prime_ratio_power
#print axioms correction_product_le
#print axioms totient_ratio_product
#print axioms totient_power_bound
#print axioms totient_endpoint_certificates
#print axioms principal_totient_scale
#print axioms single_zero_totient_scale
#print axioms principalMass_paid
#print axioms principal_term_paid
#print axioms principal_bound_paid
#print axioms S_principal_and_error_paid
#print axioms one_zero_kernel_paid
#print axioms actual_simple_zero_paid
#print axioms one_zero_lowKernel_paid
#print axioms actual_simple_lowKernel_paid
#print axioms rowCutoff
#print axioms lowHeight_ge_one
#print axioms M3_modulus_large
#print axioms M3_table_domain
#print axioms low_table_domain
#print axioms M3_log_product_ge_thirty
#print axioms middle_table_domain
#print axioms high_table_domain
#print axioms M3_familyCount_row
#print axioms M3_familyCount_14000
#print axioms M3_familyCount_13
#print axioms M3_familyCount_20
#print axioms rowCutoff_ge_half
#print axioms rowCutoff_le_one
#print axioms M3_rowCutoff_ge_source_split
#print axioms densityBand_zero_eq_count
#print axioms family_beta_integrable
#print axioms countIntegral
#print axioms countIntegral_split
#print axioms countIntegral_row
#print axioms M3_countIntegral_row
#print axioms cutoff_power_exp
#print axioms M3_near_one_integral_paid
#print axioms M3_0478_integral_paid
#print axioms family_low_integrable
#print axioms M3_low_integral_row
#print axioms original_low_0478_subinterval
#print axioms finite_separated_integral
#print axioms finite_separated_swap
#print axioms rectangleZeros
#print axioms zeroValues_rectangle_filter
#print axioms familyCount_rectangle
#print axioms familyCount_separated
#print axioms familyCount_integral_swap
#print axioms countIntegral_height_swap
#print axioms familyCount_inner_integrable
#print axioms densityBand_integral_le_counts
#print axioms threeRowPrice
#print axioms M3_three_row_integral_paid
#print axioms M3_countIntegral_split_paid
#print axioms M3_low_three_row_integral_paid
#print axioms original_middle_base_ge_one
#print axioms original_middle_endpoint_split_paid
#print axioms original_high_endpoint_split_paid
#print axioms exp_div_substitution
#print axioms heightKernel_exp_jacobian
#print axioms height_log_substitution
#print axioms countIntegral_log_substitution
#print axioms moving_countIntegral_log_substitution
#print axioms original_middle_count_reduction
#print axioms original_high_count_reduction
#print axioms original_low_table_bill
#print axioms original_middle_endpoint_table_bill
#print axioms original_high_endpoint_table_bill
#print axioms original_middle_height_table_bill
#print axioms original_high_height_table_bill
#print axioms countIntegral_nonneg
#print axioms countIntegral_mono_upper
#print axioms countIntegral_mono_height
#print axioms M3_moving_remainder_monotone
#print axioms heightKernel_mul_integrable
#print axioms M3_threeRowPrice_continuousOn
#print axioms M3_height_integral_split_paid
#print axioms M3_height_near_integral_paid
#print axioms threeRowPrice_log_substitution

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
