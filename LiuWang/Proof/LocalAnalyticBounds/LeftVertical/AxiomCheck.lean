import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Consumer
import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.LowConsumer

/-! # 左垂直边新增成员的完整类型与标准公理审计 -/

set_option autoImplicit false
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option format.width 120

open LiuWang.Proof.LocalAnalyticBounds.LeftVertical

#check @norm_digamma_le_log_add_fourteen
#print axioms norm_digamma_le_log_add_fourteen
#check @norm_logDeriv_gammaFactor_left_le
#print axioms norm_logDeriv_gammaFactor_left_le
#check @norm_logDeriv_gammaFactor_three_halves_le
#print axioms norm_logDeriv_gammaFactor_three_halves_le
#check @norm_neg_logDeriv_zeta_three_halves_le_twenty
#print axioms norm_neg_logDeriv_zeta_three_halves_le_twenty
#check @norm_logDeriv_LFunction_three_halves_le_twenty
#print axioms norm_logDeriv_LFunction_three_halves_le_twenty
#check @norm_logDeriv_LFunction_left_le
#print axioms norm_logDeriv_LFunction_left_le
#check @rpow_neg_half_le_inv
#print axioms rpow_neg_half_le_inv
#check @norm_real_centered_kernel_left_le
#print axioms norm_real_centered_kernel_left_le
#check @norm_horizontalIntegrand_left_le
#print axioms norm_horizontalIntegrand_left_le
#check @continuous_left_integrand
#print axioms continuous_left_integrand
#check @intervalIntegrable_left_integrand
#print axioms intervalIntegrable_left_integrand
#check @continuous_one_div_abs_add_one
#print axioms continuous_one_div_abs_add_one
#check @integral_one_div_abs_add_one
#print axioms integral_one_div_abs_add_one
#check @norm_left_integral_le_explicit
#print axioms norm_left_integral_le_explicit
#check @source_height_log_ge_ninety
#print axioms source_height_log_ge_ninety
#check @normalized_explicit_bound_le_source
#print axioms normalized_explicit_bound_le_source
#check @pow_eighteen_le_exp
#print axioms pow_eighteen_le_exp
#check @million_sourceT_le_endpoint
#print axioms million_sourceT_le_endpoint
#check @source_left_cost_le_small_budget
#print axioms source_left_cost_le_small_budget
#check @norm_left_integral_source_sharp_le
#print axioms norm_left_integral_source_sharp_le
#check @norm_left_integral_source_small_le
#print axioms norm_left_integral_source_small_le
#check @actual_left_vertical_estimate
#print axioms actual_left_vertical_estimate
#check @Consumer.actual_source_left_vertical_budget
#print axioms Consumer.actual_source_left_vertical_budget
#check @real_centered_kernel_eq_integral
#print axioms real_centered_kernel_eq_integral
#check @norm_real_centered_kernel_low_re_le
#print axioms norm_real_centered_kernel_low_re_le
#check @lowZeroWindow
#print axioms lowZeroWindow
#check @inv_height_sq_add_four_le_reference_kernel
#print axioms inv_height_sq_add_four_le_reference_kernel
#check @finite_lowZeroWindow
#print axioms finite_lowZeroWindow
#check @lowZeroFinset
#print axioms lowZeroFinset
#check @mem_lowZeroFinset
#print axioms mem_lowZeroFinset
#check @card_lowZeroFinset_le
#print axioms card_lowZeroFinset_le
#check @norm_lowZero_centered_sum_le
#print axioms norm_lowZero_centered_sum_le
#check @pow_ninety_six_le_exp
#print axioms pow_ninety_six_le_exp
#check @source_sqrt_endpoint_ge_large_power
#print axioms source_sqrt_endpoint_ge_large_power
#check @lowZero_explicit_cost_le_small_budget
#print axioms lowZero_explicit_cost_le_small_budget
#check @norm_lowZero_centered_sum_source_le
#print axioms norm_lowZero_centered_sum_source_le
#check @Consumer.actual_source_low_zero_budget
#print axioms Consumer.actual_source_low_zero_budget
