import LiuWang.Proof.OscillatoryBounds.EndpointChecks

/-! # 全部公开声明的完整类型、原定义值与传递公理审计 -/

open LiuWang.Proof.OscillatoryBounds

#print AnalyticNumberTheory.LargeSieve.charReal
#print LiuWang.Proof.Interfaces.sourceWindowLower
#print LiuWang.Proof.Interfaces.J
#print LiuWang.Proof.Interfaces.Jrho

#check @continuous_charReal_mul
#check @intervalIntegrable_charReal
#check @norm_integral_charReal_le_length
#check @charReal_mul_eq_exp
#check @norm_frequency
#check @integral_charReal_eq
#check @norm_integral_charReal_le_reciprocal
#check @continuousOn_cpow_charReal
#check @intervalIntegrable_cpow_charReal
#check @norm_cpow_charReal
#check @norm_integral_cpow_charReal_le_weight
#check @norm_integral_cpow_charReal_le_source_weight
#check @norm_integral_weight_mul_le
#check @hasDerivAt_charReal_mul
#check @norm_integral_rpow_charReal_le
#check @norm_integral_real_cpow_charReal_le
#check @near_denominator_lower
#check @hasDerivAt_near_primitive
#check @norm_integral_cpow_charReal_near
#check @far_denominator_lower
#check @hasDerivAt_far_primitive
#check @norm_integral_cpow_charReal_far_general
#check @norm_integral_cpow_charReal_far
#check @norm_phase_denominator
#check @reciprocal_phase_variation
#check @norm_integral_cpow_charReal_first_derivative
#check @small_phase_diameter
#check @norm_integral_cpow_charReal_first_derivative_open
#check @norm_integral_cpow_charReal_sqrt_general
#check @norm_integral_cpow_charReal_sqrt
#check @J_intervalIntegrable
#check @Jrho_intervalIntegrable
#check @J_length
#check @J_reciprocal
#check @J_bound
#check @Jrho_weight
#check @Jrho_real_reciprocal
#check @Jrho_real_bound
#check @Jrho_real_bound_sourceDomain
#check @Jrho_near
#check @Jrho_sqrt
#check @Jrho_transition
#check @Jrho_far
#check @Jrho_intervalIntegrable_sourceDomain
#check @Jrho_near_sourceDomain
#check @Jrho_transition_sourceDomain
#check @Jrho_far_sourceDomain
#check @J_zero_value
#check @source_thresholds_order
#check @Jrho_lower_boundary
#check @Jrho_upper_boundary

#print axioms continuous_charReal_mul
#print axioms intervalIntegrable_charReal
#print axioms norm_integral_charReal_le_length
#print axioms charReal_mul_eq_exp
#print axioms norm_frequency
#print axioms integral_charReal_eq
#print axioms norm_integral_charReal_le_reciprocal
#print axioms continuousOn_cpow_charReal
#print axioms intervalIntegrable_cpow_charReal
#print axioms norm_cpow_charReal
#print axioms norm_integral_cpow_charReal_le_weight
#print axioms norm_integral_cpow_charReal_le_source_weight
#print axioms norm_integral_weight_mul_le
#print axioms hasDerivAt_charReal_mul
#print axioms norm_integral_rpow_charReal_le
#print axioms norm_integral_real_cpow_charReal_le
#print axioms near_denominator_lower
#print axioms hasDerivAt_near_primitive
#print axioms norm_integral_cpow_charReal_near
#print axioms far_denominator_lower
#print axioms hasDerivAt_far_primitive
#print axioms norm_integral_cpow_charReal_far_general
#print axioms norm_integral_cpow_charReal_far
#print axioms norm_phase_denominator
#print axioms reciprocal_phase_variation
#print axioms norm_integral_cpow_charReal_first_derivative
#print axioms small_phase_diameter
#print axioms norm_integral_cpow_charReal_first_derivative_open
#print axioms norm_integral_cpow_charReal_sqrt_general
#print axioms norm_integral_cpow_charReal_sqrt
#print axioms J_intervalIntegrable
#print axioms Jrho_intervalIntegrable
#print axioms J_length
#print axioms J_reciprocal
#print axioms J_bound
#print axioms Jrho_weight
#print axioms Jrho_real_reciprocal
#print axioms Jrho_real_bound
#print axioms Jrho_real_bound_sourceDomain
#print axioms Jrho_near
#print axioms Jrho_sqrt
#print axioms Jrho_transition
#print axioms Jrho_far
#print axioms Jrho_intervalIntegrable_sourceDomain
#print axioms Jrho_near_sourceDomain
#print axioms Jrho_transition_sourceDomain
#print axioms Jrho_far_sourceDomain
#print axioms J_zero_value
#print axioms source_thresholds_order
#print axioms Jrho_lower_boundary
#print axioms Jrho_upper_boundary
